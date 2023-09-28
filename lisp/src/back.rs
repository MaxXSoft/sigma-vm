use crate::anf::*;
use sigma_vm::bytecode::builder::Builder;
use sigma_vm::bytecode::consts::ObjectRef;
use sigma_vm::bytecode::insts::Inst;
use sigma_vm::bytecode::module::StaticModule;
use std::mem;

/// Sigma VM module generator.
pub struct Generator {
  state: State,
  requires: Vec<Require>,
  main_body: Vec<Statement>,
}

impl Generator {
  /// Creates a new generator.
  pub fn new() -> Self {
    Self {
      state: State::new(),
      requires: Vec::new(),
      main_body: Vec::new(),
    }
  }

  /// Generates on the given statement.
  pub fn generate_on(&mut self, stmt: Statement) {
    match stmt {
      Statement::Define(d) if d.exportable => d.generate(&mut self.state),
      Statement::Provide(p) => p.generate(&mut self.state),
      Statement::Require(r) => self.requires.push(r),
      stmt => self.main_body.push(stmt),
    }
  }

  /// Consumes the current builder and generates a static module.
  pub fn generate(mut self) -> StaticModule {
    self.state.gen_requires(self.requires);
    if !self.main_body.is_empty() {
      self.state.gen_main(self.main_body);
    }
    self.state.gen_funcs();
    self.state.builder.build().unwrap()
  }
}

/// State of a generator.
struct State {
  builder: Builder,
  obj_value: u64,
  obj_ptr: u64,
  invoke: u64,
  panic: u64,
  check_nargs: u64,
  funcs: Vec<(Option<u64>, Lambda)>,
}

impl State {
  /// Handle of the current module.
  const MOD_HANDLE: u64 = 0;

  /// Handle of the builtin module.
  const BUILTIN_HANDLE: u64 = 1;

  /// Number of preserved global variables.
  const NUM_PRESERVED_GLOBALS: u64 = 2;

  fn new() -> Self {
    let mut builder = Builder::new();
    // generate object metadata
    let obj_value = builder.constant(ObjectRef {
      size: 24,
      align: 8,
      destructor: 0,
      offsets: &[2], // kind, value, next
    });
    let obj_ptr = builder.constant(ObjectRef {
      size: 24,
      align: 8,
      destructor: 0,
      offsets: &[1, 2], // kind, pointer, next
    });
    let invoke = builder.constant("invoke");
    let panic = builder.constant("panic");
    let check_nargs = builder.constant("check_nargs");
    // create state
    let mut state = Self {
      builder,
      obj_value,
      obj_ptr,
      invoke,
      panic,
      check_nargs,
      funcs: Vec::new(),
    };
    // generate instructions for the module initializer
    state.gen_init_builtin();
    state
  }

  /// Generates requires (imports) and finish the
  /// module initializer generation.
  fn gen_requires(&mut self, requires: Vec<Require>) {
    for r in requires {
      r.generate(self);
    }
    // generate a `ret` instruction for the module initializer
    self.builder.inst(Inst::Ret);
  }

  /// Generates the `main` function.
  fn gen_main(&mut self, stmts: Vec<Statement>) {
    let main = self.builder.label();
    self.builder.insert_label(main);
    // clear all arguments
    self.builder.inst(Inst::Sys(11));
    // generate main body
    for stmt in stmts {
      stmt.generate(self);
    }
    // generate return
    self.builder.inst(Inst::PushU(0));
    self.builder.inst(Inst::Ret);
    // export `main` function
    self.builder.export("main".into(), main, None, 1);
  }

  /// Generates other functions.
  fn gen_funcs(&mut self) {
    while !self.funcs.is_empty() {
      let funcs = mem::take(&mut self.funcs);
      for (label, f) in funcs {
        if let Some(l) = label {
          self.builder.insert_label(l);
        }
        f.generate(self);
      }
    }
  }

  /// Generates instructions to load builtin module and store the handler.
  fn gen_init_builtin(&mut self) {
    // store the handle of the current module to globbal variable
    self.builder.inst(Inst::StG(Self::MOD_HANDLE));
    // load builtin module
    let builtins = self.builder.constant("builtins.sbc");
    self.builder.inst(Inst::LoadC(builtins));
    // check if failed
    self.builder.inst(Inst::Dup);
    let end_check = self.builder.label();
    self.builder.cfi(Inst::Bnz, end_check);
    // print error message and panic
    self.gen_panic("failed to load builtin module");
    // store the builtin module handle to globbal variable
    self.builder.insert_label(end_check);
    self.builder.inst(Inst::StG(Self::BUILTIN_HANDLE));
  }

  /// Generates a panic.
  fn gen_panic(&mut self, msg: &str) {
    let error_msg = self.builder.constant(format!("FATAL: {msg}\n"));
    self.builder.inst(Inst::LaC(error_msg));
    self.builder.inst(Inst::Dup);
    self.builder.inst(Inst::PushU(8));
    self.builder.inst(Inst::Add);
    self.builder.inst(Inst::Swap);
    self.builder.inst(Inst::LdDO(0));
    self.builder.inst(Inst::Sys(10));
    self.builder.inst(Inst::Sys(13));
  }

  /// Generates a builtin panic.
  fn gen_builtin_panic(&mut self, msg: &str) {
    let error_msg = self.builder.constant(format!("{msg}\n"));
    self.builder.inst(Inst::LaC(error_msg));
    self.builder.inst(Inst::LdG(Self::BUILTIN_HANDLE));
    self.builder.inst(Inst::CallExtC(self.panic));
  }

  /// Returns the actual global variable number of the given variable.
  fn global(var: u64) -> u64 {
    Self::NUM_PRESERVED_GLOBALS + var
  }

  // /// Generates a quote.
  // fn quote(&mut self, elem: Element) {
  //   match elem.kind {
  //     ElemKind::Num(num) => self.num(num),
  //     ElemKind::Str(s) => self.str(&s),
  //     ElemKind::Sym(s) => self.sym(&s),
  //     ElemKind::Quote(e) => {
  //       self.list(vec![
  //         Element {
  //           kind: ElemKind::Str("quote".into()),
  //           span: elem.span,
  //         },
  //         *e,
  //       ]);
  //     }
  //     ElemKind::List(elems) => self.list(elems),
  //   }
  // }

  /// Generates a new number value.
  fn num(&mut self, num: f64) {
    self.atom(self.obj_value, AtomKind::Num);
    self.builder.inst(Inst::Dup);
    self.builder.push_f64(num);
    self.builder.inst(Inst::StDO(1));
  }

  /// Generates a new string value.
  fn str(&mut self, s: &str) {
    self.atom(self.obj_ptr, AtomKind::Str);
    self.builder.inst(Inst::Dup);
    self.push_str(s);
    self.builder.inst(Inst::StDO(1));
  }

  /// Generates a new symbol value.
  fn sym(&mut self, s: &str) {
    self.atom(self.obj_ptr, AtomKind::Sym);
    self.builder.inst(Inst::Dup);
    self.push_str(s);
    self.builder.inst(Inst::StDO(1));
  }

  /// Generates a new string, pushes its pointer to the stack.
  fn push_str(&mut self, s: &str) {
    let s = self.builder.constant(s);
    self.builder.inst(Inst::LaC(s));
  }

  // /// Generates a new list.
  // fn list(&mut self, elems: Vec<Element>) {
  //   self.atom(self.obj_ptr, AtomKind::List);
  //   self.builder.inst(Inst::Dup);
  //   self.chain(elems.into_iter());
  //   self.builder.inst(Inst::StDO(1));
  // }

  // /// Chains the given elements into a linked list.
  // fn chain<I>(&mut self, mut elems: I)
  // where
  //   I: Iterator<Item = Element>,
  // {
  //   if let Some(elem) = elems.next() {
  //     self.quote(elem);
  //     self.builder.inst(Inst::Dup);
  //     self.chain(elems);
  //     self.builder.inst(Inst::StDO(2));
  //   } else {
  //     self.builder.inst(Inst::PushU(0));
  //   }
  // }

  /// Generates a new atom, leaves the 2nd field uninitialized.
  fn atom(&mut self, obj: u64, kind: AtomKind) {
    self.builder.inst(Inst::NewOC(obj));
    self.builder.inst(Inst::Dup);
    self.builder.inst(Inst::PushU(kind as u64));
    self.builder.inst(Inst::StDO(0));
    self.builder.inst(Inst::Dup);
    self.builder.inst(Inst::PushU(0));
    self.builder.inst(Inst::StDO(2));
  }
}

/// Kind of atom.
///
/// # Notes
///
/// This must be synchronized with implementations in `builtins.sbas`.
enum AtomKind {
  /// Number.
  Num,
  /// String.
  Str,
  /// Symbol.
  Sym,
  /// List.
  List,
  /// Builtin function.
  Builtin,
  /// Lambda.
  Lambda,
}

/// Trait for generating statements.
trait Generate {
  /// Generates the given statement.
  fn generate(self, state: &mut State);
}

impl Generate for Statement {
  fn generate(self, state: &mut State) {
    match self {
      Self::Define(d) => d.generate(state),
      Self::Expr(e) => e.generate(state),
      Self::Require(r) => r.generate(state),
      Self::Provide(p) => p.generate(state),
    }
  }
}

impl Generate for Define {
  fn generate(self, state: &mut State) {
    // generate the expression
    self.expr.generate(state);
    // store to global variable
    state.builder.inst(Inst::StG(State::global(self.var)));
  }
}

impl Generate for Expr {
  fn generate(self, state: &mut State) {
    match self {
      Self::Value(v) => v.generate(state),
      Self::CompExpr(c) => c.generate(state),
      Self::Let(l) => l.generate(state),
    }
  }
}

impl Generate for Require {
  fn generate(self, state: &mut State) {
    // load module
    let path = state.builder.constant(format!("{}.sbc", self.path));
    state.builder.inst(Inst::LoadC(path));
    // check if failed
    state.builder.inst(Inst::Dup);
    let end_check = state.builder.label();
    state.builder.cfi(Inst::Bnz, end_check);
    // print error message and panic
    state.gen_builtin_panic(&format!("failed to load module `{}`", self.path));
    // get symbols from module
    state.builder.insert_label(end_check);
    let nsyms = self.sym_vars.len();
    for (i, (sym, var)) in self.sym_vars.into_iter().enumerate() {
      if i + 1 != nsyms {
        state.builder.inst(Inst::Dup);
      }
      // call the symbol
      let sym = state.builder.constant(sym);
      state.builder.inst(Inst::CallExtC(sym));
      // store to global variable
      state.builder.inst(Inst::StG(State::global(var)));
    }
  }
}

impl Generate for Provide {
  fn generate(self, state: &mut State) {
    for (sym, var) in self.sym_vars {
      // generate a function for the current provide
      let func = Lambda {
        params: vec![],
        captures: vec![],
        expr: Box::new(Expr::Value(Value::GlobalVar(var))),
      };
      // add to function list
      let label = state.builder.label();
      state.funcs.push((Some(label), func));
      // export the generated function
      state.builder.export(sym, label, Some(0), 1);
    }
  }
}

impl Generate for Value {
  fn generate(self, state: &mut State) {
    match self {
      Self::Num(n) => todo!(),
      Self::Str(s) => todo!(),
      Self::Sym(s) => todo!(),
      Self::List(l) => todo!(),
      Self::Var(v) => todo!(),
      Self::GlobalVar(g) => todo!(),
      Self::Builtin(b) => todo!(),
      Self::Lambda(l) => l.generate(state),
    }
  }
}

impl Generate for CompExpr {
  fn generate(self, state: &mut State) {
    match self {
      Self::Apply(a) => a.generate(state),
      Self::If(i) => i.generate(state),
    }
  }
}

impl Generate for Let {
  fn generate(self, state: &mut State) {
    todo!()
  }
}

impl Generate for Lambda {
  fn generate(self, state: &mut State) {
    todo!()
  }
}

impl Generate for Apply {
  fn generate(self, state: &mut State) {
    todo!()
  }
}

impl Generate for If {
  fn generate(self, state: &mut State) {
    todo!()
  }
}
