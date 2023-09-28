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
    self.state.gen_main(self.main_body);
    self.state.gen_funcs();
    self.state.builder.build().unwrap()
  }
}

/// State of a generator.
struct State {
  builder: Builder,
  obj_value: u64,
  obj_ptr: u64,
  funcs: Vec<Lambda>,
}

impl State {
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
    // generate a `pop` instruction for the module initializer
    builder.inst(Inst::Pop);
    Self {
      builder,
      obj_value,
      obj_ptr,
      funcs: Vec::new(),
    }
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
      for f in funcs {
        f.generate(self);
      }
    }
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
enum AtomKind {
  /// Number.
  Num,
  /// String.
  Str,
  /// Symbol.
  Sym,
  /// List.
  List,
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
    todo!()
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
    todo!()
  }
}

impl Generate for Provide {
  fn generate(self, state: &mut State) {
    todo!()
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
