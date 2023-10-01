use crate::anf::*;
use sigma_vm::bytecode::builder::Builder;
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
  funcs: Vec<Func>,
}

impl State {
  /// Handle of the current module.
  const MOD_HANDLE: u64 = 0;

  /// Handle of the builtin module.
  const BUILTIN_HANDLE: u64 = 1;

  /// Number of preserved global variables.
  const NUM_PRESERVED_GLOBALS: u64 = 2;

  fn new() -> Self {
    // create state
    let mut state = Self {
      builder: Builder::new(),
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
    let loop_start = self.builder.label();
    let loop_end = self.builder.label();
    self.builder.cfi(Inst::BzNP, loop_end);
    self.builder.insert_label(loop_start);
    self.builder.inst(Inst::Swap);
    self.builder.inst(Inst::Pop);
    self.builder.cfi(Inst::Loop, loop_start);
    self.builder.insert_label(loop_end);
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
      for func in funcs {
        func.generate(self);
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
    self.builder.inst(Inst::Sys(12));
  }

  /// Generates a builtin panic.
  fn gen_builtin_panic(&mut self, msg: &str) {
    let error_msg = self.builder.constant(format!("{msg}\n"));
    self.builder.inst(Inst::LaC(error_msg));
    self.builder.inst(Inst::LdG(Self::BUILTIN_HANDLE));
    let panic = self.builder.constant("panic");
    self.builder.inst(Inst::CallExtC(panic));
  }

  /// Generates a call to the given builtin function.
  fn gen_builtin_call(&mut self, name: &str) {
    let name = self.builder.constant(name);
    self.builder.inst(Inst::LdG(Self::BUILTIN_HANDLE));
    self.builder.inst(Inst::CallExtC(name));
  }

  /// Returns the actual global variable number of the given variable.
  fn global(var: u64) -> u64 {
    Self::NUM_PRESERVED_GLOBALS + var
  }
}

/// Static function, converted from a [`Lambda`].
struct Func {
  label: u64,
  params: Vec<u64>,
  captures_rev: Vec<u64>,
  expr: Box<Expr>,
}

/// Trait for generating statements.
trait Generate {
  /// Generates on the current ANF.
  fn generate(self, state: &mut State);
}

impl Generate for Statement {
  fn generate(self, state: &mut State) {
    match self {
      Self::Define(d) => d.generate(state),
      Self::Expr(e) => {
        e.generate(state);
        // drop the value
        state.builder.inst(Inst::Pop)
      }
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
      let label = state.builder.label();
      let func = Func {
        label,
        params: vec![],
        captures_rev: vec![],
        expr: Box::new(Expr::Value(Value::GlobalVar(var))),
      };
      // add to function list
      state.funcs.push(func);
      // export the generated function
      state.builder.export(sym, label, Some(0), 1);
    }
  }
}

impl Generate for Value {
  fn generate(self, state: &mut State) {
    match self {
      Self::Num(n) => {
        state.builder.push_f64(n);
        state.gen_builtin_call("new_num")
      }
      Self::Str(s) => {
        let s = state.builder.constant(s);
        state.builder.inst(Inst::LaC(s));
        state.gen_builtin_call("new_str")
      }
      Self::Sym(s) => {
        let s = state.builder.constant(s);
        state.builder.inst(Inst::LaC(s));
        state.gen_builtin_call("new_sym")
      }
      Self::List(l) => {
        let len = l.len() as u64;
        l.into_iter().for_each(|v| v.generate(state));
        state.builder.inst(Inst::PushU(len));
        state.gen_builtin_call("new_list")
      }
      Self::Var(v) => state.builder.inst(Inst::LdV(v)),
      Self::GlobalVar(g) => state.builder.inst(Inst::LdG(State::global(g))),
      Self::Builtin(b) => b.generate(state),
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
    self.def.generate(state);
    state.builder.inst(Inst::StV(self.var));
    self.expr.generate(state);
  }
}

impl Generate for Lambda {
  fn generate(self, state: &mut State) {
    let label = state.builder.label();
    // generate module handle and function PC
    state.builder.inst(Inst::LdG(State::MOD_HANDLE));
    state.builder.pc_imm(Inst::PushU, label);
    // generate captured variables
    let mut captures_rev = Vec::new();
    for capture in self.captures.into_iter().rev() {
      state.builder.inst(Inst::LdV(capture.captured));
      captures_rev.push(capture.id);
    }
    // generate lambda object
    let len = captures_rev.len() as u64 + 2;
    state.builder.inst(Inst::PushU(len));
    state.gen_builtin_call("new_lambda");
    // push the rest part as a function to state
    state.funcs.push(Func {
      label,
      params: self.params,
      captures_rev,
      expr: self.expr,
    });
  }
}

impl Generate for Apply {
  fn generate(self, state: &mut State) {
    let len = self.args.len() as u64;
    self.args.into_iter().for_each(|v| v.generate(state));
    self.func.generate(state);
    state.builder.inst(Inst::PushU(len + 1));
    state.gen_builtin_call("invoke");
  }
}

impl Generate for If {
  fn generate(self, state: &mut State) {
    let label_else = state.builder.label();
    let label_end = state.builder.label();
    self.cond.generate(state);
    state.gen_builtin_call("to_bool");
    state.builder.cfi(Inst::Bz, label_else);
    self.then.generate(state);
    state.builder.cfi(Inst::Jmp, label_end);
    state.builder.insert_label(label_else);
    self.else_then.generate(state);
    state.builder.insert_label(label_end);
  }
}

impl Generate for Builtin {
  fn generate(self, state: &mut State) {
    state.gen_builtin_call(match self {
      Self::Atom => "atom",
      Self::Number => "number",
      Self::Equal => "equal",
      Self::Car => "car",
      Self::Cdr => "cdr",
      Self::Cons => "cons",
      Self::List => "list",
      Self::Add => "builtin_add",
      Self::Sub => "builtin_sub",
      Self::Mul => "builtin_mul",
      Self::Div => "builtin_div",
      Self::Gt => "builtin_gt",
      Self::Lt => "builtin_lt",
      Self::Ge => "builtin_ge",
      Self::Le => "builtin_le",
      Self::Eq => "builtin_eq",
      Self::Print => "builtin_print",
    })
  }
}

impl Generate for Func {
  fn generate(self, state: &mut State) {
    // insert label
    state.builder.insert_label(self.label);
    // check argument number
    let nargs = self.params.len() as u64 + 1;
    state.builder.inst(Inst::PushU(nargs));
    state.gen_builtin_call("check_nargs");
    // store captured variables
    let len = self.captures_rev.len();
    for (i, id) in self.captures_rev.into_iter().rev().enumerate() {
      if i + 1 != len {
        state.builder.inst(Inst::Dup);
      }
      state.builder.inst(Inst::LdPO(i as i64));
      state.builder.inst(Inst::StV(id));
    }
    // store parameters
    for id in self.params.into_iter().rev() {
      state.builder.inst(Inst::StV(id));
    }
    // generate body and return
    self.expr.generate(state);
    state.builder.inst(Inst::Ret);
  }
}
