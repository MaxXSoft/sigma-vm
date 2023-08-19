use crate::front::{ElemKind, Element};
use laps::return_error;
use laps::span::{Result, Span};
use std::collections::HashMap;

/// Expression.
#[derive(Debug)]
pub enum Expr {
  /// Value (atomic expression).
  Value(Value),
  /// Complex expression.
  CompExpr(CompExpr),
  /// Let binding.
  Let(Let),
}

/// Value (atomic expression).
#[derive(Debug)]
pub enum Value {
  /// Number.
  Num(f64),
  /// String.
  Str(String),
  /// Symbol.
  Sym(String),
  /// List.
  List(Vec<Value>),
  /// Variable reference.
  Var(u64),
  /// Variable reference from an outer scope.
  OuterVar(u64),
  /// Lambda.
  Lambda(Lambda),
}

/// Complex expression.
#[derive(Debug)]
pub enum CompExpr {
  /// Function application.
  Apply(Apply),
  /// If expression.
  If(If),
}

/// Let binding.
#[derive(Debug)]
pub struct Let {
  pub var: u64,
  pub def: CompExpr,
  pub expr: Box<Expr>,
}

/// Lambda.
#[derive(Debug)]
pub struct Lambda {
  pub params: Vec<u64>,
  pub expr: Box<Expr>,
}

/// Function application.
#[derive(Debug)]
pub struct Apply {
  pub func: Value,
  pub args: Vec<Value>,
}

/// If expression.
#[derive(Debug)]
pub struct If {
  pub cond: Value,
  pub then: Box<Expr>,
  pub else_then: Box<Expr>,
}

/// A-normal form generator.
pub struct Generator {
  env: Env,
}

impl Generator {
  /// Creates a new generator.
  pub fn new() -> Self {
    Self { env: Env::new() }
  }

  /// Generates on the given element.
  pub fn generate(&mut self, elem: Element) -> Expr {
    match elem.kind {
      _ => todo!(),
    }
  }

  /// Generates a value.
  fn gen_value(&mut self, elem: Element) -> Result<Value> {
    match elem.kind {
      ElemKind::Num(n) => Ok(Value::Num(n)),
      ElemKind::Str(s) => Ok(Value::Str(s)),
      ElemKind::Sym(s) => self.gen_sym(s, elem.span),
      ElemKind::Quote(e) => Ok(self.gen_quote(*e)),
      ElemKind::List(_) => return_error!(elem.span, "invalid value"),
    }
  }

  /// Generates a symbol.
  fn gen_sym(&mut self, sym: String, span: Span) -> Result<Value> {
    match self.env.get(&sym) {
      Some(VarKind::Var(id, _)) => Ok(Value::Var(id)),
      Some(VarKind::OuterVar(id, _)) => Ok(Value::OuterVar(id)),
      None => return_error!(span, "symbol {sym} not found"),
    }
  }

  /// Generates a quotation.
  fn gen_quote(&mut self, elem: Element) -> Value {
    match elem.kind {
      ElemKind::Num(n) => Value::Num(n),
      ElemKind::Str(s) => Value::Str(s),
      ElemKind::Sym(s) => Value::Sym(s),
      ElemKind::Quote(e) => Value::List(vec![Value::Sym("quote".into()), self.gen_quote(*e)]),
      ElemKind::List(es) => Value::List(es.into_iter().map(|e| self.gen_quote(e)).collect()),
    }
  }
}

/// Environment for type checking.
struct Env {
  scopes: Vec<Scope>,
}

impl Env {
  /// Creates a new environment.
  fn new() -> Self {
    Self {
      scopes: vec![Scope::new()],
    }
  }

  /// Enters a new scope.
  fn enter(&mut self) {
    self.scopes.push(Scope::new());
  }

  /// Exits from the current scope.
  fn exit(&mut self) {
    self.scopes.pop();
  }

  /// Defines a new variable. Returns the variable number.
  fn define(&mut self, name: String, ty: Type) -> u64 {
    self.scopes.last_mut().unwrap().define(name, ty)
  }

  /// Finds the given variable in all scopes.
  fn get(&mut self, name: &str) -> Option<VarKind> {
    let mut iter = self.scopes.iter();
    if let Some((id, ty)) = iter.next().unwrap().get(name) {
      Some(VarKind::Var(*id, ty))
    } else {
      for scope in iter {
        if let Some((id, ty)) = scope.get(name) {
          return Some(VarKind::OuterVar(*id, ty));
        }
      }
      None
    }
  }
}

/// Scope of environment.
struct Scope {
  vars: HashMap<String, (u64, Type)>,
}

impl Scope {
  /// Creates a new scope.
  fn new() -> Self {
    Self {
      vars: HashMap::new(),
    }
  }

  /// Defines a new variable. Returns the variable number.
  fn define(&mut self, name: String, ty: Type) -> u64 {
    if let Some((id, t)) = self.vars.get_mut(&name) {
      *t = ty;
      *id
    } else {
      let id = self.vars.len() as u64;
      self.vars.insert(name, (id, ty));
      id
    }
  }

  /// Finds the given variable.
  fn get(&self, name: &str) -> Option<&(u64, Type)> {
    self.vars.get(name)
  }
}

/// Kind of variable.
enum VarKind<'t> {
  Var(u64, &'t Type),
  OuterVar(u64, &'t Type),
}

/// Type of value.
#[derive(Debug, Clone)]
enum Type {
  /// Number.
  Num,
  /// String.
  Str,
  /// Symbol.
  Sym,
  /// List.
  List(Vec<Type>),
  /// Lambda, with parameter types and return type.
  Lambda(Vec<Type>, Box<Type>),
  /// Unknown.
  Unknown,
}
