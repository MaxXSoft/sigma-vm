use crate::front::{ElemKind, Element};
use laps::span::{Result, Span};
use laps::{log_warning, return_error};
use std::collections::HashMap;

/// Statement.
#[derive(Debug)]
pub enum Statement {
  /// Definition.
  Define(Define),
  /// Expression.
  Expr(Expr),
}

/// Definition.
#[derive(Debug)]
pub struct Define {
  pub name: String,
  pub var: u64,
  pub expr: Expr,
}

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
  /// Variable reference from the global scope.
  GlobalVar(u64),
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
  pub fn generate(&mut self, elem: Element) -> Result<Option<Statement>> {
    // handle by kind
    match elem.kind {
      ElemKind::List(es) => {
        // get the first element
        let first = es
          .first()
          .ok_or_else(|| return_error!(elem.span, "list can not be empty"))?;
        // handle by kind
        match &first.kind {
          ElemKind::Num(_) | ElemKind::Str(_) => {
            return_error!(first.span, "element is not callable")
          }
          ElemKind::Sym(s) => match s.as_str() {
            "define" => {
              return self
                .gen_define(&es[1..], elem.span)
                .map(|d| Some(Statement::Define(d)))
            }
            "lambda" => {}
            "cond" => {
              return self
                .gen_cond(&es[1..], elem.span)
                .map(|a| Some(Statement::Expr(Expr::CompExpr(CompExpr::If(a)))))
            }
            _ => {}
          },
          _ => {}
        };
        // generate apply
        return self
          .gen_apply(&es)
          .map(|a| Some(Statement::Expr(Expr::CompExpr(CompExpr::Apply(a)))));
      }
      _ => {}
    }
    // unhandled, just ignore
    log_warning!(elem.span, "ignored this expression");
    Ok(None)
  }

  /// Returns the symbol from the current element.
  fn sym(elem: &Element) -> Result<String> {
    match &elem.kind {
      ElemKind::Sym(s) => Ok(s.clone()),
      _ => return_error!(elem.span, "expected symbol"),
    }
  }

  /// Generates a definition.
  fn gen_define(&mut self, elems: &[Element], span: Span) -> Result<Define> {
    if elems.len() != 2 {
      return_error!(span, "expected exactly 2 arguments")
    }
    let name = Self::sym(&elems[0])?;
    let var = self.env.define(name.clone());
    let expr = self.gen_expr(&elems[1])?;
    Ok(Define { name, var, expr })
  }

  /// Generates a lambda function.
  fn gen_lambda(&mut self, elems: &[Element], span: Span) -> Result<Lambda> {
    if elems.len() != 2 {
      return_error!(span, "expected exactly 2 arguments")
    }
    // get parameter list
    let params = match &elems[0].kind {
      ElemKind::List(es) => es,
      _ => return_error!(elems[0].span, "expected parameter list"),
    };
    self.env.enter();
    let params = params
      .iter()
      .enumerate()
      .map(|(i, p)| Self::sym(p).map(|s| self.env.define_arg(s, i as u64)))
      .collect::<Result<_>>()?;
    // generate body
    let expr = Box::new(self.gen_expr(&elems[1])?);
    self.env.exit();
    Ok(Lambda { params, expr })
  }

  /// Generates a conditional expression.
  fn gen_cond(&mut self, elems: &[Element], span: Span) -> Result<If> {
    if elems.is_empty() {
      return_error!(span, "expected at least 1 argument")
    }
    // check all conditions
    for elem in elems {
      // get condition and expression
      let (cond, expr) = match &elem.kind {
        ElemKind::List(es) => match &es[..] {
          [cond, expr] => (cond, expr),
          _ => return_error!(elem.span, "expected exactly 2 elements"),
        },
        _ => return_error!(elem.span, "expected list"),
      };
      //
    }
    todo!()
  }

  /// Generates a function application.
  fn gen_apply(&mut self, elems: &[Element]) -> Result<Apply> {
    todo!()
  }

  /// Generates an expression.
  fn gen_expr(&mut self, elem: &Element) -> Result<Expr> {
    match &elem.kind {
      ElemKind::Num(n) => Ok(Expr::Value(Value::Num(*n))),
      ElemKind::Str(s) => Ok(Expr::Value(Value::Str(s.clone()))),
      ElemKind::Sym(s) => self.gen_sym(s, &elem.span).map(Expr::Value),
      ElemKind::Quote(e) => Ok(Expr::Value(self.gen_quote(&e))),
      ElemKind::List(_) => return_error!(elem.span, "invalid value"),
    }
  }

  /// Generates a symbol.
  fn gen_sym(&mut self, sym: &str, span: &Span) -> Result<Value> {
    match self.env.get(sym) {
      Some(VarKind::Var(id)) => Ok(Value::Var(id)),
      Some(VarKind::OuterVar(id)) => Ok(Value::OuterVar(id)),
      None => return_error!(span, "symbol {sym} not found"),
    }
  }

  /// Generates a quotation.
  fn gen_quote(&mut self, elem: &Element) -> Value {
    match &elem.kind {
      ElemKind::Num(n) => Value::Num(*n),
      ElemKind::Str(s) => Value::Str(s.clone()),
      ElemKind::Sym(s) => Value::Sym(s.clone()),
      ElemKind::Quote(e) => Value::List(vec![Value::Sym("quote".into()), self.gen_quote(&e)]),
      ElemKind::List(es) => Value::List(es.iter().map(|e| self.gen_quote(e)).collect()),
    }
  }

  /// Generates on the given list.
  fn gen_list(&mut self, elems: Vec<Element>, span: Span) -> Result<Expr> {
    todo!()
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
  fn define(&mut self, name: String) -> u64 {
    self.scopes.last_mut().unwrap().define(name)
  }

  /// Defines a new argument. Returns the variable number.
  fn define_arg(&mut self, name: String, i: u64) -> u64 {
    self.scopes.last_mut().unwrap().define_arg(name, i)
  }

  /// Finds the given variable in all scopes.
  fn get(&mut self, name: &str) -> Option<VarKind> {
    let mut iter = self.scopes.iter();
    if let Some(id) = iter.next().unwrap().get(name) {
      Some(VarKind::Var(id))
    } else {
      for scope in iter {
        if let Some(id) = scope.get(name) {
          return Some(VarKind::OuterVar(id));
        }
      }
      None
    }
  }
}

/// Scope of environment.
struct Scope {
  vars: HashMap<String, u64>,
}

impl Scope {
  /// Creates a new scope.
  fn new() -> Self {
    Self {
      vars: HashMap::new(),
    }
  }

  /// Defines a new variable. Returns the variable number.
  fn define(&mut self, name: String) -> u64 {
    let id = self.vars.len() as u64;
    *self.vars.entry(name).or_insert(id)
  }

  /// Defines a new argument. Returns the variable number.
  fn define_arg(&mut self, name: String, i: u64) -> u64 {
    *self.vars.entry(name).or_insert(i)
  }

  /// Finds the given variable.
  fn get(&self, name: &str) -> Option<u64> {
    self.vars.get(name).copied()
  }
}

/// Kind of variable.
enum VarKind {
  Var(u64),
  OuterVar(u64),
}
