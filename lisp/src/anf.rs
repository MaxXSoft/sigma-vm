use crate::front::{ElemKind, Element};
use laps::span::{Result, Span};
use laps::{log_error, log_warning, return_error};
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
  /// Builtin function.
  Builtin(Builtin),
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

/// Builtin functions.
#[derive(Debug)]
pub enum Builtin {
  /// atom?
  Atom,
  /// number?
  Number,
  /// eq?
  Equal,
  /// car
  Car,
  /// cdr
  Cdr,
  /// cons
  Cons,
  /// list
  List,
  /// +
  Add,
  /// -
  Sub,
  /// *
  Mul,
  /// /
  Div,
  /// >
  Gt,
  /// <
  Lt,
  /// >=
  Ge,
  /// <=
  Le,
  /// =
  Eq,
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
                .gen_cond(&es[1..], &elem.span)
                .map(|e| Some(Statement::Expr(e)))
            }
            _ => return self.gen_apply(&es).map(|e| Some(Statement::Expr(e))),
          },
          _ => return self.gen_apply(&es).map(|e| Some(Statement::Expr(e))),
        };
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

  /// Generates a conditional expression.
  fn gen_cond(&mut self, elems: &[Element], span: &Span) -> Result<Expr> {
    if elems.is_empty() {
      return_error!(span, "expected at least 1 argument")
    }
    // check all conditions
    let mut conds = vec![];
    let mut else_then = None;
    for elem in elems {
      // check if should be skipped
      if else_then.is_some() {
        log_warning!(elem.span, "this branch will never be evaluated");
        continue;
      }
      // get condition and expression
      let (cond, expr) = match &elem.kind {
        ElemKind::List(es) => match &es[..] {
          [cond, expr] => (self.gen_expr(cond)?, self.gen_expr(expr)?),
          _ => return_error!(elem.span, "expected exactly 2 elements"),
        },
        _ => return_error!(elem.span, "expected list"),
      };
      // generate condition or else branch
      if matches!(&cond, Expr::Value(Value::Sym(s)) if s == "t") {
        else_then = Some(expr);
      } else {
        let (bs, v) = self.extract(cond);
        conds.push((bs, v, expr));
      }
    }
    // generate if
    if let Some(else_then) = else_then {
      Ok(conds.into_iter().rev().fold(else_then, |e, (bs, cond, t)| {
        Self::gen_let(
          bs,
          Expr::CompExpr(CompExpr::If(If {
            cond,
            then: Box::new(t),
            else_then: Box::new(e),
          })),
        )
      }))
    } else {
      return_error!(span, "missing else branch")
    }
  }

  /// Generates a function application.
  ///
  /// The element list must not empty.
  fn gen_apply(&mut self, elems: &[Element]) -> Result<Expr> {
    // collect bindings and elements
    let mut bindings = vec![];
    let mut new_elems = vec![];
    for elem in elems {
      let expr = self.gen_expr(elem)?;
      let (bs, v) = self.extract(expr);
      bindings.extend(bs);
      new_elems.push(v);
    }
    // generate expression
    Ok(Self::gen_let(
      bindings,
      Expr::CompExpr(CompExpr::Apply(Apply {
        func: new_elems.remove(0),
        args: new_elems,
      })),
    ))
  }

  /// Extracts bindings and the final value from the given expression.
  fn extract(&mut self, expr: Expr) -> (Vec<(u64, CompExpr)>, Value) {
    match expr {
      Expr::Value(v) => (vec![], v),
      Expr::CompExpr(c) => {
        let temp = self.env.define_temp();
        (vec![(temp, c)], Value::Var(temp))
      }
      Expr::Let(l) => self.extract_let(l),
    }
  }

  /// Extracts bindings and the final value from the given let expression.
  fn extract_let(&mut self, l: Let) -> (Vec<(u64, CompExpr)>, Value) {
    let mut bindings = vec![(l.var, l.def)];
    let value = match *l.expr {
      Expr::Value(v) => v,
      Expr::CompExpr(c) => {
        let temp = self.env.define_temp();
        bindings.push((temp, c));
        Value::Var(temp)
      }
      Expr::Let(l) => {
        let (bs, v) = self.extract_let(l);
        bindings.extend(bs);
        v
      }
    };
    (bindings, value)
  }

  /// Generates a let expression by the given bindings and expression.
  fn gen_let(bindings: Vec<(u64, CompExpr)>, expr: Expr) -> Expr {
    bindings.into_iter().rev().fold(expr, |e, (var, def)| {
      Expr::Let(Let {
        var,
        def,
        expr: Box::new(e),
      })
    })
  }

  /// Generates an expression.
  fn gen_expr(&mut self, elem: &Element) -> Result<Expr> {
    match &elem.kind {
      ElemKind::Num(n) => Ok(Expr::Value(Value::Num(*n))),
      ElemKind::Str(s) => Ok(Expr::Value(Value::Str(s.clone()))),
      ElemKind::Sym(s) => self.gen_sym(s, &elem.span).map(Expr::Value),
      ElemKind::Quote(e) => Ok(Expr::Value(self.gen_quote(&e))),
      ElemKind::List(es) => self.gen_list(es, &elem.span),
    }
  }

  /// Generates a symbol.
  fn gen_sym(&mut self, sym: &str, span: &Span) -> Result<Value> {
    self
      .env
      .get(sym)
      .ok_or_else(|| log_error!(span, "symbol {sym} not found"))
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
  fn gen_list(&mut self, elems: &[Element], span: &Span) -> Result<Expr> {
    // get the first element
    let first = elems
      .first()
      .ok_or_else(|| return_error!(span, "list can not be empty"))?;
    // handle by kind
    match &first.kind {
      ElemKind::Num(_) | ElemKind::Str(_) => {
        return_error!(first.span, "element is not callable")
      }
      ElemKind::Sym(s) => match s.as_str() {
        "define" => return_error!(span, "invalid definition"),
        "lambda" => return self.gen_lambda(&elems[1..], span),
        "cond" => return self.gen_cond(&elems[1..], span),
        _ => {}
      },
      _ => {}
    };
    // generate apply
    self.gen_apply(elems)
  }

  /// Generates a lambda function.
  fn gen_lambda(&mut self, elems: &[Element], span: &Span) -> Result<Expr> {
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
    Ok(Expr::Value(Value::Lambda(Lambda { params, expr })))
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

  /// Defines a new temporary variable. Returns the variable number.
  fn define_temp(&mut self) -> u64 {
    self.scopes.last_mut().unwrap().define_temp()
  }

  /// Finds the given variable in all scopes.
  fn get(&mut self, name: &str) -> Option<Value> {
    let mut iter = self.scopes.iter().enumerate().rev();
    if let Some(id) = iter.next().unwrap().1.get(name) {
      Some(Value::Var(id))
    } else {
      // find in outer scopes
      for (i, scope) in iter {
        if let Some(id) = scope.get(name) {
          return if i == 0 {
            Some(Value::GlobalVar(id))
          } else {
            Some(Value::OuterVar(id))
          };
        }
      }
      // check if is a builtin function
      match name {
        "atom?" => Some(Value::Builtin(Builtin::Atom)),
        "number?" => Some(Value::Builtin(Builtin::Number)),
        "eq?" => Some(Value::Builtin(Builtin::Equal)),
        "car" => Some(Value::Builtin(Builtin::Car)),
        "cdr" => Some(Value::Builtin(Builtin::Cdr)),
        "cons" => Some(Value::Builtin(Builtin::Cons)),
        "list" => Some(Value::Builtin(Builtin::List)),
        "+" => Some(Value::Builtin(Builtin::Add)),
        "-" => Some(Value::Builtin(Builtin::Sub)),
        "*" => Some(Value::Builtin(Builtin::Mul)),
        "/" => Some(Value::Builtin(Builtin::Div)),
        ">" => Some(Value::Builtin(Builtin::Gt)),
        "<" => Some(Value::Builtin(Builtin::Lt)),
        ">=" => Some(Value::Builtin(Builtin::Ge)),
        "<=" => Some(Value::Builtin(Builtin::Le)),
        "=" => Some(Value::Builtin(Builtin::Eq)),
        _ => None,
      }
    }
  }
}

/// Scope of environment.
struct Scope {
  vars: HashMap<String, u64>,
  next_var_id: u64,
}

impl Scope {
  /// Creates a new scope.
  fn new() -> Self {
    Self {
      vars: HashMap::new(),
      next_var_id: 0,
    }
  }

  /// Defines a new variable. Returns the variable number.
  fn define(&mut self, name: String) -> u64 {
    let id = self.next_var_id;
    self.next_var_id += 1;
    *self.vars.entry(name).or_insert(id)
  }

  /// Defines a new argument. Returns the variable number.
  fn define_arg(&mut self, name: String, i: u64) -> u64 {
    self.next_var_id = std::cmp::max(self.next_var_id, i + 1);
    *self.vars.entry(name).or_insert(i)
  }

  /// Defines a new temporary variable. Returns the variable number.
  fn define_temp(&mut self) -> u64 {
    let id = self.next_var_id;
    self.next_var_id += 1;
    id
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
  GlobalVar(u64),
  Builtin(Builtin),
}
