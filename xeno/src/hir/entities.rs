/// Static variable definition.
#[derive(Debug)]
pub struct StaticDef {
  /// `true` if the static variable is public.
  pub is_pub: bool,
  /// The declaration.
  pub decl: StaticDecl,
  /// Initial value of the variable.
  pub value: Expr,
}

/// Static variable declaration (for exporting/importing).
#[derive(Debug)]
pub struct StaticDecl {
  /// `true` if the static variable is mutable.
  pub is_mut: bool,
  /// Variable name.
  pub name: String,
  /// Type of variable.
  pub ty: Type,
}

/// Function definition.
#[derive(Debug)]
pub struct FuncDef {
  /// `true` if the function is public.
  pub is_pub: bool,
  /// Function declaration.
  pub decl: FuncDecl,
  /// Function body.
  pub body: Block,
}

/// Function declaration.
#[derive(Debug)]
pub struct FuncDecl {
  /// Function name.
  pub name: String,
  // TODO
}

/// Block.
#[derive(Debug)]
pub struct Block {
  //
}

/// Type.
#[derive(Debug)]
pub enum Type {
  //
}

/// Expression.
#[derive(Debug)]
pub struct Expr {
  //
}
