use crate::front::lexer::{Float, Int};

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
  /// Implicit parameters.
  pub implicit_params: Option<Vec<ImplicitParam>>,
  /// Parameters.
  pub params: Option<Vec<Param>>,
  /// Return type.
  pub ret_ty: Option<Type>,
}

/// Implicit parameter.
#[derive(Debug)]
pub struct ImplicitParam {
  /// Parameter.
  pub param: Param,
  /// Default value.
  pub default: Option<Expr>,
}

/// Parameter.
#[derive(Debug)]
pub struct Param {
  /// `true` if the parameter should be repeated.
  pub is_rep: bool,
  /// Parameter name.
  pub name: String,
  /// Parameter type.
  pub ty: Type,
}

/// Type.
#[derive(Debug)]
pub enum Type {
  /// Primitive type.
  Prim(PrimType),
  /// Structure type.
  Struct(StructType),
  /// Enumerate type.
  Enum(EnumType),
  /// Array type.
  Array(ArrayType),
  /// Tuple type.
  Tuple(TupleType),
  /// Function type.
  Func(FuncType),
  /// Type of type.
  TypeOf(TypeOfType),
  /// Trait type.
  Trait(TraitType),
  /// Self type.
  SelfTy,
}

/// Primitive type.
#[derive(Debug)]
pub enum PrimType {
  /// Signed 8-bit integer.
  I8,
  /// Signed 16-bit integer.
  I16,
  /// Signed 32-bit integer.
  I32,
  /// Signed 64-bit integer.
  I64,
  /// Unsigned 8-bit integer.
  U8,
  /// Unsigned 16-bit integer.
  U16,
  /// Unsigned 32-bit integer.
  U32,
  /// Unsigned 64-bit integer.
  U64,
  /// 32-bit floating point.
  F32,
  /// 64-bit floating point.
  F64,
  /// Unicode scalar value.
  Char,
  /// UTF-8 string.
  Str,
  /// Never type.
  Never,
}

/// Structure type.
#[derive(Debug)]
pub struct StructType {
  /// Fields.
  pub fields: Vec<StructField>,
}

/// Field of structure type.
#[derive(Debug)]
pub struct StructField {
  /// `true` if the field is public.
  pub is_pub: bool,
  /// Field name.
  pub name: String,
  /// Field type.
  pub ty: Type,
}

/// Enumerate type.
#[derive(Debug)]
pub struct EnumType {
  /// Variants.
  pub variants: Vec<EnumVariant>,
}

/// Variant of enumerate type.
#[derive(Debug)]
pub struct EnumVariant {
  /// Variant name.
  pub name: String,
  /// Variant data.
  pub data: Option<VariantData>,
}

/// Variant data of enumerate type.
#[derive(Debug)]
pub enum VariantData {
  Tuple(TupleType),
  Expr(Expr),
}

/// Array type.
#[derive(Debug)]
pub struct ArrayType {
  /// Element type.
  pub elem_ty: Box<Type>,
}

/// Tuple type.
#[derive(Debug)]
pub struct TupleType {
  /// Element types.
  pub elem_tys: Vec<RepType>,
}

/// Repeatable type.
#[derive(Debug)]
pub struct RepType {
  /// `true` if the type should be repeated.
  pub is_rep: bool,
  /// Type.
  pub ty: Type,
}

/// Function type.
#[derive(Debug)]
pub struct FuncType {
  /// Implicit parameters.
  pub implicit_params: Option<Vec<RepType>>,
  /// Parameters.
  pub params: Option<Vec<RepType>>,
  /// Return type.
  pub ret_ty: Option<Box<Type>>,
}

/// Type of type.
#[derive(Debug)]
pub struct TypeOfType {
  // TODO.
}

/// Trait type.
#[derive(Debug)]
pub struct TraitType {
  // TODO.
}

/// Statement.
#[derive(Debug)]
pub enum Statement {
  /// Static variable definition.
  StaticDef(StaticDef),
  /// Function definition.
  FuncDef(FuncDef),
  /// Let statement.
  Let(Let),
  /// Expression statement.
  Expr(Expr),
}

/// Let statement.
#[derive(Debug)]
pub struct Let {
  /// `true` if the binding is mutable.
  pub is_mut: bool,
  /// Binding pattern.
  pub pat: ConcretePat,
  /// Type.
  pub ty: Option<Type>,
  /// Value.
  pub val: Expr,
}

/// Concrete pattern.
#[derive(Debug)]
pub enum ConcretePat {
  /// Variable pattern.
  Var(VarPat),
  /// Dummy pattern (underscore).
  Dummy,
  /// Tuple pattern.
  Tuple(Vec<Pattern>),
  /// Array pattern.
  Array(Vec<Pattern>),
  /// Structure pattern.
  Struct(StructPat),
  /// Enumerate pattern.
  Enum(EnumPat),
}

/// Pattern.
#[derive(Debug)]
pub enum Pattern {
  /// Any pattern.
  Any,
  /// Concrete pattern.
  Concrete(ConcretePat),
}

/// Variable pattern.
#[derive(Debug)]
pub struct VarPat {
  /// Variable name.
  pub name: String,
  /// Binding pattern.
  pub pat: Option<Box<ConcretePat>>,
}

/// Structure pattern.
#[derive(Debug)]
pub struct StructPat {
  // TODO.
}

/// Enumerate pattern.
#[derive(Debug)]
pub struct EnumPat {
  // TODO.
}

/// Expression.
#[derive(Debug)]
pub enum Expr {
  /// Binary expression.
  Binary(Binary),
  /// Unary expression.
  Unary(Unary),
}

/// Binary expression.
#[derive(Debug)]
pub struct Binary {
  /// Operator.
  pub op: String,
  /// Left-hand side operand.
  pub lhs: Box<Expr>,
  /// Right-hand side operand.
  pub rhs: Box<Expr>,
}

/// Unary expression.
#[derive(Debug)]
pub enum Unary {
  /// Prefix expression.
  Prefix(Prefix),
  /// Call expression.
  Call(Call),
  /// Access expression.
  Access(Access),
  /// Try expression.
  Try(Box<Self>),
  /// Type cast expression.
  Cast(Cast),
  /// Factor expression.
  Factor(Factor),
}

/// Prefix expression.
#[derive(Debug)]
pub struct Prefix {
  /// Operator.
  pub op: String,
  /// Operand.
  pub opr: Box<Unary>,
}

/// Call expression.
#[derive(Debug)]
pub struct Call {
  /// Callee.
  pub callee: Box<Unary>,
  /// Arguments.
  pub args: CallArgs,
}

/// Argument list of function call.
#[derive(Debug)]
pub enum CallArgs {
  /// Implicit arguments with optional arguments.
  Implicit(Vec<Expr>, Option<Vec<Expr>>),
  /// Arguments.
  Args(Vec<Expr>),
}

/// Access expression.
#[derive(Debug)]
pub struct Access {
  // TODO.
}

/// Type cast expression.
#[derive(Debug)]
pub struct Cast {
  /// Expression to cast.
  pub expr: Box<Unary>,
  /// Type to cast to.
  pub ty: Type,
}

/// Factor expression.
#[derive(Debug)]
pub enum Factor {
  /// Block.
  Block(Block),
  /// While loop.
  While(While),
  /// Break.
  Break(Option<Label>),
  /// Continue.
  Continue(Option<Label>),
  /// If-else.
  If(If),
  /// Return.
  Return(Option<Box<Expr>>),
  /// Literal.
  Literal(Literal),
  /// Underscore.
  Underscore,
  /// Parenthesized expression.
  Paren(Box<Expr>),
  /// Tuple.
  Tuple(Vec<Expr>),
  /// Array.
  Array(Vec<Expr>),
  // TODO.
}

/// Block.
#[derive(Debug)]
pub struct Block {
  /// Statements.
  pub stmts: Vec<Statement>,
}

/// While loop.
#[derive(Debug)]
pub struct While {
  /// Label.
  pub label: Option<Label>,
  /// Condition.
  pub cond: Cond,
  /// Body.
  pub body: Block,
}

/// Label of while loop.
pub type Label = String;

/// Condition expression.
#[derive(Debug)]
pub enum Cond {
  /// Expression.
  Expr(Box<Expr>),
  /// Let binding.
  Let(Box<Let>),
}

/// If-else.
#[derive(Debug)]
pub struct If {
  /// Condition.
  pub cond: Cond,
  /// Then branch.
  pub then: Block,
  /// Else branch.
  pub else_then: Option<Else>,
}

/// Else branch of if-else.
#[derive(Debug)]
pub enum Else {
  /// If-else.
  If(Box<If>),
  /// Block.
  Body(Block),
}

/// Literal.
#[derive(Debug)]
pub enum Literal {
  /// Integer.
  Int(Int),
  /// Floating-point.
  Float(Float),
  /// Character.
  Char(char),
  /// Byte.
  Byte(u8),
  /// String.
  String(String),
  /// Bytes.
  Bytes(Vec<u8>),
}
