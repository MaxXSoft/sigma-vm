use crate::front::lexer::{PreDefOp, Token, TokenKind};
use laps::ast::{NonEmptyOptSepSeq, NonEmptySepSeq, OptPrefix, OptSepSeq, OptTokenPrefix, NonEmptySeq};
use laps::prelude::*;

token_ast! {
  #[derive(Debug)]
  pub macro Token<TokenKind> {
    [int] => { kind: TokenKind::Int(_), prompt: "integer literal" },
    [float] => { kind: TokenKind::Float(_), prompt: "floating-point literal" },
    [ch] => { kind: TokenKind::Char(_), prompt: "character literal" },
    [byte] => { kind: TokenKind::Byte(_), prompt: "byte literal" },
    [string] => { kind: TokenKind::Str(_), prompt: "string literal" },
    [rawstr] => { kind: TokenKind::RawStr(_), prompt: "raw string literal" },
    [bytes] => { kind: TokenKind::Bytes(_), prompt: "bytes literal" },
    [+] => { kind: TokenKind::PreDefOp(PreDefOp::Add) },
    [-] => { kind: TokenKind::PreDefOp(PreDefOp::Sub) },
    [*] => { kind: TokenKind::PreDefOp(PreDefOp::Mul) },
    [/] => { kind: TokenKind::PreDefOp(PreDefOp::Div) },
    [%] => { kind: TokenKind::PreDefOp(PreDefOp::Mod) },
    [&] => { kind: TokenKind::PreDefOp(PreDefOp::And) },
    [|] => { kind: TokenKind::PreDefOp(PreDefOp::Or) },
    [!] => { kind: TokenKind::PreDefOp(PreDefOp::Not) },
    [^] => { kind: TokenKind::PreDefOp(PreDefOp::Xor) },
    [<<] => { kind: TokenKind::PreDefOp(PreDefOp::Shl) },
    [>>] => { kind: TokenKind::PreDefOp(PreDefOp::Shr) },
    [&&] => { kind: TokenKind::PreDefOp(PreDefOp::LogicAnd) },
    [||] => { kind: TokenKind::PreDefOp(PreDefOp::LogicOr) },
    [==] => { kind: TokenKind::PreDefOp(PreDefOp::Eq) },
    [!=] => { kind: TokenKind::PreDefOp(PreDefOp::Ne) },
    [<] => { kind: TokenKind::PreDefOp(PreDefOp::Lt) },
    [<=] => { kind: TokenKind::PreDefOp(PreDefOp::Le) },
    [>] => { kind: TokenKind::PreDefOp(PreDefOp::Gt) },
    [>=] => { kind: TokenKind::PreDefOp(PreDefOp::Ge) },
    [=] => { kind: TokenKind::PreDefOp(PreDefOp::Assign) },
    [+=] => { kind: TokenKind::PreDefOp(PreDefOp::AddAssign) },
    [-=] => { kind: TokenKind::PreDefOp(PreDefOp::SubAssign) },
    [*=] => { kind: TokenKind::PreDefOp(PreDefOp::MulAssign) },
    [/=] => { kind: TokenKind::PreDefOp(PreDefOp::DivAssign) },
    [%=] => { kind: TokenKind::PreDefOp(PreDefOp::ModAssign) },
    [&=] => { kind: TokenKind::PreDefOp(PreDefOp::AndAssign) },
    [|=] => { kind: TokenKind::PreDefOp(PreDefOp::OrAssign) },
    [^=] => { kind: TokenKind::PreDefOp(PreDefOp::XorAssign) },
    [<<=] => { kind: TokenKind::PreDefOp(PreDefOp::ShlAssign) },
    [>>=] => { kind: TokenKind::PreDefOp(PreDefOp::ShrAssign) },
    [lpr] => { kind: TokenKind::PreDefOp(PreDefOp::LeftParen) },
    [rpr] => { kind: TokenKind::PreDefOp(PreDefOp::RightParen) },
    [lbk] => { kind: TokenKind::PreDefOp(PreDefOp::LeftBracket) },
    [rbk] => { kind: TokenKind::PreDefOp(PreDefOp::RightBracket) },
    [lbr] => { kind: TokenKind::PreDefOp(PreDefOp::LeftBrace) },
    [rbr] => { kind: TokenKind::PreDefOp(PreDefOp::RightBrace) },
    [.] => { kind: TokenKind::PreDefOp(PreDefOp::Dot) },
    [..] => { kind: TokenKind::PreDefOp(PreDefOp::AnyPat) },
    [...] => { kind: TokenKind::PreDefOp(PreDefOp::Repeat) },
    [->] => { kind: TokenKind::PreDefOp(PreDefOp::Arrow) },
    [,] => { kind: TokenKind::PreDefOp(PreDefOp::Comma) },
    [:] => { kind: TokenKind::PreDefOp(PreDefOp::Colon) },
    [@] => { kind: TokenKind::PreDefOp(PreDefOp::At) },
    [_] => { kind: TokenKind::PreDefOp(PreDefOp::Underscore) },
    [?] => { kind: TokenKind::PreDefOp(PreDefOp::Question) },
    [;] => { kind: TokenKind::PreDefOp(PreDefOp::Semicolon) },
    [op] => { kind: TokenKind::Op(_), prompt: "operator-like identifier" },
    [pub] => { kind: TokenKind::Ident(s) if s == "pub", prompt: "pub" },
    [import] => { kind: TokenKind::Ident(s) if s == "import", prompt: "import" },
    [static] => { kind: TokenKind::Ident(s) if s == "static", prompt: "static" },
    [mut] => { kind: TokenKind::Ident(s) if s == "mut", prompt: "mut" },
    [fn] => { kind: TokenKind::Ident(s) if s == "fn", prompt: "fn" },
    [native] => { kind: TokenKind::Ident(s) if s == "native", prompt: "native" },
    [trait] => { kind: TokenKind::Ident(s) if s == "trait", prompt: "trait" },
    [impl] => { kind: TokenKind::Ident(s) if s == "impl", prompt: "impl" },
    [for] => { kind: TokenKind::Ident(s) if s == "for", prompt: "for" },
    [where] => { kind: TokenKind::Ident(s) if s == "where", prompt: "where" },
    [i8] => { kind: TokenKind::Ident(s) if s == "i8", prompt: "i8" },
    [i16] => { kind: TokenKind::Ident(s) if s == "i16", prompt: "i16" },
    [i32] => { kind: TokenKind::Ident(s) if s == "i32", prompt: "i32" },
    [i64] => { kind: TokenKind::Ident(s) if s == "i64", prompt: "i64" },
    [u8] => { kind: TokenKind::Ident(s) if s == "u8", prompt: "u8" },
    [u16] => { kind: TokenKind::Ident(s) if s == "u16", prompt: "u16" },
    [u32] => { kind: TokenKind::Ident(s) if s == "u32", prompt: "u32" },
    [u64] => { kind: TokenKind::Ident(s) if s == "u64", prompt: "u64" },
    [f32] => { kind: TokenKind::Ident(s) if s == "f32", prompt: "f32" },
    [f64] => { kind: TokenKind::Ident(s) if s == "f64", prompt: "f64" },
    [char] => { kind: TokenKind::Ident(s) if s == "char", prompt: "char" },
    [str] => { kind: TokenKind::Ident(s) if s == "str", prompt: "str" },
    [struct] => { kind: TokenKind::Ident(s) if s == "struct", prompt: "struct" },
    [enum] => { kind: TokenKind::Ident(s) if s == "enum", prompt: "enum" },
    [type] => { kind: TokenKind::Ident(s) if s == "type", prompt: "type" },
    [Self] => { kind: TokenKind::Ident(s) if s == "Self", prompt: "Self" },
    [let] => { kind: TokenKind::Ident(s) if s == "let", prompt: "let" },
    [while] => { kind: TokenKind::Ident(s) if s == "while", prompt: "while" },
    [break] => { kind: TokenKind::Ident(s) if s == "break", prompt: "break" },
    [continue] => { kind: TokenKind::Ident(s) if s == "continue", prompt: "continue" },
    [if] => { kind: TokenKind::Ident(s) if s == "if", prompt: "if" },
    [else] => { kind: TokenKind::Ident(s) if s == "else", prompt: "else" },
    [return] => { kind: TokenKind::Ident(s) if s == "return", prompt: "return" },
    [ident] => { kind: TokenKind::Ident(_), prompt: "identifier" },
    [eof] => { kind: TokenKind::Eof },
  }
}

/// Annotated item.
pub type AnnotatedItem = OptPrefix<Anno, Item>;

/// Annotation.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Anno {
  pub _at: Token![@],
  pub ident: Token![ident],
  // TODO: support annotation macro.
}

/// Item.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Item {
  /// Import.
  Import(Import),
  /// Static variable definition.
  Static(OptPub<Static>),
  /// Function definition.
  FuncDef(FuncDef),
  /// Native declarations.
  NativeDecl(NativeDecl),
  /// Trait.
  Trait(OptPub<Trait>),
  /// Implementation.
  Impl(Impl),
}

/// Item that starts with an optional `pub`.
pub type OptPub<T> = OptTokenPrefix<Token![pub], T>;

/// Import.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Import {
  pub _import: Token![import],
  pub path: ImportPath,
}

/// Path of import.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum ImportPath {
  Path(Path),
  Paths(Paths),
}

/// Path.
#[derive(Debug, Parse)]
#[token(Token)]
pub struct Path {
  pub ident: Token![ident],
  pub segs: Vec<(Token![.], Token![ident])>,
  pub end: Option<(Token![.], PathsOrWildcard)>,
}

impl Spanned for Path {
  fn span(&self) -> laps::span::Span {
    let span = self.ident.span();
    if let Some(end) = &self.end {
      span.into_end_updated(end.span())
    } else if let Some(seg) = self.segs.last() {
      span.into_end_updated(seg.span())
    } else {
      span
    }
  }
}

/// Paths or wildcard.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum PathsOrWildcard {
  Paths(Paths),
  Wildcard(Token![*]),
}

/// Paths.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Paths {
  pub _lbr: Token![lbr],
  pub path: NonEmptyOptSepSeq<Path, Token![,]>,
  pub _rbr: Token![rbr],
}

/// Static variable definition.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Static {
  pub _static: Token![static],
  pub _mut: Option<Token![mut]>,
  pub ident: Token![ident],
  pub _colon: Token![:],
  pub ty: Type,
  pub _assign: Token![=],
  pub expr: Expr,
}

/// Function definition.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct FuncDef {
  pub decl: OptPub<FuncDecl>,
  pub body: Block,
}

/// Function declarations.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct FuncDecl {
  pub _fn: Token![fn],
  pub ident: Token![ident],
  pub implicit_params: Option<ImplicitParams>,
  pub params: Option<Params>,
  pub ret_ty: Option<(Token![->], Type)>,
  pub where_clause: Option<Where>,
}

/// Native declarations.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct NativeDecl {
  pub _native: Token![native],
  pub lib: Path,
  pub _lbr: Token![lbr],
  pub decls: Vec<OptPub<FuncDecl>>,
  pub _rbr: Token![rbr],
}

/// Trait.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Trait {
  pub _trait: Token![trait],
  pub ident: Token![ident],
  pub implicit_params: Option<ImplicitParams>,
  pub params: Option<Params>,
  pub inherit: Option<Inherit>,
  pub where_clause: Option<Where>,
  pub _lbr: Token![lbr],
  pub methods: Vec<Method>,
  pub _rbr: Token![rbr],
}

/// Inherit of trait.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Inherit {
  pub _colon: Token![:],
  pub traits: NonEmptySepSeq<PathExpr, Token![+]>,
}

/// Method of trait.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Option)]
pub struct Method {
  decl: FuncDecl,
  body: Option<Block>,
}

/// Implementation.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Impl {
  pub _impl: Token![impl],
  pub implicit_params: Option<ImplicitParams>,
  pub impl_trait: Option<(PathExpr, Token![for])>,
  pub ty: PathExpr,
  pub where_clause: Option<Where>,
  pub _lbr: Token![lbr],
  pub defs: Vec<FuncDef>,
  pub _rbr: Token![rbr],
}

/// Implicit parameters.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ImplicitParams {
  pub _lbk: Token![lbk],
  pub params: OptSepSeq<ImplicitParam, Token![,]>,
  pub _rbk: Token![rbk],
}

/// Implicit parameter.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ImplicitParam {
  pub rep_ident: OptPrefix<Token![...], Token![ident]>,
  pub ty: Option<(Token![:], Type)>,
  pub default: Option<(Token![=], Expr)>,
}

/// Implicit arguments.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ImplicitArgs {
  pub _lbk: Token![lbk],
  pub params: OptSepSeq<Expr, Token![,]>,
  pub _rbk: Token![rbk],
}

/// Parameters.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Params {
  pub _lpr: Token![lpr],
  pub params: OptSepSeq<Param, Token![,]>,
  pub _rpr: Token![rpr],
}

/// Parameter.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Param {
  pub rep_ident: OptPrefix<Token![...], Token![ident]>,
  pub _colon: Token![:],
  pub ty: Type,
}

/// Arguments.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Args {
  pub _lpr: Token![lpr],
  pub params: OptSepSeq<Expr, Token![,]>,
  pub _rpr: Token![rpr],
}

/// Where clause.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Where {
  pub _where: Token![where],
  pub bounds: NonEmptyOptSepSeq<WhereBound, Token![,]>,
}

/// Bound of where clause.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum WhereBound {
  Trait(TraitBound),
  Type(TypeBound),
}

/// Trait bound of where clause.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct TraitBound {
  pub ty: PathExpr,
  pub _colon: Token![:],
  pub bounds: NonEmptySepSeq<PathExpr, Token![+]>,
}

/// Type bound of where clause.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct TypeBound {
  pub ty: PathExpr,
  pub _colon: Token![:],
  pub bound: PathExpr,
}

/// Type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Type {
  Prim(PrimType),
  Struct(StructType),
  Enum(EnumType),
  Array(ArrayType),
  Tuple(TupleType),
  Func(FuncType),
  TypeOf(TypeOfType),
  Trait(TraitType),
  SelfTy(Token![Self]),
}

/// Primitive type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum PrimType {
  I8(Token![i8]),
  I16(Token![i16]),
  I32(Token![i32]),
  I64(Token![i64]),
  U8(Token![u8]),
  U16(Token![u16]),
  U32(Token![u32]),
  U64(Token![u64]),
  F32(Token![f32]),
  F64(Token![f64]),
  Char(Token![char]),
  Str(Token![str]),
  Never(Token![!]),
}

/// Structure type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct StructType {
  pub _struct: Token![struct],
  pub _lbr: Token![lbr],
  pub fields: OptSepSeq<OptPrefix<Token![pub], StructField>, Token![,]>,
  pub _rbr: Token![rbr],
}

/// Field of structure type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct StructField {
  pub ident: Token![ident],
  pub _colon: Token![:],
  pub ty: Type,
}

/// Enumerate type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct EnumType {
  pub _enum: Token![enum],
  pub _lbr: Token![lbr],
  pub variants: OptSepSeq<EnumVariant, Token![,]>,
  pub _rbr: Token![rbr],
}

/// Variant of enumerate type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct EnumVariant {
  pub ident: Token![ident],
  pub tuple: Option<TupleType>,
  pub value: Option<(Token![=], Expr)>,
}

/// Array type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ArrayType {
  pub _lbk: Token![lbk],
  pub ty: Box<Type>,
  pub _rbk: Token![rbk],
}

/// Tuple type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct TupleType {
  pub _lpr: Token![lpr],
  pub tys: RepTypes,
  pub _rpr: Token![rpr],
}

/// List of repeatable types.
pub type RepTypes = OptSepSeq<RepType, Token![,]>;

/// Repeatable type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_start(Option)]
pub struct RepType {
  pub rep: Option<Token![...]>,
  pub ty: Type,
}

/// Function type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct FuncType {
  pub _fn: Token![fn],
  pub implicit_params: Option<ImplicitParamsType>,
  pub params: Option<ParamsType>,
  pub ret_ty: Option<(Token![->], Box<Type>)>,
}

/// Type for implicit parameters.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ImplicitParamsType {
  pub _lbk: Token![lbk],
  pub tys: RepTypes,
  pub _rbk: Token![rbk],
}

/// Type for parameters.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ParamsType {
  pub _lpr: Token![lpr],
  pub tys: RepTypes,
  pub _rpr: Token![rpr],
}

/// Type of type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Option)]
pub struct TypeOfType {
  pub _type: Token![type],
  pub bound: Option<TotBound>,
}

/// Bound of type-of-type.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum TotBound {
  Trait(TraitTotBound),
  Value(ValueTotBound),
}

/// Trait type bound of type-of-type.
pub type TraitTotBound = NonEmptySeq<(Token![+], PathExpr)>;

/// Value type bound of type-of-type.
pub type ValueTotBound = (Token![:], TraitType);

/// Trait type.
pub type TraitType = NonEmptySepSeq<PathExpr, Token![+]>;

/// Statement.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Statement {
  Item(Item),
  Let(Let),
  Expr(Expr),
}

/// Let statement.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Let {
  pub _let: Token![let],
  pub _mut: Option<Token![mut]>,
  pub pat: ConcretePat,
  pub ty: Option<(Token![:], Type)>,
  pub _assign: Token![=],
  pub value: Expr,
}

/// Concrete pattern.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum ConcretePat {
  Var(VarPat),
  Dummy(Token![_]),
  Tuple(TuplePat),
  Array(ArrayPat),
  Struct(StructPat),
  Enum(EnumPat),
}

/// Pattern.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Pattern {
  Any(Token![..]),
  Concrete(ConcretePat),
}

/// Variable pattern.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Option)]
pub struct VarPat {
  pub ident: Token![ident],
  pub pat: Option<(Token![@], Box<ConcretePat>)>,
}

/// Tuple pattern.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct TuplePat {
  pub _lpr: Token![lpr],
  pub pats: OptSepSeq<Pattern, Token![,]>,
  pub _rpr: Token![rpr],
}

/// Array pattern.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ArrayPat {
  pub _lbk: Token![lbk],
  pub pats: OptSepSeq<Pattern, Token![,]>,
  pub _rbk: Token![rbk],
}

/// Structure pattern.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct StructPat {
  pub ty: PathExpr,
  pub _lbr: Token![lbr],
  pub pats: OptSepSeq<FieldPat, Token![,]>,
  pub _rbr: Token![rbr],
}

/// Field pattern of structure.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum FieldPat {
  #[spanned_end(Option)]
  Field(Token![ident], Option<(Token![:], ConcretePat)>),
  Any(Token![..]),
}

/// Enumerate pattern.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Option)]
pub struct EnumPat {
  pub ty: PathExpr,
  pub pat: Option<TuplePat>,
}

/// Expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Vec)]
pub struct Expr {
  pub bin: BinaryExpr,
  pub suffixes: Vec<Suffix>,
}

/// Suffix of expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Suffix {
  CallArgs(CallArgs),
  Access(Token![.], PathExpr),
  Try(Token![?]),
}

/// Argument list of function call.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum CallArgs {
  #[spanned_end(Option)]
  Implicit(ImplicitArgs, Option<Args>),
  Args(Args),
}

/// Binary expression.
pub type BinaryExpr = NonEmptySepSeq<Prefix, Op>;

/// Prefix expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_start(Vec)]
pub struct Prefix {
  pub ops: Vec<Op>,
  pub factor: Factor,
}

/// Operator.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Op {
  Add(Token![+]),
  Sub(Token![-]),
  Mul(Token![*]),
  Div(Token![/]),
  Mod(Token![%]),
  And(Token![&]),
  Or(Token![|]),
  Not(Token![!]),
  Xor(Token![^]),
  Shl(Token![<<]),
  Shr(Token![>>]),
  LogicAnd(Token![&&]),
  LogicOr(Token![||]),
  Eq(Token![==]),
  Ne(Token![!=]),
  Lt(Token![<]),
  Le(Token![<=]),
  Gt(Token![>]),
  Ge(Token![>=]),
  Asign(Token![=]),
  AddAsign(Token![+=]),
  SubAssign(Token![-=]),
  MulAssign(Token![*=]),
  DivAssign(Token![/=]),
  ModAssign(Token![%=]),
  AndAssign(Token![&=]),
  OrAssign(Token![|=]),
  XorAssign(Token![^=]),
  ShlAssign(Token![<<=]),
  ShrAssign(Token![>>=]),
  AnyPat(Token![..]),
  Arrow(Token![->]),
  Comma(Token![,]),
  Colon(Token![:]),
  Op(Token![op]),
  Ident(Token![ident]),
}

/// Factor expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Factor {
  Block(Block),
  While(OptPrefix<WhileLabel, While>),
  Break(Break),
  Continue(Continue),
  If(If),
  Return(Return),
  Literal(Literal),
  Underscore(Token![_]),
  ParenOrTuple(ParenOrTupleExpr),
  Array(ArrayExpr),
  Closure(Closure),
  Expand(Expand),
  Type(TypeExpr),
  PathOrStruct(PathOrStructExpr),
}

/// Block.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Block {
  pub _lbr: Token![lbr],
  pub stmts: OptSepSeq<Statement, Token![;]>,
  pub _rbr: Token![rbr],
}

/// While loop.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct While {
  pub _while: Token![while],
  pub cond: Cond,
  pub body: Block,
}

/// Label of while loop.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct WhileLabel {
  pub label: Label,
  pub _colon: Token![:],
}

/// Label reference.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Label {
  pub _at: Token![@],
  pub ident: Token![ident],
}

/// Condition expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Cond {
  Expr(Expr),
  Let(Let),
}

/// Break expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Option)]
pub struct Break {
  pub _break: Token![break],
  pub label: Option<Label>,
}

/// Continue expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Option)]
pub struct Continue {
  pub _continue: Token![continue],
  pub label: Option<Label>,
}

/// If expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Option)]
pub struct If {
  pub _if: Token![if],
  pub cond: Cond,
  pub body: Block,
  pub else_if: Option<(Token![else], Else)>,
}

/// Else part of if expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Else {
  If(Box<If>),
  Body(Block),
}

/// Return expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Option)]
pub struct Return {
  pub _return: Token![return],
  pub value: Option<Expr>,
}

/// Literal expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Literal {
  Int(Token![int]),
  Float(Token![float]),
  Char(Token![ch]),
  Byte(Token![byte]),
  Str(Token![string]),
  RawStr(Token![rawstr]),
  Bytes(Token![bytes]),
}

/// Parentheses expression or tuple expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ParenOrTupleExpr {
  pub _lpr: Token![lpr],
  pub value: OptSepSeq<Expr, Token![,]>,
  pub _rpr: Token![rpr],
}

/// Array expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ArrayExpr {
  pub _lbk: Token![lbk],
  pub value: OptSepSeq<Expr, Token![,]>,
  pub _rbk: Token![rbk],
}

/// Closure.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Closure {
  pub _fn: Token![fn],
  pub implicit_params: Option<ImplicitClosureParams>,
  pub params: Option<ClosureParams>,
  pub ret_type: Option<(Token![->], Type)>,
  pub where_clause: Option<Where>,
  pub body: Expr,
}

/// Implicit parameters of closure.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ImplicitClosureParams {
  pub _lbk: Token![lbk],
  pub value: OptSepSeq<ClosureParam, Token![,]>,
  pub _rbk: Token![rbk],
}

/// Parameters of closure.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct ClosureParams {
  pub _lpr: Token![lpr],
  pub value: OptSepSeq<ClosureParam, Token![,]>,
  pub _rpr: Token![rpr],
}

/// Parameter of closure.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Option)]
pub struct ClosureParam {
  pub ident: Token![ident],
  pub ty: Option<(Token![:], Type)>,
}

/// Expand expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Expand {
  pub _rep: Token![...],
  pub value: Expr,
}

/// Type expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct TypeExpr {
  pub _type: Token![type],
  pub ty: Type,
}

/// Path expression or structure expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
#[spanned_end(Option)]
pub struct PathOrStructExpr {
  pub path: PathExpr,
  pub struct_expr: Option<StructExpr>,
}

/// Path expression.
pub type PathExpr = NonEmptySepSeq<PathExprSeg, Token![.]>;

/// Segment of path expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct PathExprSeg {
  pub ident: Token![ident],
  pub implicit_args: Option<ImplicitArgs>,
  pub args: Option<Args>,
}

/// Structure expression (actually the trailing part).
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct StructExpr {
  pub _lbr: Token![lbr],
  pub fields: OptSepSeq<FieldExpr, Token![,]>,
  pub _rbr: Token![rbr],
}

/// Field of structure expression.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum FieldExpr {
  #[spanned_end(Option)]
  Field(Token![ident], Option<(Token![:], Expr)>),
  Fill(Token![..], Expr),
}
