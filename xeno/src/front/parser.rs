use crate::front::lexer::{PreDefOp, Token, TokenKind};
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
    [return] => { kind: TokenKind::Ident(s) if s == "return", prompt: "return" },
    [ident] => { kind: TokenKind::Ident(_), prompt: "identifier" },
    [eof] => { kind: TokenKind::Eof },
  }
}

// /// Annotated item.
// #[derive(Debug, Parse, Spanned)]
// #[token(Token)]
// pub struct AnnotatedItem {
//   anno: Option<Anno>,
//   item: Item,
// }

// /// Annotation.
// #[derive(Debug, Parse, Spanned)]
// #[token(Token)]
// pub struct Anno {
//   pub _at: Token![@],
//   pub ident: Token![ident],
//   // TODO: support annotation macro.
// }

// /// Item.
// #[derive(Debug, Parse, Spanned)]
// #[token(Token)]
// pub enum Item {
//   /// Import.
//   Import(Import),
//   /// Static variable definition.
//   Static(Static),
//   /// Function definition.
//   FuncDef(FuncDef),
//   /// Native declarations.
//   NativeDecl(NativeDecl),
//   /// Trait.
//   Trait(Trait),
//   /// Implementation.
//   Impl(Impl),
// }

// /// Import.
// #[derive(Debug, Parse, Spanned)]
// #[token(Token)]
// pub struct Import {
//   pub _import: Token![import],
//   //
// }

// /// Static variable definition.
// #[derive(Debug, Parse, Spanned)]
// #[token(Token)]
// pub struct Static {
//   //
// }

// /// Function definition.
// #[derive(Debug, Parse, Spanned)]
// #[token(Token)]
// pub struct FuncDef {
//   //
// }

// /// Native declarations.
// #[derive(Debug, Parse, Spanned)]
// #[token(Token)]
// pub struct NativeDecl {
//   //
// }

// /// Trait.
// #[derive(Debug, Parse, Spanned)]
// #[token(Token)]
// pub struct Trait {
//   //
// }

// /// Implementation.
// #[derive(Debug, Parse, Spanned)]
// #[token(Token)]
// pub struct Impl {
//   //
// }
