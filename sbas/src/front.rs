use laps::ast::{NonEmptySepSeq, SepSeq};
use laps::lexer::{int_literal, str_literal, Lexer};
use laps::prelude::*;
use laps::reader::Reader;
use laps::token::TokenBuffer;
use laps::token::TokenStream;
use std::{fmt, io, str};

/// Kind of token.
#[token_kind]
#[derive(Debug, Tokenize)]
pub enum TokenKind {
  /// Spaces and comments.
  #[skip(r"\s+|#.*\n|#.*")]
  _Skip,
  /// Directive.
  #[regex(r"\.[a-z0-9]+")]
  Directive(Directive),
  /// Section.
  #[regex(r"consts|exports|insts|custom")]
  Section(Section),
  /// Variadic.
  #[regex(r"variadic")]
  Variadic,
  /// Instruction or label.
  #[regex(r"[_a-zA-Z][_a-zA-Z0-9]*")]
  InstOrLabel(InstOrLabel),
  /// Temporary label reference.
  #[regex(r"([0-9]|[1-9][0-9]+|0x[0-9a-fA-F]+|0b[01]+|0o[0-7]+)(f|b)")]
  TempLabelRef(TempLabelRef),
  /// Integer.
  // TODO: handle sign
  #[regex(r"-?([0-9]|[1-9][0-9]+|0x[0-9a-fA-F]+|0b[01]+|0o[0-7]+)", int_literal)]
  Int(u64),
  /// Floating point.
  #[regex(r"-?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?")]
  Float(f64),
  /// String.
  #[regex(
    r#""([^\x00-\x1f"\\]|\\([rnt0\\'"]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}))*""#,
    str_literal
  )]
  Str(String),
  /// Other character.
  #[regex(r".")]
  Other(char),
  /// End-of-file.
  #[eof]
  Eof,
}

/// Directive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Directive {
  Section,
  Export,
  I8,
  U8,
  I16,
  U16,
  I32,
  U32,
  I64,
  U64,
  F32,
  F64,
  Str,
  Object,
  Raw,
  Bytes,
}

impl fmt::Display for Directive {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Section => write!(f, "section"),
      Self::Export => write!(f, "export"),
      Self::I8 => write!(f, "i8"),
      Self::U8 => write!(f, "u8"),
      Self::I16 => write!(f, "i16"),
      Self::U16 => write!(f, "u16"),
      Self::I32 => write!(f, "i32"),
      Self::U32 => write!(f, "u32"),
      Self::I64 => write!(f, "i64"),
      Self::U64 => write!(f, "u64"),
      Self::F32 => write!(f, "f32"),
      Self::F64 => write!(f, "f64"),
      Self::Str => write!(f, "str"),
      Self::Object => write!(f, "object"),
      Self::Raw => write!(f, "raw"),
      Self::Bytes => write!(f, "bytes"),
    }
  }
}

impl str::FromStr for Directive {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match &s[1..] {
      "section" => Ok(Self::Section),
      "export" => Ok(Self::Export),
      "i8" => Ok(Self::I8),
      "u8" => Ok(Self::U8),
      "i16" => Ok(Self::I16),
      "u16" => Ok(Self::U16),
      "i32" => Ok(Self::I32),
      "u32" => Ok(Self::U32),
      "i64" => Ok(Self::I64),
      "u64" => Ok(Self::U64),
      "f32" => Ok(Self::F32),
      "f64" => Ok(Self::F64),
      "str" => Ok(Self::Str),
      "object" => Ok(Self::Object),
      "raw" => Ok(Self::Raw),
      "bytes" => Ok(Self::Bytes),
      _ => Err(()),
    }
  }
}

/// Section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Section {
  Consts,
  Exports,
  Insts,
  Custom,
}

impl fmt::Display for Section {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Consts => write!(f, "consts"),
      Self::Exports => write!(f, "exports"),
      Self::Insts => write!(f, "insts"),
      Self::Custom => write!(f, "custom"),
    }
  }
}

impl str::FromStr for Section {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s {
      "consts" => Ok(Self::Consts),
      "exports" => Ok(Self::Exports),
      "insts" => Ok(Self::Insts),
      "custom" => Ok(Self::Custom),
      _ => Err(()),
    }
  }
}

/// Instruction or label.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstOrLabel(pub String);

impl fmt::Display for InstOrLabel {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.0.fmt(f)
  }
}

impl str::FromStr for InstOrLabel {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    Ok(Self(s.into()))
  }
}

/// Temporary label reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TempLabelRef {
  pub label: u64,
  pub front: bool,
}

impl fmt::Display for TempLabelRef {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}{}", self.label, if self.front { 'f' } else { 'b' })
  }
}

impl str::FromStr for TempLabelRef {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let (label, front) = (&s[..s.len() - 1], s.chars().last().unwrap());
    label
      .parse()
      .map(|label| Self {
        label,
        front: front == 'f',
      })
      .map_err(|_| ())
  }
}

/// Type of token.
type Token = laps::token::Token<TokenKind>;

token_ast! {
  #[derive(Debug)]
  pub macro Token<TokenKind> {
    [section] => { kind: TokenKind::Directive(Directive::Section) },
    [export] => { kind: TokenKind::Directive(Directive::Export) },
    [i8] => { kind: TokenKind::Directive(Directive::I8) },
    [u8] => { kind: TokenKind::Directive(Directive::U8) },
    [i16] => { kind: TokenKind::Directive(Directive::I16) },
    [u16] => { kind: TokenKind::Directive(Directive::U16) },
    [i32] => { kind: TokenKind::Directive(Directive::I32) },
    [u32] => { kind: TokenKind::Directive(Directive::U32) },
    [i64] => { kind: TokenKind::Directive(Directive::I64) },
    [u64] => { kind: TokenKind::Directive(Directive::U64) },
    [f32] => { kind: TokenKind::Directive(Directive::F32) },
    [f64] => { kind: TokenKind::Directive(Directive::F64) },
    [str] => { kind: TokenKind::Directive(Directive::Str) },
    [object] => { kind: TokenKind::Directive(Directive::Object) },
    [raw] => { kind: TokenKind::Directive(Directive::Raw) },
    [bytes] => { kind: TokenKind::Directive(Directive::Bytes) },
    [sec] => { kind: TokenKind::Section(_), prompt: "section" },
    [va] => { kind: TokenKind::Variadic },
    [il] => { kind: TokenKind::InstOrLabel(_), prompt: "instruction or label" },
    [tlr] => { kind: TokenKind::TempLabelRef(_), prompt: "temporary label reference" },
    [int] => { kind: TokenKind::Int(_), prompt: "integer" },
    [float] => { kind: TokenKind::Float(_), prompt: "floating point" },
    [string] => { kind: TokenKind::Str(_), prompt: "string" },
    [,] => { kind: TokenKind::Other(',') },
    [lbc] => { kind: TokenKind::Other('[') },
    [rbc] => { kind: TokenKind::Other(']') },
    [:] => { kind: TokenKind::Other(':') },
    [eof] => { kind: TokenKind::Eof },
  }
}

/// Statement or end-of-file.
#[derive(Parse)]
#[token(Token)]
enum StatementOrEof {
  Statement(Statement),
  Eof(Token![eof]),
}

/// Statement.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum Statement {
  SectionDecl(SectionDecl),
  Export(Export),
  IntConst(IntConst),
  FloatConst(FloatConst),
  StrConst(StrConst),
  Object(Object),
  RawConst(RawConst),
  Bytes(Bytes),
  LabelDef(LabelDef),
  Instruction(Instruction),
}

/// Section declaration.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct SectionDecl {
  pub _section: Token![section],
  pub sec: Token![sec],
}

/// Export information.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Export {
  pub _export: Token![export],
  pub name: Token![string],
  pub _comma1: Token![,],
  pub label: LabelRef,
  pub _comma2: Token![,],
  pub num_args: NumArgs,
  pub _comma3: Token![,],
  pub num_rets: Token![int],
}

/// Number of arguments.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum NumArgs {
  Variadic(Token![va]),
  Num(Token![int]),
}

/// Integer constant.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct IntConst {
  pub kind: IntConstKind,
  pub value: Token![int],
}

/// Kind of integer constant.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum IntConstKind {
  I8(Token![i8]),
  U8(Token![u8]),
  I16(Token![i16]),
  U16(Token![u16]),
  I32(Token![i32]),
  U32(Token![u32]),
  I64(Token![i64]),
  U64(Token![u64]),
}

/// Floating point constant.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct FloatConst {
  pub kind: FloatConstKind,
  pub value: Token![float],
}

/// Kind of floating point constant.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum FloatConstKind {
  F32(Token![f32]),
  F64(Token![f64]),
}

/// String constant.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct StrConst {
  pub _str: Token![str],
  pub value: Token![string],
}

/// Object metadata.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Object {
  pub _object: Token![object],
  pub size: Token![int],
  pub _comma1: Token![,],
  pub align: Token![int],
  pub _comma2: Token![,],
  pub destructor: Option<Destructor>,
  pub _lbc: Token![lbc],
  pub offsets: SepSeq<Token![int], Token![,]>,
  pub _rbc: Token![rbc],
}

/// Destructor of an object metadata.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Destructor {
  pub destructor: LabelRef,
  pub _comma: Token![,],
}

/// Raw constant.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct RawConst {
  pub _raw: Token![raw],
  pub values: NonEmptySepSeq<RawValue, Token![,]>,
}

/// Raw constant value.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum RawValue {
  Str(Token![string]),
  Byte(Token![int]),
}

/// Byte sequence.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct Bytes {
  pub _bytes: Token![bytes],
  pub values: NonEmptySepSeq<RawValue, Token![,]>,
}

/// Instruction.
#[derive(Debug, Parse)]
#[token(Token)]
pub struct Instruction {
  pub opcode: Token![il],
  pub opr: Option<InstOperand>,
}

impl Spanned for Instruction {
  fn span(&self) -> laps::span::Span {
    let mut span = self.opcode.span();
    if let Some(opr) = &self.opr {
      span.update_end(opr.span());
    }
    span
  }
}

//// Instruction operand.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum InstOperand {
  Imm(Token![int]),
  LabelRef(LabelRef),
}

/// Label definition.
#[derive(Debug, Spanned)]
pub struct LabelDef {
  pub kind: LabelDefKind,
  pub _colon: Token![:],
}

impl<TS> Parse<TS> for LabelDef
where
  TS: TokenStream<Token = Token>,
{
  fn parse(tokens: &mut TS) -> laps::span::Result<Self> {
    Ok(Self {
      kind: tokens.parse()?,
      _colon: tokens.parse()?,
    })
  }

  fn maybe(tokens: &mut TS) -> laps::span::Result<bool> {
    Ok(
      tokens
        .lookahead()
        .maybe(Token![il])?
        .maybe(Token![:])?
        .result()?
        || tokens.lookahead().maybe(Token![int])?.result()?,
    )
  }
}

/// Kind of label definition.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum LabelDefKind {
  Named(Token![il]),
  Temp(Token![int]),
}

/// Label reference.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum LabelRef {
  Named(Token![il]),
  Temp(Token![tlr]),
}

/// Bytecode assembly parser.
pub struct Parser<R> {
  tokens: TokenBuffer<Lexer<Reader<R>, TokenKind>, Token>,
}

impl<R> Parser<R> {
  /// Creates a new parser from the given reader.
  pub fn new(reader: Reader<R>) -> Self {
    Self {
      tokens: TokenBuffer::new(TokenKind::lexer(reader)),
    }
  }

  /// Parses the next statement.
  pub fn parse(&mut self) -> laps::span::Result<Option<Statement>>
  where
    R: io::Read,
  {
    Ok(match self.tokens.parse::<StatementOrEof>()? {
      StatementOrEof::Statement(stmt) => Some(stmt),
      StatementOrEof::Eof(_) => None,
    })
  }
}
