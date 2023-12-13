use laps::ast::{NonEmptySepSeq, SepSeq};
use laps::lexer::{signed_int_literal, str_literal, Lexer};
use laps::prelude::*;
use laps::reader::Reader;
use laps::span::Span;
use laps::token::TokenBuffer;
use laps::token::TokenStream;
use sigma_vm::bytecode::insts::Opcode;
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
  InstOrLabel(OpcOrLabel),
  /// Temporary label reference.
  #[regex(r"([0-9]|[1-9][0-9]+|0x[0-9a-fA-F]+|0b[01]+|0o[0-7]+)(f|b)")]
  TempLabelRef(TempLabelRef),
  /// Integer.
  #[regex(
    r"-?([0-9]|[1-9][0-9]+|0x[0-9a-fA-F]+|0b[01]+|0o[0-7]+)",
    signed_int_literal
  )]
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

/// Opcode or label.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpcOrLabel {
  Opcode(InstOpcode),
  Label(String),
}

impl fmt::Display for OpcOrLabel {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Opcode(o) => o.fmt(f),
      Self::Label(l) => l.fmt(f),
    }
  }
}

impl str::FromStr for OpcOrLabel {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    Ok(
      InstOpcode::from_str(s)
        .map(Self::Opcode)
        .unwrap_or_else(|_| Self::Label(s.into())),
    )
  }
}

/// Opcode of instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstOpcode {
  Nop,
  PushI,
  PushU,
  PushPc,
  Pop,
  Dup,
  DupS1,
  Swap,
  LdB,
  LdBU,
  LdH,
  LdHU,
  LdW,
  LdWU,
  LdD,
  LdP,
  LdBO,
  LdBUO,
  LdHO,
  LdHUO,
  LdWO,
  LdWUO,
  LdDO,
  LdPO,
  LdV,
  LdG,
  LdC,
  LaC,
  StB,
  StH,
  StW,
  StD,
  StBO,
  StHO,
  StWO,
  StDO,
  StV,
  StG,
  StA,
  New,
  NewO,
  NewOC,
  NewA,
  NewAC,
  Load,
  LoadC,
  LoadM,
  Bz,
  BzNP,
  Bnz,
  Loop,
  Jmp,
  JmpS,
  Call,
  CallS,
  CallExt,
  CallExtS,
  CallExtC,
  Ret,
  Sys,
  Break,
  Not,
  LNot,
  And,
  Or,
  Xor,
  Shl,
  Shr,
  Sar,
  Sext,
  Zext,
  Eq,
  Ne,
  Lt,
  Le,
  Gt,
  Ge,
  LtU,
  LeU,
  GtU,
  GeU,
  Neg,
  Add,
  Sub,
  Mul,
  Div,
  DivU,
  Mod,
  ModU,
  LtF,
  LeF,
  GtF,
  GeF,
  NegF,
  AddF,
  SubF,
  MulF,
  DivF,
  ModF,
  LtD,
  LeD,
  GtD,
  GeD,
  NegD,
  AddD,
  SubD,
  MulD,
  DivD,
  ModD,
  I2F,
  I2D,
  F2I,
  F2D,
  D2I,
  D2F,
  ITF,
  ITD,
  ITP,
}

impl fmt::Display for InstOpcode {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{self:?}")
  }
}

impl str::FromStr for InstOpcode {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s.to_lowercase().as_str() {
      "nop" => Ok(Self::Nop),
      "pushi" => Ok(Self::PushI),
      "pushu" => Ok(Self::PushU),
      "pushpc" => Ok(Self::PushPc),
      "pop" => Ok(Self::Pop),
      "dup" => Ok(Self::Dup),
      "dups1" => Ok(Self::DupS1),
      "swap" => Ok(Self::Swap),
      "ldb" => Ok(Self::LdB),
      "ldbu" => Ok(Self::LdBU),
      "ldh" => Ok(Self::LdH),
      "ldhu" => Ok(Self::LdHU),
      "ldw" => Ok(Self::LdW),
      "ldwu" => Ok(Self::LdWU),
      "ldd" => Ok(Self::LdD),
      "ldp" => Ok(Self::LdP),
      "ldbo" => Ok(Self::LdBO),
      "ldbuo" => Ok(Self::LdBUO),
      "ldho" => Ok(Self::LdHO),
      "ldhuo" => Ok(Self::LdHUO),
      "ldwo" => Ok(Self::LdWO),
      "ldwuo" => Ok(Self::LdWUO),
      "lddo" => Ok(Self::LdDO),
      "ldpo" => Ok(Self::LdPO),
      "ldv" => Ok(Self::LdV),
      "ldg" => Ok(Self::LdG),
      "ldc" => Ok(Self::LdC),
      "lac" => Ok(Self::LaC),
      "stb" => Ok(Self::StB),
      "sth" => Ok(Self::StH),
      "stw" => Ok(Self::StW),
      "std" => Ok(Self::StD),
      "stbo" => Ok(Self::StBO),
      "stho" => Ok(Self::StHO),
      "stwo" => Ok(Self::StWO),
      "stdo" => Ok(Self::StDO),
      "stv" => Ok(Self::StV),
      "stg" => Ok(Self::StG),
      "sta" => Ok(Self::StA),
      "new" => Ok(Self::New),
      "newo" => Ok(Self::NewO),
      "newoc" => Ok(Self::NewOC),
      "newa" => Ok(Self::NewA),
      "newac" => Ok(Self::NewAC),
      "load" => Ok(Self::Load),
      "loadc" => Ok(Self::LoadC),
      "loadm" => Ok(Self::LoadM),
      "bz" => Ok(Self::Bz),
      "bznp" => Ok(Self::BzNP),
      "bnz" => Ok(Self::Bnz),
      "loop" => Ok(Self::Loop),
      "jmp" => Ok(Self::Jmp),
      "jmps" => Ok(Self::JmpS),
      "call" => Ok(Self::Call),
      "calls" => Ok(Self::CallS),
      "callext" => Ok(Self::CallExt),
      "callexts" => Ok(Self::CallExtS),
      "callextc" => Ok(Self::CallExtC),
      "ret" => Ok(Self::Ret),
      "sys" => Ok(Self::Sys),
      "break" => Ok(Self::Break),
      "not" => Ok(Self::Not),
      "lnot" => Ok(Self::LNot),
      "and" => Ok(Self::And),
      "or" => Ok(Self::Or),
      "xor" => Ok(Self::Xor),
      "shl" => Ok(Self::Shl),
      "shr" => Ok(Self::Shr),
      "sar" => Ok(Self::Sar),
      "sext" => Ok(Self::Sext),
      "zext" => Ok(Self::Zext),
      "eq" => Ok(Self::Eq),
      "ne" => Ok(Self::Ne),
      "lt" => Ok(Self::Lt),
      "le" => Ok(Self::Le),
      "gt" => Ok(Self::Gt),
      "ge" => Ok(Self::Ge),
      "ltu" => Ok(Self::LtU),
      "leu" => Ok(Self::LeU),
      "gtu" => Ok(Self::GtU),
      "geu" => Ok(Self::GeU),
      "neg" => Ok(Self::Neg),
      "add" => Ok(Self::Add),
      "sub" => Ok(Self::Sub),
      "mul" => Ok(Self::Mul),
      "div" => Ok(Self::Div),
      "divu" => Ok(Self::DivU),
      "mod" => Ok(Self::Mod),
      "modu" => Ok(Self::ModU),
      "ltf" => Ok(Self::LtF),
      "lef" => Ok(Self::LeF),
      "gtf" => Ok(Self::GtF),
      "gef" => Ok(Self::GeF),
      "negf" => Ok(Self::NegF),
      "addf" => Ok(Self::AddF),
      "subf" => Ok(Self::SubF),
      "mulf" => Ok(Self::MulF),
      "divf" => Ok(Self::DivF),
      "modf" => Ok(Self::ModF),
      "ltd" => Ok(Self::LtD),
      "led" => Ok(Self::LeD),
      "gtd" => Ok(Self::GtD),
      "ged" => Ok(Self::GeD),
      "negd" => Ok(Self::NegD),
      "addd" => Ok(Self::AddD),
      "subd" => Ok(Self::SubD),
      "muld" => Ok(Self::MulD),
      "divd" => Ok(Self::DivD),
      "modd" => Ok(Self::ModD),
      "i2f" => Ok(Self::I2F),
      "i2d" => Ok(Self::I2D),
      "f2i" => Ok(Self::F2I),
      "f2d" => Ok(Self::F2D),
      "d2i" => Ok(Self::D2I),
      "d2f" => Ok(Self::D2F),
      "itf" => Ok(Self::ITF),
      "itd" => Ok(Self::ITD),
      "itp" => Ok(Self::ITP),
      _ => Err(()),
    }
  }
}

impl From<InstOpcode> for Opcode {
  fn from(op: InstOpcode) -> Self {
    match op {
      InstOpcode::Nop => Self::Nop,
      InstOpcode::PushI => Self::PushI,
      InstOpcode::PushU => Self::PushU,
      InstOpcode::PushPc => Self::PushPc,
      InstOpcode::Pop => Self::Pop,
      InstOpcode::Dup => Self::Dup,
      InstOpcode::DupS1 => Self::DupS1,
      InstOpcode::Swap => Self::Swap,
      InstOpcode::LdB => Self::LdB,
      InstOpcode::LdBU => Self::LdBU,
      InstOpcode::LdH => Self::LdH,
      InstOpcode::LdHU => Self::LdHU,
      InstOpcode::LdW => Self::LdW,
      InstOpcode::LdWU => Self::LdWU,
      InstOpcode::LdD => Self::LdD,
      InstOpcode::LdP => Self::LdP,
      InstOpcode::LdBO => Self::LdBO,
      InstOpcode::LdBUO => Self::LdBUO,
      InstOpcode::LdHO => Self::LdHO,
      InstOpcode::LdHUO => Self::LdHUO,
      InstOpcode::LdWO => Self::LdWO,
      InstOpcode::LdWUO => Self::LdWUO,
      InstOpcode::LdDO => Self::LdDO,
      InstOpcode::LdPO => Self::LdPO,
      InstOpcode::LdV => Self::LdV,
      InstOpcode::LdG => Self::LdG,
      InstOpcode::LdC => Self::LdC,
      InstOpcode::LaC => Self::LaC,
      InstOpcode::StB => Self::StB,
      InstOpcode::StH => Self::StH,
      InstOpcode::StW => Self::StW,
      InstOpcode::StD => Self::StD,
      InstOpcode::StBO => Self::StBO,
      InstOpcode::StHO => Self::StHO,
      InstOpcode::StWO => Self::StWO,
      InstOpcode::StDO => Self::StDO,
      InstOpcode::StV => Self::StV,
      InstOpcode::StG => Self::StG,
      InstOpcode::StA => Self::StA,
      InstOpcode::New => Self::New,
      InstOpcode::NewO => Self::NewO,
      InstOpcode::NewOC => Self::NewOC,
      InstOpcode::NewA => Self::NewA,
      InstOpcode::NewAC => Self::NewAC,
      InstOpcode::Load => Self::Load,
      InstOpcode::LoadC => Self::LoadC,
      InstOpcode::LoadM => Self::LoadM,
      InstOpcode::Bz => Self::Bz,
      InstOpcode::BzNP => Self::BzNP,
      InstOpcode::Bnz => Self::Bnz,
      InstOpcode::Loop => Self::Loop,
      InstOpcode::Jmp => Self::Jmp,
      InstOpcode::JmpS => Self::JmpS,
      InstOpcode::Call => Self::Call,
      InstOpcode::CallS => Self::CallS,
      InstOpcode::CallExt => Self::CallExt,
      InstOpcode::CallExtS => Self::CallExtS,
      InstOpcode::CallExtC => Self::CallExtC,
      InstOpcode::Ret => Self::Ret,
      InstOpcode::Sys => Self::Sys,
      InstOpcode::Break => Self::Break,
      InstOpcode::Not => Self::Not,
      InstOpcode::LNot => Self::LNot,
      InstOpcode::And => Self::And,
      InstOpcode::Or => Self::Or,
      InstOpcode::Xor => Self::Xor,
      InstOpcode::Shl => Self::Shl,
      InstOpcode::Shr => Self::Shr,
      InstOpcode::Sar => Self::Sar,
      InstOpcode::Sext => Self::Sext,
      InstOpcode::Zext => Self::Zext,
      InstOpcode::Eq => Self::Eq,
      InstOpcode::Ne => Self::Ne,
      InstOpcode::Lt => Self::Lt,
      InstOpcode::Le => Self::Le,
      InstOpcode::Gt => Self::Gt,
      InstOpcode::Ge => Self::Ge,
      InstOpcode::LtU => Self::LtU,
      InstOpcode::LeU => Self::LeU,
      InstOpcode::GtU => Self::GtU,
      InstOpcode::GeU => Self::GeU,
      InstOpcode::Neg => Self::Neg,
      InstOpcode::Add => Self::Add,
      InstOpcode::Sub => Self::Sub,
      InstOpcode::Mul => Self::Mul,
      InstOpcode::Div => Self::Div,
      InstOpcode::DivU => Self::DivU,
      InstOpcode::Mod => Self::Mod,
      InstOpcode::ModU => Self::ModU,
      InstOpcode::LtF => Self::LtF,
      InstOpcode::LeF => Self::LeF,
      InstOpcode::GtF => Self::GtF,
      InstOpcode::GeF => Self::GeF,
      InstOpcode::NegF => Self::NegF,
      InstOpcode::AddF => Self::AddF,
      InstOpcode::SubF => Self::SubF,
      InstOpcode::MulF => Self::MulF,
      InstOpcode::DivF => Self::DivF,
      InstOpcode::ModF => Self::ModF,
      InstOpcode::LtD => Self::LtD,
      InstOpcode::LeD => Self::LeD,
      InstOpcode::GtD => Self::GtD,
      InstOpcode::GeD => Self::GeD,
      InstOpcode::NegD => Self::NegD,
      InstOpcode::AddD => Self::AddD,
      InstOpcode::SubD => Self::SubD,
      InstOpcode::MulD => Self::MulD,
      InstOpcode::DivD => Self::DivD,
      InstOpcode::ModD => Self::ModD,
      InstOpcode::I2F => Self::I2F,
      InstOpcode::I2D => Self::I2D,
      InstOpcode::F2I => Self::F2I,
      InstOpcode::F2D => Self::F2D,
      InstOpcode::D2I => Self::D2I,
      InstOpcode::D2F => Self::D2F,
      InstOpcode::ITF => Self::ITF,
      InstOpcode::ITD => Self::ITD,
      InstOpcode::ITP => Self::ITP,
    }
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
    [opcode] => { kind: TokenKind::InstOrLabel(OpcOrLabel::Opcode(_)), prompt: "opcode" },
    [label] => { kind: TokenKind::InstOrLabel(OpcOrLabel::Label(_)), prompt: "label" },
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
  Instruction(Instruction),
  LabelDef(LabelDef),
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
  pub end_label: LabelRef,
  pub _comma3: Token![,],
  pub num_args: NumArgs,
  pub _comma4: Token![,],
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
#[derive(Debug)]
pub struct Instruction {
  pub opcode: InstOpcode,
  pub op_span: Span,
  pub opr: Option<InstOperand>,
}

impl<TS> Parse<TS> for Instruction
where
  TS: TokenStream<Token = Token>,
{
  fn parse(tokens: &mut TS) -> laps::span::Result<Self> {
    // parse opcode
    let opcode: Token![opcode] = tokens.parse()?;
    let op_span = opcode.span();
    let opcode = match opcode.unwrap::<OpcOrLabel, _>() {
      OpcOrLabel::Opcode(opcode) => opcode,
      _ => unreachable!(),
    };
    // parse operand
    let opr = if Opcode::from(opcode.clone()).operand_type().is_some() {
      Some(tokens.parse()?)
    } else {
      None
    };
    Ok(Self {
      opcode,
      op_span,
      opr,
    })
  }

  fn maybe(tokens: &mut TS) -> laps::span::Result<bool> {
    <Token![opcode]>::maybe(tokens)
  }
}

impl Spanned for Instruction {
  fn span(&self) -> Span {
    let mut span = self.op_span.clone();
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
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub struct LabelDef {
  pub kind: LabelDefKind,
  pub _colon: Token![:],
}

/// Kind of label definition.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
pub enum LabelDefKind {
  Named(Token![label]),
  Temp(Token![int]),
}

/// Label reference.
#[derive(Debug, Spanned)]
pub enum LabelRef {
  Named(Token![label]),
  Temp(Token![tlr]),
}

impl<TS> Parse<TS> for LabelRef
where
  TS: TokenStream<Token = Token>,
{
  fn parse(tokens: &mut TS) -> laps::span::Result<Self> {
    Ok(if <Token![label]>::maybe(tokens)? {
      Self::Named(tokens.parse()?)
    } else {
      Self::Temp(tokens.parse()?)
    })
  }

  fn maybe(tokens: &mut TS) -> laps::span::Result<bool> {
    if tokens
      .lookahead()
      .maybe(Token![label])?
      .maybe(Token![:])?
      .result()?
    {
      return Ok(false);
    }
    Ok(<Token![label]>::maybe(tokens)? || <Token![tlr]>::maybe(tokens)?)
  }
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
