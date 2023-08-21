use laps::ast::NonEmptySepSeq;
use laps::lexer::{int_literal, str_literal};
use laps::prelude::*;
use std::{fmt, str};

/// Kind of token.
#[token_kind]
#[derive(Debug, Tokenize)]
enum TokenKind {
  /// Spaces and comments.
  #[skip(r"\s+|#.*\n|#.*")]
  _Skip,
  /// Directive.
  #[regex(r"\.[a-z]+")]
  Directive(Directive),
  /// Label.
  #[regex(r"([_a-zA-Z][_a-zA-Z0-9]*|[0-9]|[1-9][0-9]+):")]
  Label(Label),
  /// Section.
  #[regex(r"consts|exports|insts|custom")]
  Section(Section),
  /// Variadic.
  #[regex(r"variadic")]
  Variadic,
  /// Instruction.
  #[regex(r"[a-z]+")]
  Inst(Inst),
  /// Integer.
  #[regex(r"[0-9]|[1-9][0-9]+|0x[0-9a-fA-F]+|0b[01]+|0o[0-7]+", int_literal)]
  Int(u64),
  /// Floating point.
  #[regex(r"-?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?")]
  Float(f64),
  /// String.
  #[regex(
    r#""([^"\\]|\\([rnt0\\'"]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}))*""#,
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
enum Directive {
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
    match s {
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

/// Label.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Label {
  Named(String),
  Temp(u32),
}

impl fmt::Display for Label {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Named(n) => write!(f, "{n}:"),
      Self::Temp(t) => write!(f, "{t}:"),
    }
  }
}

impl str::FromStr for Label {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match &s[..s.len() - 1] {
      "" => Err(()),
      s => Ok(
        s.parse()
          .ok()
          .map(Self::Temp)
          .unwrap_or_else(|| Self::Named(s.into())),
      ),
    }
  }
}

/// Section.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Section {
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

/// Instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Inst {
  Nop,
  PushI,
  PushU,
  Pop,
  Dup,
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
  Bnz,
  Jmp,
  Call,
  CallExt,
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

impl fmt::Display for Inst {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Nop => write!(f, "nop"),
      Self::PushI => write!(f, "pushi"),
      Self::PushU => write!(f, "pushu"),
      Self::Pop => write!(f, "pop"),
      Self::Dup => write!(f, "dup"),
      Self::Swap => write!(f, "swap"),
      Self::LdB => write!(f, "ldb"),
      Self::LdBU => write!(f, "ldbu"),
      Self::LdH => write!(f, "ldh"),
      Self::LdHU => write!(f, "ldhu"),
      Self::LdW => write!(f, "ldw"),
      Self::LdWU => write!(f, "ldwu"),
      Self::LdD => write!(f, "ldd"),
      Self::LdP => write!(f, "ldp"),
      Self::LdBO => write!(f, "ldbo"),
      Self::LdBUO => write!(f, "ldbuo"),
      Self::LdHO => write!(f, "ldho"),
      Self::LdHUO => write!(f, "ldhuo"),
      Self::LdWO => write!(f, "ldwo"),
      Self::LdWUO => write!(f, "ldwuo"),
      Self::LdDO => write!(f, "lddo"),
      Self::LdPO => write!(f, "ldpo"),
      Self::LdV => write!(f, "ldv"),
      Self::LdG => write!(f, "ldg"),
      Self::LdC => write!(f, "ldc"),
      Self::LaC => write!(f, "lac"),
      Self::StB => write!(f, "stb"),
      Self::StH => write!(f, "sth"),
      Self::StW => write!(f, "stw"),
      Self::StD => write!(f, "std"),
      Self::StBO => write!(f, "stbo"),
      Self::StHO => write!(f, "stho"),
      Self::StWO => write!(f, "stwo"),
      Self::StDO => write!(f, "stdo"),
      Self::StV => write!(f, "stv"),
      Self::StG => write!(f, "stg"),
      Self::StA => write!(f, "sta"),
      Self::New => write!(f, "new"),
      Self::NewO => write!(f, "newo"),
      Self::NewOC => write!(f, "newoc"),
      Self::NewA => write!(f, "newa"),
      Self::NewAC => write!(f, "newac"),
      Self::Load => write!(f, "load"),
      Self::LoadC => write!(f, "loadc"),
      Self::LoadM => write!(f, "loadm"),
      Self::Bz => write!(f, "bz"),
      Self::Bnz => write!(f, "bnz"),
      Self::Jmp => write!(f, "jmp"),
      Self::Call => write!(f, "call"),
      Self::CallExt => write!(f, "callext"),
      Self::CallExtC => write!(f, "callextc"),
      Self::Ret => write!(f, "ret"),
      Self::Sys => write!(f, "sys"),
      Self::Break => write!(f, "break"),
      Self::Not => write!(f, "not"),
      Self::LNot => write!(f, "lnot"),
      Self::And => write!(f, "and"),
      Self::Or => write!(f, "or"),
      Self::Xor => write!(f, "xor"),
      Self::Shl => write!(f, "shl"),
      Self::Shr => write!(f, "shr"),
      Self::Sar => write!(f, "sar"),
      Self::Sext => write!(f, "sext"),
      Self::Zext => write!(f, "zext"),
      Self::Eq => write!(f, "eq"),
      Self::Ne => write!(f, "ne"),
      Self::Lt => write!(f, "lt"),
      Self::Le => write!(f, "le"),
      Self::Gt => write!(f, "gt"),
      Self::Ge => write!(f, "ge"),
      Self::LtU => write!(f, "ltu"),
      Self::LeU => write!(f, "leu"),
      Self::GtU => write!(f, "gtu"),
      Self::GeU => write!(f, "geu"),
      Self::Neg => write!(f, "neg"),
      Self::Add => write!(f, "add"),
      Self::Sub => write!(f, "sub"),
      Self::Mul => write!(f, "mul"),
      Self::Div => write!(f, "div"),
      Self::DivU => write!(f, "divu"),
      Self::Mod => write!(f, "mod"),
      Self::ModU => write!(f, "modu"),
      Self::LtF => write!(f, "ltf"),
      Self::LeF => write!(f, "lef"),
      Self::GtF => write!(f, "gtf"),
      Self::GeF => write!(f, "gef"),
      Self::NegF => write!(f, "negf"),
      Self::AddF => write!(f, "addf"),
      Self::SubF => write!(f, "subf"),
      Self::MulF => write!(f, "mulf"),
      Self::DivF => write!(f, "divf"),
      Self::ModF => write!(f, "modf"),
      Self::LtD => write!(f, "ltd"),
      Self::LeD => write!(f, "led"),
      Self::GtD => write!(f, "gtd"),
      Self::GeD => write!(f, "ged"),
      Self::NegD => write!(f, "negd"),
      Self::AddD => write!(f, "addd"),
      Self::SubD => write!(f, "subd"),
      Self::MulD => write!(f, "muld"),
      Self::DivD => write!(f, "divd"),
      Self::ModD => write!(f, "modd"),
      Self::I2F => write!(f, "i2f"),
      Self::I2D => write!(f, "i2d"),
      Self::F2I => write!(f, "f2i"),
      Self::F2D => write!(f, "f2d"),
      Self::D2I => write!(f, "d2i"),
      Self::D2F => write!(f, "d2f"),
      Self::ITF => write!(f, "itf"),
      Self::ITD => write!(f, "itd"),
      Self::ITP => write!(f, "itp"),
    }
  }
}

impl str::FromStr for Inst {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s {
      "nop" => Ok(Self::Nop),
      "pushi" => Ok(Self::PushI),
      "pushu" => Ok(Self::PushU),
      "pop" => Ok(Self::Pop),
      "dup" => Ok(Self::Dup),
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
      "bnz" => Ok(Self::Bnz),
      "jmp" => Ok(Self::Jmp),
      "call" => Ok(Self::Call),
      "callext" => Ok(Self::CallExt),
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

/// Type of token.
type Token = laps::token::Token<TokenKind>;

token_ast! {
  #[derive(Debug)]
  macro Token<TokenKind> {
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
    [label] => { kind: TokenKind::Label(_), prompt: "label" },
    [sec] => { kind: TokenKind::Section(_), prompt: "section" },
    [va] => { kind: TokenKind::Variadic },
    [inst] => { kind: TokenKind::Inst(_), prompt: "instruction" },
    [int] => { kind: TokenKind::Int(_), prompt: "integer" },
    [float] => { kind: TokenKind::Float(_), prompt: "floating point" },
    [string] => { kind: TokenKind::Str(_), prompt: "string" },
    [,] => { kind: TokenKind::Other(',') },
  }
}

/// Statement.
#[derive(Debug, Parse)]
#[token(Token)]
enum Statement {
  SectionDecl(SectionDecl),
  Export(Export),
  IntConst(IntConst),
  FloatConst(FloatConst),
  StrConst(StrConst),
  RawConst(RawConst),
  Bytes(Bytes),
  LabelDef(LabelDef),
  Instruction(Instruction),
}

/// Section declaraction.
#[derive(Debug, Parse)]
#[token(Token)]
struct SectionDecl {
  _section: Token![section],
  sec: Token![sec],
}

/// Export information.
#[derive(Debug, Parse)]
#[token(Token)]
struct Export {
  _export: Token![export],
  name: Token![string],
  _comma1: Token![,],
  label: Token![label],
  _comma2: Token![,],
  num_args: NumArgs,
  _comma3: Token![,],
  num_rets: Token![int],
}

/// Number of arguments.
#[derive(Debug, Parse)]
#[token(Token)]
enum NumArgs {
  Variadic(Token![va]),
  Num(Token![int]),
}

/// Integer constant.
#[derive(Debug, Parse)]
#[token(Token)]
struct IntConst {
  kind: IntConstKind,
  value: Token![int],
}

/// Kind of integer constant.
#[derive(Debug, Parse)]
#[token(Token)]
enum IntConstKind {
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
#[derive(Debug, Parse)]
#[token(Token)]
struct FloatConst {
  kind: FloatConstKind,
  value: Token![float],
}

/// Kind of floating point constant.
#[derive(Debug, Parse)]
#[token(Token)]
enum FloatConstKind {
  F32(Token![f32]),
  F64(Token![f64]),
}

/// String constant.
#[derive(Debug, Parse)]
#[token(Token)]
struct StrConst {
  _str: Token![str],
  value: Token![string],
}

/// Raw constant.
#[derive(Debug, Parse)]
#[token(Token)]
struct RawConst {
  _raw: Token![raw],
  values: NonEmptySepSeq<RawValue, Token![,]>,
}

/// Raw constant value.
#[derive(Debug, Parse)]
#[token(Token)]
enum RawValue {
  Str(Token![string]),
  Byte(Token![int]),
}

/// Byte sequence.
#[derive(Debug, Parse)]
#[token(Token)]
struct Bytes {
  _bytes: Token![bytes],
  values: NonEmptySepSeq<RawValue, Token![,]>,
}

/// Label definition.
#[derive(Debug, Parse)]
#[token(Token)]
struct LabelDef {
  label: Token![label],
}

/// Instruction.
#[derive(Debug, Parse)]
#[token(Token)]
struct Instruction {
  inst: Token![inst],
  opr: Option<Token![int]>,
}
