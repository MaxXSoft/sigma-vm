use laps::lexer::{char_literal, str_literal};
use laps::prelude::*;
use std::{fmt, num, str};

/// Type of token.
pub type Token = laps::token::Token<TokenKind>;

/// Kind of token.
#[token_kind]
#[derive(Debug, Tokenize)]
pub enum TokenKind {
  /// Whitespaces.
  #[skip(r"\s+")]
  _Skip,
  /// Integer literal.
  #[regex(r"(0b[01]+|0o[0-7]+|0x[0-9a-fA-F]+|[0-9]+)([iIuU](8|16|32|64))?")]
  Int(Int),
  /// Floating-point literal.
  #[regex(r"[0-9]+(\.([0-9]+([eE][+-]?[0-9]+)?([fF](32|64))?)?|([eE][+-]?[0-9]+)([fF](32|64))?|([fF](32|64)))")]
  Float(Float),
  /// Character literal.
  #[regex(
    r#"'([^'\\\n\r\t]|\\'|\\"|\\x[0-7][0-9a-fA-F]|\\n|\\r|\\t|\\\\|\\0|\\u\{[0-9a-fA-F]{1,6}\})'"#,
    char_literal
  )]
  Char(char),
  /// Byte literal.
  #[regex(
    r#"b'([\x20-\x26\x28-\x5b\x5d-\x7e]|\\x[0-9a-fA-F]{2}|\\n|\\r|\\t|\\\\|\\0|\\'|\\")'"#,
    parse_byte
  )]
  Byte(u8),
  /// String literal.
  #[regex(
    r#""([^'\\\n\r\t]|\\'|\\"|\\x[0-7][0-9a-fA-F]|\\n|\\r|\\t|\\\\|\\0|\\u\{[0-9a-fA-F]{1,6}\})*""#
  )]
  Str(Str),
  /// Raw string literal.
  #[regex(r####"r"[^"]*"|r#"([^"]|"[^#])*"#|r##"([^"]|"[^#]|"#[^#])*"##|r###"([^"]|"[^#]|"#[^#]|"##[^#])*"###"####)]
  RawStr(RawStr),
  /// Bytes literal.
  #[regex(r#"b"([\x20-\x26\x28-\x5b\x5d-\x7e]|\\x[0-9a-fA-F]{2}|\\n|\\r|\\t|\\\\|\\0|\\'|\\")*""#)]
  Bytes(Bytes),
  /// Pre-defined operator-like identifiers.
  #[regex(r"\+|-|\*|/|%|&|\||!|\^|<<|>>|&&|\|\||==|!=|<|<=|>|>=|=|\+=|-=|\*=|/=|%=|&=|\|=|\^=|<<=|>>=|\(|\)|\[|\]|\{|\}|\.|\.\.|\.\.\.|->|,|:|@|_|\?|;")]
  PreDefOp(PreDefOp),
  /// Other operator-like identifiers.
  #[regex(r"[~!@#$%^&*()_\-+={}\[\]|\\:;<,>.?/]+")]
  Op(Op),
  /// Other identifiers.
  #[regex(r#"[^\s~!@#$%^&*()_\-+={}\[\]|\\:;<,>.?/0-9][^\s~!@#$%^&*()\-+={}\[\]|\\:;<,>.?/]*"#)]
  Ident(String),
  /// End-of-file.
  #[eof]
  Eof,
}

/// Integer literal.
#[derive(Debug, Clone, PartialEq)]
pub enum Int {
  /// 8-bit signed integer.
  I8(i8),
  /// 16-bit signed integer.
  I16(i16),
  /// 32-bit signed integer.
  I32(i32),
  /// 64-bit signed integer.
  I64(i64),
  /// 8-bit unsigned integer.
  U8(u8),
  /// 16-bit unsigned integer.
  U16(u16),
  /// 32-bit unsigned integer.
  U32(u32),
  /// 64-bit unsigned integer.
  U64(u64),
  /// Untyped integer.
  Untyped(u64),
}

impl fmt::Display for Int {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::I8(i) => write!(f, "{i}i8"),
      Self::I16(i) => write!(f, "{i}i16"),
      Self::I32(i) => write!(f, "{i}i32"),
      Self::I64(i) => write!(f, "{i}i64"),
      Self::U8(i) => write!(f, "{i}u8"),
      Self::U16(i) => write!(f, "{i}u16"),
      Self::U32(i) => write!(f, "{i}u32"),
      Self::U64(i) => write!(f, "{i}u64"),
      Self::Untyped(i) => write!(f, "{i}"),
    }
  }
}

impl str::FromStr for Int {
  type Err = num::ParseIntError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let (radix, s) = match s.find(['b', 'o', 'x']) {
      Some(i) => {
        let radix = match &s[..i + 1] {
          "0b" => 2,
          "0o" => 8,
          "0x" => 16,
          _ => unreachable!(),
        };
        (radix, &s[i + 1..])
      }
      None => (10, s),
    };
    let (digits, suffix) = match s.find(['i', 'u']) {
      Some(i) => (&s[..i], Some(&s[i..])),
      None => (s, None),
    };
    match suffix {
      Some("i8") => i8::from_str_radix(digits, radix).map(Self::I8),
      Some("i16") => i16::from_str_radix(digits, radix).map(Self::I16),
      Some("i32") => i32::from_str_radix(digits, radix).map(Self::I32),
      Some("i64") => i64::from_str_radix(digits, radix).map(Self::I64),
      Some("u8") => u8::from_str_radix(digits, radix).map(Self::U8),
      Some("u16") => u16::from_str_radix(digits, radix).map(Self::U16),
      Some("u32") => u32::from_str_radix(digits, radix).map(Self::U32),
      Some("u64") => u64::from_str_radix(digits, radix).map(Self::U64),
      None => u64::from_str_radix(digits, radix).map(Self::Untyped),
      _ => unreachable!(),
    }
  }
}

/// Floating-point literal.
#[derive(Debug, Clone, PartialEq)]
pub enum Float {
  F32(f32),
  F64(f64),
  Untyped(f64),
}

impl fmt::Display for Float {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::F32(v) => write!(f, "{v}f32"),
      Self::F64(v) => write!(f, "{v}f64"),
      Self::Untyped(v) => write!(f, "{v}"),
    }
  }
}

impl str::FromStr for Float {
  type Err = num::ParseFloatError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let (digits, suffix) = match s.find('f') {
      Some(i) => (&s[..i], Some(&s[i..])),
      None => (s, None),
    };
    match suffix {
      Some("f32") => digits.parse().map(Self::F32),
      Some("f64") => digits.parse().map(Self::F64),
      None => digits.parse().map(Self::Untyped),
      _ => unreachable!(),
    }
  }
}

/// Parses a byte literal from the given string.
fn parse_byte(s: &str) -> Option<u8> {
  char_literal(&s[1..]).map(|c| c as u8)
}

/// String literal.
#[derive(Debug, Clone, PartialEq)]
pub struct Str(pub String);

impl fmt::Display for Str {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{:?}", self.0)
  }
}

impl str::FromStr for Str {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    str_literal(s).map(Self).ok_or(())
  }
}

/// Raw string literal.
#[derive(Debug, Clone, PartialEq)]
pub struct RawStr(pub String);

impl fmt::Display for RawStr {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{:?}", self.0)
  }
}

impl str::FromStr for RawStr {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    str_literal(&s[s.find('"').unwrap()..=s.rfind('"').unwrap()])
      .map(Self)
      .ok_or(())
  }
}

/// Bytes literal.
#[derive(Debug, Clone, PartialEq)]
pub struct Bytes(pub Vec<u8>);

impl fmt::Display for Bytes {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{:?}", self.0)
  }
}

impl str::FromStr for Bytes {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    str_literal(&s[1..]).map(|s| Self(s.into_bytes())).ok_or(())
  }
}

/// Pre-defined operator.
#[derive(Debug, Clone, PartialEq)]
pub enum PreDefOp {
  /// +
  Add,
  /// -
  Sub,
  /// *
  Mul,
  /// /
  Div,
  /// %
  Mod,
  /// &
  And,
  /// |
  Or,
  /// !
  Not,
  /// ^
  Xor,
  /// <<
  Shl,
  /// >>
  Shr,
  /// &&
  LogicAnd,
  /// ||
  LogicOr,
  /// ==
  Eq,
  /// !=
  Ne,
  /// <
  Lt,
  /// <=
  Le,
  /// >
  Gt,
  /// >=
  Ge,
  /// =
  Assign,
  /// +=
  AddAssign,
  /// -=
  SubAssign,
  /// *=
  MulAssign,
  /// /=
  DivAssign,
  /// %=
  ModAssign,
  /// &=
  AndAssign,
  /// |=
  OrAssign,
  /// ^=
  XorAssign,
  /// <<=
  ShlAssign,
  /// >>=
  ShrAssign,
  /// (
  LeftParen,
  /// )
  RightParen,
  /// [
  LeftBracket,
  /// ]
  RightBracket,
  /// {
  LeftBrace,
  /// }
  RightBrace,
  /// .
  Dot,
  /// ..
  AnyPat,
  /// ...
  Repeat,
  /// ->
  Arrow,
  /// ,
  Comma,
  /// :
  Colon,
  /// @
  At,
  /// _
  Underscore,
  /// ?
  Question,
  /// ;
  Semicolon,
}

impl fmt::Display for PreDefOp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Add => write!(f, "+"),
      Self::Sub => write!(f, "-"),
      Self::Mul => write!(f, "*"),
      Self::Div => write!(f, "/"),
      Self::Mod => write!(f, "%"),
      Self::And => write!(f, "&"),
      Self::Or => write!(f, "|"),
      Self::Not => write!(f, "!"),
      Self::Xor => write!(f, "^"),
      Self::Shl => write!(f, "<<"),
      Self::Shr => write!(f, ">>"),
      Self::LogicAnd => write!(f, "&&"),
      Self::LogicOr => write!(f, "||"),
      Self::Eq => write!(f, "=="),
      Self::Ne => write!(f, "!="),
      Self::Lt => write!(f, "<"),
      Self::Le => write!(f, "<="),
      Self::Gt => write!(f, ">"),
      Self::Ge => write!(f, ">="),
      Self::Assign => write!(f, "="),
      Self::AddAssign => write!(f, "+="),
      Self::SubAssign => write!(f, "-="),
      Self::MulAssign => write!(f, "*="),
      Self::DivAssign => write!(f, "/="),
      Self::ModAssign => write!(f, "%="),
      Self::AndAssign => write!(f, "&="),
      Self::OrAssign => write!(f, "|="),
      Self::XorAssign => write!(f, "^="),
      Self::ShlAssign => write!(f, "<<="),
      Self::ShrAssign => write!(f, ">>="),
      Self::LeftParen => write!(f, "("),
      Self::RightParen => write!(f, ")"),
      Self::LeftBracket => write!(f, "["),
      Self::RightBracket => write!(f, "]"),
      Self::LeftBrace => write!(f, "{{"),
      Self::RightBrace => write!(f, "}}"),
      Self::Dot => write!(f, "."),
      Self::AnyPat => write!(f, ".."),
      Self::Repeat => write!(f, "..."),
      Self::Arrow => write!(f, "->"),
      Self::Comma => write!(f, ","),
      Self::Colon => write!(f, ":"),
      Self::At => write!(f, "@"),
      Self::Underscore => write!(f, "_"),
      Self::Question => write!(f, "?"),
      Self::Semicolon => write!(f, ";"),
    }
  }
}

impl str::FromStr for PreDefOp {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s {
      "+" => Ok(Self::Add),
      "-" => Ok(Self::Sub),
      "*" => Ok(Self::Mul),
      "/" => Ok(Self::Div),
      "%" => Ok(Self::Mod),
      "&" => Ok(Self::And),
      "|" => Ok(Self::Or),
      "!" => Ok(Self::Not),
      "^" => Ok(Self::Xor),
      "<<" => Ok(Self::Shl),
      ">>" => Ok(Self::Shr),
      "&&" => Ok(Self::LogicAnd),
      "||" => Ok(Self::LogicOr),
      "==" => Ok(Self::Eq),
      "!=" => Ok(Self::Ne),
      "<" => Ok(Self::Lt),
      "<=" => Ok(Self::Le),
      ">" => Ok(Self::Gt),
      ">=" => Ok(Self::Ge),
      "=" => Ok(Self::Assign),
      "+=" => Ok(Self::AddAssign),
      "-=" => Ok(Self::SubAssign),
      "*=" => Ok(Self::MulAssign),
      "/=" => Ok(Self::DivAssign),
      "%=" => Ok(Self::ModAssign),
      "&=" => Ok(Self::AndAssign),
      "|=" => Ok(Self::OrAssign),
      "^=" => Ok(Self::XorAssign),
      "<<=" => Ok(Self::ShlAssign),
      ">>=" => Ok(Self::ShrAssign),
      "(" => Ok(Self::LeftParen),
      ")" => Ok(Self::RightParen),
      "[" => Ok(Self::LeftBracket),
      "]" => Ok(Self::RightBracket),
      "{{" => Ok(Self::LeftBrace),
      "}}" => Ok(Self::RightBrace),
      "." => Ok(Self::Dot),
      ".." => Ok(Self::AnyPat),
      "..." => Ok(Self::Repeat),
      "->" => Ok(Self::Arrow),
      "," => Ok(Self::Comma),
      ":" => Ok(Self::Colon),
      "@" => Ok(Self::At),
      "_" => Ok(Self::Underscore),
      "?" => Ok(Self::Question),
      ";" => Ok(Self::Semicolon),
      _ => unreachable!(),
    }
  }
}

/// Operator-like identifier.
#[derive(Debug, Clone, PartialEq)]
pub struct Op(pub String);

impl fmt::Display for Op {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.0)
  }
}

impl str::FromStr for Op {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    Ok(Self(s.into()))
  }
}
