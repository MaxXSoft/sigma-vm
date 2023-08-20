use laps::prelude::*;
use std::{fmt, str};

#[token_kind]
#[derive(Debug, Tokenize)]
enum TokenKind {
  /// Spaces and comments.
  #[skip(r"\s+|#.*\n|#.*")]
  _Skip,
  /// Directive.
  #[regex(r"\.[a-z]+")]
  Directive(Directive),
  /// Instruction.
  #[regex(r"a")]
  Inst(String),
}

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
