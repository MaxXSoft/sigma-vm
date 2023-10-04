use laps::prelude::*;

/// Kind of token.
enum TokenKind {
  _Skip,
  Int(Int),
  Float(Float),
  Char(char),
  Byte(u8),
  Str(Str),
  RawStr(RawStr),
  Bytes(Bytes),
  Ident(String),
  Eof,
}

/// Integer literal.
enum Int {
  I8(i8),
  I16(i16),
  I32(i32),
  I64(i64),
  U8(u8),
  U16(u16),
  U32(u32),
  U64(u64),
  Untyped(u64),
}

/// Floating-point literal.
enum Float {
  F32(f32),
  F64(f64),
}

/// String literal.
struct Str {
  value: String,
}

/// Raw string literal.
struct RawStr {
  value: String,
}

/// Bytes literal.
struct Bytes {
  value: Vec<u8>,
}
