//! Definitions about constant pool.

/// Constant.
#[derive(Debug)]
pub struct Const {
  kind: ConstKind,
  data: Box<[u8]>,
}

/// Kind of constant.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstKind {
  /// Signed 8-bit integer.
  I8,
  /// Unsigned 8-bit integer.
  U8,
  /// Signed 16-bit integer.
  I16,
  /// Unsigned 16-bit integer.
  U16,
  /// Signed 32-bit integer.
  I32,
  /// Unsigned 32-bit integer.
  U32,
  /// Signed 64-bit integer.
  I64,
  /// Unsigned 64-bit integer.
  U64,
  /// 32-bit floating point.
  F32,
  /// 64-bit floating point.
  F64,
  /// String.
  Str,
  /// Object metadata.
  Obj,
  /// Raw data.
  Raw,
}

/// String constant.
///
/// Starts with an integer that represents the length of bytes,
/// and then a byte array contains UTF-8 encoded string.
#[derive(Debug)]
pub struct Str<Bytes: Array<u8>> {
  len: u64,
  bytes: Bytes,
}

/// Object metadata.
///
/// With object size and managed pointer information.
#[derive(Debug)]
pub struct Object<Offsets: Array<u64>> {
  size: u64,
  managed_ptr: ManagedPtr<Offsets>,
}

/// Managed pointer information.
///
/// A list of offsets in 64-bit double words of managed pointers in the object.
#[derive(Debug)]
pub struct ManagedPtr<Offsets: Array<u64>> {
  len: u64,
  offsets: Offsets,
}

/// Raw data.
///
/// Starts with an integer that represents the data length,
/// and then a byte array contains the data.
#[derive(Debug)]
pub struct Raw<Bytes: Array<u8>> {
  len: u64,
  bytes: Bytes,
}

/// Marker trait for arrays (`[T; N]` and `[T]`).
pub trait Array<T>: array::Array<T> {}

mod array {
  pub trait Array<T> {}
  impl<T, const N: usize> Array<T> for [T; N] {}
  impl<T> Array<T> for [T] {}
}
