//! Definitions of data structures in constant pool.

/// String constant.
///
/// Starts with an integer that represents the length of bytes,
/// and then a byte array contains UTF-8 encoded string.
pub struct Str<Bytes: Array<u8>> {
  len: u64,
  bytes: Bytes,
}

/// Object metadata.
///
/// With object size and managed pointer information.
pub struct Object<Offsets: Array<u64>> {
  size: u64,
  managed_ptr: ManagedPtr<Offsets>,
}

/// Managed pointer information.
///
/// A list of offsets in 64-bit double words of managed pointers in the object.
pub struct ManagedPtr<Offsets: Array<u64>> {
  len: u64,
  offsets: Offsets,
}

/// Raw data.
///
/// Starts with an integer that represents the data length,
/// and then a byte array contains the data.
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
