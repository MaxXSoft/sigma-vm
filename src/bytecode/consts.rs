//! Definitions of data structures in constant pool.

/// String constant.
///
/// Starts with an integer that represents the length of bytes,
/// and then a byte array contains UTF-8 encoded string.
pub struct Str {
  len: u64,
  bytes: [u8],
}

/// Object metadata.
///
/// With object size and managed pointer information.
pub struct Object {
  size: u64,
  managed_ptr: ManagedPtr,
}

/// Managed pointer information.
///
/// A list of offsets in 64-bit double words of managed pointers in the object.
pub struct ManagedPtr {
  len: u64,
  offsets: [u64],
}
