//! Definitions about constant pool.

use std::{mem, slice};

/// Constant.
#[derive(Debug)]
pub struct Const {
  kind: ConstKind,
  data: Box<[u8]>,
}

impl Const {
  /// Returns the address of the current constant.
  pub fn addr(&self) -> u64 {
    self.data.as_ptr() as u64
  }

  /// Returns the value of the current constant as an integer,
  /// or [`None`] if value is unavailable.
  ///
  /// # Safety
  ///
  /// The kind matches the data.
  pub unsafe fn value(&self) -> Option<u64> {
    macro_rules! value {
      ($($kind:ident => $ty:ty),* $(,)?) => {
        match self.kind {
          $(ConstKind::$kind => Some(*(self.data.as_ptr() as *const $ty) as u64),)*
          _ => None,
        }
      };
    }
    value! {
      I8 => i8,
      U8 => u8,
      I16 => i16,
      U16 => u16,
      I32 => i32,
      U32 => u32,
      I64 => i64,
      U64 => u64,
      F32 => u32,
      F64 => u64,
    }
  }
}

/// Helper macro for implementing [`From<T>`] for [`Const`].
macro_rules! impl_from {
  ($ty:ident<$g:ident: $b:path>, $kind:ident) => {
    impl<$g> From<$ty<$g>> for Const
    where
      $g: $b,
    {
      fn from(value: $ty<$g>) -> Self {
        Self {
          kind: ConstKind::$kind,
          data: Box::from(unsafe {
            slice::from_raw_parts(&value as *const _ as *const u8, mem::size_of_val(&value))
          }),
        }
      }
    }
  };
  ($ty:ty, $kind:ident) => {
    impl From<$ty> for Const {
      fn from(value: $ty) -> Self {
        Self {
          kind: ConstKind::$kind,
          data: Box::from(unsafe {
            slice::from_raw_parts(&value as *const _ as *const u8, mem::size_of_val(&value))
          }),
        }
      }
    }
  };
}

impl_from!(i8, I8);
impl_from!(u8, U8);
impl_from!(i16, I16);
impl_from!(u16, U16);
impl_from!(i32, I32);
impl_from!(u32, U32);
impl_from!(i64, I64);
impl_from!(u64, U64);
impl_from!(f32, F32);
impl_from!(f64, F64);
impl_from!(Str<Bytes: Array<u8>>, Str);
impl_from!(Object<Offsets: Array<u64>>, Obj);
impl_from!(Raw<Bytes: Array<u8>>, Raw);

/// Helper macro for defining kind of constant.
macro_rules! const_kind {
  ($($(#[$a:meta])* $kind:ident),+ $(,)?) => {
    /// Kind of constant.
    #[repr(u8)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum ConstKind {
      $($(#[$a])* $kind),+
    }

    impl ConstKind {
      /// Creates a new [`ConstKind`] from the given byte.
      pub fn from_byte(b: u8) -> Option<Self> {
        let mut k = 0;
        const_kind!(@arm b, k $(,$kind)+)
      }
    }
  };
  (@arm $b:ident, $k:ident, $kind:ident $(,$kinds:ident)+) => {{
    if $b == $k { return Some(Self::$kind) }
    $k += 1;
    const_kind!(@arm $b, $k $(,$kinds)+)
  }};
  (@arm $b:ident, $k:ident, $kind:ident) => {{
    if $b == $k { return Some(Self::$kind) }
    None
  }};
}

const_kind! {
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
#[repr(C)]
#[derive(Debug)]
pub struct Str<Bytes: Array<u8>> {
  len: u64,
  bytes: Bytes,
}

/// Object metadata.
///
/// With object size and managed pointer information.
#[repr(C)]
#[derive(Debug)]
pub struct Object<Offsets: Array<u64>> {
  size: u64,
  managed_ptr: ManagedPtr<Offsets>,
}

/// Managed pointer information.
///
/// A list of offsets in 64-bit double words of managed pointers in the object.
#[repr(C)]
#[derive(Debug)]
pub struct ManagedPtr<Offsets: Array<u64>> {
  len: u64,
  offsets: Offsets,
}

/// Raw data.
///
/// Starts with an integer that represents the data length,
/// and then a byte array contains the data.
#[repr(C)]
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
