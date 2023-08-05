//! Definitions about constant pool.

use std::ptr::{self, Pointee};
use std::{mem, slice};

/// Constant.
#[derive(Debug)]
pub struct Const {
  kind: ConstKind,
  data: Box<[u8]>,
}

impl Const {
  /// Creates a new constant with the given data and the size of the data.
  ///
  /// # Safety
  ///
  /// The kind must match the data.
  pub unsafe fn new<T>(kind: ConstKind, data: Box<T>, size: usize) -> Self
  where
    T: ?Sized,
  {
    let data = Box::from_raw(slice::from_raw_parts_mut(
      Box::leak(data) as *mut _ as *mut u8,
      size,
    ));
    Self { kind, data }
  }

  /// Returns the kind of the current constant.
  pub fn kind(&self) -> ConstKind {
    self.kind
  }

  /// Sets the kind of the current constant.
  ///
  /// # Safety
  ///
  /// The kind must match the data.
  pub unsafe fn set_kind(&mut self, kind: ConstKind) {
    self.kind = kind;
  }

  /// Returns the address of the current constant.
  pub fn addr(&self) -> *const () {
    self.data.as_ptr() as *const ()
  }

  /// Returns the address of the current constant as [`u64`].
  pub fn addr_u64(&self) -> u64 {
    let addr = self.addr();
    assert_eq!(mem::size_of_val(&addr), mem::size_of::<u64>());
    addr as u64
  }

  /// Returns the value of the current constant,
  /// or [`None`] if value is unavailable.
  ///
  /// # Safety
  ///
  /// The kind must match the data.
  pub unsafe fn value<T>(&self) -> Option<T>
  where
    T: FromConst,
  {
    T::from(self)
  }

  /// Returns the value of the current constant as [`u64`],
  /// or [`None`] if value is unavailable.
  ///
  /// # Safety
  ///
  /// The kind must match the data.
  pub unsafe fn value_u64(&self) -> Option<u64> {
    macro_rules! value {
      ($($kind:ident => $ty:ty),* $(,)?) => {
        match self.kind {
          $(ConstKind::$kind => Some(*(self.addr() as *const $ty) as u64),)*
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

  /// Returns a reference of string constant, or [`None`] if
  /// the current constant is not a string constant.
  ///
  /// # Safety
  ///
  /// The kind must match the data.
  pub unsafe fn str(&self) -> Option<&Str<[u8]>> {
    self.bytes(ConstKind::Str)
  }

  /// Returns a reference of object metadata, or [`None`] if
  /// the current constant is not an object metadata.
  ///
  /// # Safety
  ///
  /// The kind must match the data.
  pub unsafe fn object(&self) -> Option<&Object<[u64]>> {
    if self.kind == ConstKind::Object {
      let len = *(self.addr() as *const u64).offset(1) as usize;
      Some(&*ptr::from_raw_parts(self.addr() as *const _, len))
    } else {
      None
    }
  }

  /// Returns a reference of raw data, or [`None`] if
  /// the current constant is not a raw data.
  ///
  /// # Safety
  ///
  /// The kind must match the data.
  pub unsafe fn raw(&self) -> Option<&Raw<[u8]>> {
    self.bytes(ConstKind::Raw)
  }

  /// Returns a reference of byte sequence (string constant or raw data),
  /// or [`None`] if the current constant is not a byte sequence.
  ///
  /// # Safety
  ///
  /// The kind must match the data.
  unsafe fn bytes<T>(&self, kind: ConstKind) -> Option<&T>
  where
    T: ?Sized + Pointee<Metadata = usize>,
  {
    if self.kind == kind {
      let len = *(self.addr() as *const u64) as usize;
      Some(&*ptr::from_raw_parts(self.addr() as *const _, len))
    } else {
      None
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
impl_from!(Object<Offsets: Array<u64>>, Object);
impl_from!(Raw<Bytes: Array<u8>>, Raw);

/// Trait for constructing values from constant.
pub trait FromConst: Sized {
  /// Constructs a value from the given constant.
  ///
  /// # Safety
  ///
  /// The kind of the constant must match the inner data.
  unsafe fn from(_: &Const) -> Option<Self>;
}

/// Helper macro for implementing [`FromConst`] for the given type.
macro_rules! impl_from_const {
  ($ty:ty, $kind:ident) => {
    impl FromConst for $ty {
      unsafe fn from(c: &Const) -> Option<Self> {
        (c.kind() == ConstKind::$kind).then(|| *(c.addr() as *const Self))
      }
    }
  };
}

impl_from_const!(i8, I8);
impl_from_const!(u8, U8);
impl_from_const!(i16, I16);
impl_from_const!(u16, U16);
impl_from_const!(i32, I32);
impl_from_const!(u32, U32);
impl_from_const!(i64, I64);
impl_from_const!(u64, U64);
impl_from_const!(f32, F32);
impl_from_const!(f64, F64);

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
  Object,
  /// Raw data.
  Raw,
}

/// String constant.
///
/// Starts with an integer that represents the length of bytes,
/// and then a byte array contains UTF-8 encoded string.
#[repr(C)]
#[derive(Debug)]
pub struct Str<Bytes: ?Sized + Array<u8>> {
  pub len: u64,
  pub bytes: Bytes,
}

/// Object metadata.
///
/// With object size and managed pointer information.
#[repr(C)]
#[derive(Debug)]
pub struct Object<Offsets: ?Sized + Array<u64>> {
  pub size: u64,
  pub managed_ptr: ManagedPtr<Offsets>,
}

/// Managed pointer information.
///
/// A list of offsets in 64-bit double words of managed pointers in the object.
#[repr(C)]
#[derive(Debug)]
pub struct ManagedPtr<Offsets: ?Sized + Array<u64>> {
  pub len: u64,
  pub offsets: Offsets,
}

/// Raw data.
///
/// Starts with an integer that represents the data length,
/// and then a byte array contains the data.
#[repr(C)]
#[derive(Debug)]
pub struct Raw<Bytes: ?Sized + Array<u8>> {
  pub len: u64,
  pub bytes: Bytes,
}

/// Marker trait for arrays (`[T; N]` and `[T]`).
pub trait Array<T>: array::Array<T> {}
impl<T, const N: usize> Array<T> for [T; N] {}
impl<T> Array<T> for [T] {}

mod array {
  pub trait Array<T> {}
  impl<T, const N: usize> Array<T> for [T; N] {}
  impl<T> Array<T> for [T] {}
}
