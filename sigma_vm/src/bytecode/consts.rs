//! Definitions about constant pool.

use crate::interpreter::heap::Heap;
use crate::utils::{alloc_uninit, impl_try_from_int, Unsized};
use std::alloc::Layout;
use std::ptr::{self, Pointee};
use std::{mem, slice};

/// Constant.
#[derive(Debug, Clone)]
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

  /// Returns the data of the current constant.
  pub fn data(&self) -> &[u8] {
    &self.data
  }

  /// Returns the address of the current constant.
  pub fn addr(&self) -> *const () {
    self.data.as_ptr() as *const ()
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
      let len = Object::<[u64]>::metadata(self.addr()) as usize;
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
    T: ?Sized + Unsized<Metadata = u64> + Pointee<Metadata = usize>,
  {
    if self.kind == kind {
      let len = T::metadata(self.addr()) as usize;
      Some(&*ptr::from_raw_parts(self.addr() as *const _, len))
    } else {
      None
    }
  }

  /// Converts the current constant into a [`HeapConst`].
  pub fn into_heap_const<H>(self, heap: &mut H) -> HeapConst
  where
    H: Heap,
  {
    let size = self.data.len();
    let ptr = heap.alloc(Layout::from_size_align(size, self.kind.align()).unwrap());
    unsafe { ptr::copy_nonoverlapping(self.data.as_ptr(), heap.addr_mut(ptr) as *mut u8, size) };
    HeapConst {
      kind: self.kind,
      ptr,
    }
  }
}

/// Constant that allocated on VM managed heap.
///
/// # Notes
///
/// Allocated heap memory is not freed when dropping [`HeapConst`],
/// so it's necessary to handle this manually.
#[derive(Debug)]
pub struct HeapConst {
  kind: ConstKind,
  ptr: u64,
}

impl HeapConst {
  /// Returns the kind of the current constant.
  pub fn kind(&self) -> ConstKind {
    self.kind
  }

  /// Returns the heap pointer of the current constant.
  pub fn ptr(&self) -> u64 {
    self.ptr
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
        let size = mem::size_of_val(&value);
        let mut data = unsafe { alloc_uninit(size, mem::align_of_val(&value), ()) }.unwrap();
        *data = value;
        unsafe { Self::new(ConstKind::$kind, data, size) }
      }
    }
  };
  ($ty:ty, $kind:ident) => {
    impl From<$ty> for Const {
      fn from(value: $ty) -> Self {
        let size = mem::size_of_val(&value);
        let mut data = unsafe { alloc_uninit(size, mem::align_of_val(&value), ()) }.unwrap();
        *data = value;
        unsafe { Self::new(ConstKind::$kind, data, size) }
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

    impl_try_from_int! {
      impl TryFrom<u8> for ConstKind {
        $($kind),+
      }
    }
  };
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

impl ConstKind {
  /// Returns the alignment of the current kind.
  pub fn align(&self) -> usize {
    match self {
      Self::I8 => mem::align_of::<i8>(),
      Self::U8 => mem::align_of::<u8>(),
      Self::I16 => mem::align_of::<i16>(),
      Self::U16 => mem::align_of::<u16>(),
      Self::I32 => mem::align_of::<i32>(),
      Self::U32 => mem::align_of::<u32>(),
      Self::I64 => mem::align_of::<i64>(),
      Self::U64 => mem::align_of::<u64>(),
      Self::F32 => mem::align_of::<f32>(),
      Self::F64 => mem::align_of::<f64>(),
      Self::Str => mem::align_of::<Str<[u8; 0]>>(),
      Self::Object => mem::align_of::<Object<[u64; 0]>>(),
      Self::Raw => mem::align_of::<Raw<[u8; 0]>>(),
    }
  }
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

impl Str<[u8]> {
  /// Converts the current string constant to a <code>&[str]</code>.
  /// Returns [`None`] if it's not a valid UTF-8 string.
  pub fn to_str(&self) -> Option<&str> {
    std::str::from_utf8(&self.bytes).ok()
  }
}

impl<Bytes: ?Sized + Array<u8>> Unsized for Str<Bytes> {
  const SIZE: usize = mem::size_of::<u64>();
  const ALIGN: usize = mem::align_of::<u64>();
  type Metadata = u64;
  const METADATA_OFFSET: usize = 0;

  fn size(metadata: Self::Metadata) -> usize {
    Self::SIZE + metadata as usize * mem::size_of::<u8>()
  }
}

/// Object metadata.
///
/// With object size, align, destructor's PC (zero means no destructor)
/// and managed pointer information.
#[repr(C)]
#[derive(Debug)]
pub struct Object<Offsets: ?Sized + Array<u64>> {
  pub size: u64,
  pub align: u64,
  pub destructor: u64,
  pub managed_ptr: ManagedPtr<Offsets>,
}

impl<Offsets: ?Sized + Array<u64>> Object<Offsets> {
  /// Returns aligned size.
  pub fn aligned_size(&self) -> u64 {
    assert!(self.align.is_power_of_two(), "invalid alignment");
    let len = self.size;
    let align = self.align;
    let len_rounded_up = len.wrapping_add(align).wrapping_sub(1) & !align.wrapping_sub(1);
    len + len_rounded_up.wrapping_sub(len)
  }
}

impl<Offsets: ?Sized + Array<u64>> Unsized for Object<Offsets> {
  const SIZE: usize = mem::size_of::<u64>() * 3 + ManagedPtr::<Offsets>::SIZE;
  const ALIGN: usize = mem::align_of::<u64>();
  type Metadata = <ManagedPtr<Offsets> as Unsized>::Metadata;
  const METADATA_OFFSET: usize = mem::size_of::<u64>() * 3 + ManagedPtr::<Offsets>::METADATA_OFFSET;

  fn size(metadata: Self::Metadata) -> usize {
    mem::size_of::<u64>() * 3 + ManagedPtr::<Offsets>::size(metadata)
  }
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

impl<Offsets: ?Sized + Array<u64>> Unsized for ManagedPtr<Offsets> {
  const SIZE: usize = mem::size_of::<u64>();
  const ALIGN: usize = mem::align_of::<u64>();
  type Metadata = u64;
  const METADATA_OFFSET: usize = 0;

  fn size(metadata: Self::Metadata) -> usize {
    Self::SIZE + metadata as usize * mem::size_of::<u64>()
  }
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

impl<Bytes: ?Sized + Array<u8>> Unsized for Raw<Bytes> {
  const SIZE: usize = mem::size_of::<u64>();
  const ALIGN: usize = mem::align_of::<u64>();
  type Metadata = u64;
  const METADATA_OFFSET: usize = 0;

  fn size(metadata: Self::Metadata) -> usize {
    Self::SIZE + metadata as usize * mem::size_of::<u8>()
  }
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
