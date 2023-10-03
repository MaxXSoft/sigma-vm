use crate::bytecode::consts::{ConstKind, HeapConst, Object, Str};
use crate::interpreter::gc::GarbageCollector;
use crate::interpreter::heap::{CheckedHeap, Heap, Ptr};
use crate::utils::Unsized;
use std::alloc::Layout;
use std::marker::PhantomData;
use std::{fmt, ptr};

/// Execution policy of the VM (interpreter).
pub trait Policy {
  /// Type of all local/global values.
  type Value;

  /// Type of error.
  type Error;

  /// Type of managed heap.
  type Heap: Heap;

  /// Type of garbage collector.
  type GarbageCollector: GarbageCollector;

  /// Creates an integer value.
  fn int_val(i: u64) -> Self::Value;

  /// Creates a 32-bit floating point value.
  fn f32_val(f: f32) -> Self::Value;

  /// Creates a 64-bit floating point value.
  fn f64_val(f: f64) -> Self::Value;

  /// Creates pointer value.
  fn ptr_val(p: Ptr) -> Self::Value;

  /// Extracts an integer value from the given value.
  ///
  /// Pointer values will be treat as integers.
  fn get_int_ptr(v: &Self::Value) -> Result<u64, Self::Error>;

  /// Extracts a 32-bit floating point value from the given value.
  fn get_f32(v: &Self::Value) -> Result<f32, Self::Error>;

  /// Extracts a 64-bit floating point value from the given value.
  fn get_f64(v: &Self::Value) -> Result<f64, Self::Error>;

  /// Extracts a pointer value from the given value.
  fn get_ptr(v: &Self::Value) -> Result<Ptr, Self::Error>;

  /// Extracts a 64-bit untyped value from the given value.
  fn get_any(v: &Self::Value) -> u64;

  /// Returns the pointer value if the given value is a pointer,
  /// otherwise [`None`].
  fn ptr_or_none(v: &Self::Value) -> Option<Ptr>;

  /// Returns a string pointer from the given heap constant,
  /// returns an error if necessary.
  fn str_ptr_from_const(c: &HeapConst) -> Result<Ptr, Self::Error>;

  /// Returns an object metadata pointer from the given heap constant,
  /// returns an error if necessary.
  fn obj_ptr_from_const(c: &HeapConst) -> Result<Ptr, Self::Error>;

  /// Unwraps an [`Option<Value>`],
  /// returns the given error message if necessary.
  fn unwrap<V>(v: Option<V>, e: &'static str) -> Result<V, Self::Error> {
    Self::unwrap_or(v, || e)
  }

  /// Unwraps an [`Option<Value>`],
  /// returns the given error message if necessary.
  fn unwrap_or<V, F, S>(v: Option<V>, f: F) -> Result<V, Self::Error>
  where
    F: FnOnce() -> S,
    S: Into<String>;

  /// Checks the given integer divisor, returns an error if necessary.
  fn check_div(divisor: u64) -> Result<(), Self::Error>;

  /// Reports a error with the given error message.
  fn report_err<S>(e: S) -> Result<(), Self::Error>
  where
    S: Into<String>;

  /// Creates a new heap.
  fn new_heap(&self) -> Self::Heap;

  /// Checks whether the given memory access is valid,
  /// returns an error if necessary.
  fn check_access(heap: &Self::Heap, p: Ptr, len: usize, align: usize) -> Result<(), Self::Error>;

  /// Creates a value from a heap constant.
  fn val_from_const(heap: &Self::Heap, c: &HeapConst) -> Self::Value {
    // do not check for constant's pointer since it's always valid
    let addr = heap.addr(c.ptr());
    match c.kind() {
      ConstKind::I8 => Self::int_val(unsafe { *(addr as *const i8) } as u64),
      ConstKind::U8 => Self::int_val(unsafe { *(addr as *const u8) } as u64),
      ConstKind::I16 => Self::int_val(unsafe { *(addr as *const i16) } as u64),
      ConstKind::U16 => Self::int_val(unsafe { *(addr as *const u16) } as u64),
      ConstKind::I32 => Self::int_val(unsafe { *(addr as *const i32) } as u64),
      ConstKind::U32 => Self::int_val(unsafe { *(addr as *const u32) } as u64),
      ConstKind::I64 => Self::int_val(unsafe { *(addr as *const i64) } as u64),
      ConstKind::U64 => Self::int_val(unsafe { *(addr as *const u64) }),
      ConstKind::F32 => Self::f32_val(unsafe { *(addr as *const f32) }),
      ConstKind::F64 => Self::f64_val(unsafe { *(addr as *const f64) }),
      _ => Self::ptr_val(c.ptr()),
    }
  }

  /// Returns a reference of string by the given pointer.
  fn str(heap: &Self::Heap, ptr: Ptr) -> Result<&Str<[u8]>, Self::Error> {
    type S = Str<[u8]>;
    let addr = heap.addr(ptr);
    // read string's length from heap
    Self::check_access(
      heap,
      ptr + S::METADATA_OFFSET as u64,
      S::METADATA_SIZE,
      S::METADATA_ALIGN,
    )?;
    let len = unsafe { S::metadata(addr) };
    // create string reference
    Self::check_access(heap, ptr, S::size(len), S::ALIGN)?;
    Ok(unsafe { &*ptr::from_raw_parts(addr, len as usize) })
  }

  /// Returns a reference of a UTF-8 string by the given pointer.
  fn utf8_str(heap: &Self::Heap, ptr: Ptr) -> Result<&str, Self::Error>;

  /// Returns a reference of object metadata by the given pointer.
  fn object(heap: &Self::Heap, ptr: Ptr) -> Result<&Object<[u64]>, Self::Error> {
    type O = Object<[u64]>;
    let addr = heap.addr(ptr);
    // read object metadata's length from heap
    Self::check_access(
      heap,
      ptr + O::METADATA_OFFSET as u64,
      O::METADATA_SIZE,
      O::METADATA_ALIGN,
    )?;
    let len = unsafe { O::metadata(addr) };
    // create object reference
    Self::check_access(heap, ptr, O::size(len), O::ALIGN)?;
    Ok(unsafe { &*ptr::from_raw_parts(addr, len as usize) })
  }

  /// Returns a layout for allocation by the given size and align.
  fn layout(size: usize, align: usize) -> Result<Layout, Self::Error>;

  /// Creates a new garbage collector.
  fn new_gc(&self) -> Self::GarbageCollector;

  /// Checks if the heap is large enough and it should be collected now.
  fn should_collect(&self, heap: &Self::Heap) -> bool;

  /// Checks if the garbage collector succeeded in reducing the heap size.
  /// Returns an error if necessary.
  fn gc_success(&self, heap_size: usize) -> Result<(), Self::Error>;
}

/// Strict policy.
///
/// Checks type of values, division, and memory out of bounds.
pub struct Strict<H, GC> {
  gc_threshold: usize,
  phantom: PhantomData<(H, GC)>,
}

impl<H, GC> Strict<H, GC> {
  /// Creates a new strict policy.
  pub fn new(gc_threshold: usize) -> Self {
    Self {
      gc_threshold,
      phantom: PhantomData,
    }
  }
}

impl<H, GC> Policy for Strict<H, GC>
where
  H: CheckedHeap,
  GC: GarbageCollector,
{
  type Value = StrictValue;
  type Error = StrictError;
  type Heap = H;
  type GarbageCollector = GC;

  fn int_val(i: u64) -> Self::Value {
    StrictValue::Int(i)
  }

  fn f32_val(f: f32) -> Self::Value {
    StrictValue::Float(f)
  }

  fn f64_val(f: f64) -> Self::Value {
    StrictValue::Double(f)
  }

  fn ptr_val(p: Ptr) -> Self::Value {
    StrictValue::Ptr(p)
  }

  fn get_int_ptr(v: &Self::Value) -> Result<u64, Self::Error> {
    match v {
      StrictValue::Int(i) => Ok(*i),
      StrictValue::Ptr(p) => Ok((*p).into()),
      StrictValue::Float(_) => Err(StrictError::TypeMismatch("integer or pointer", "float")),
      StrictValue::Double(_) => Err(StrictError::TypeMismatch("integer or pointer", "double")),
    }
  }

  fn get_f32(v: &Self::Value) -> Result<f32, Self::Error> {
    match v {
      StrictValue::Float(f) => Ok(*f),
      StrictValue::Int(_) => Err(StrictError::TypeMismatch("float", "integer")),
      StrictValue::Ptr(_) => Err(StrictError::TypeMismatch("float", "pointer")),
      StrictValue::Double(_) => Err(StrictError::TypeMismatch("float", "double")),
    }
  }

  fn get_f64(v: &Self::Value) -> Result<f64, Self::Error> {
    match v {
      StrictValue::Double(f) => Ok(*f),
      StrictValue::Int(_) => Err(StrictError::TypeMismatch("double", "integer")),
      StrictValue::Ptr(_) => Err(StrictError::TypeMismatch("double", "pointer")),
      StrictValue::Float(_) => Err(StrictError::TypeMismatch("double", "float")),
    }
  }

  fn get_ptr(v: &Self::Value) -> Result<Ptr, Self::Error> {
    match v {
      StrictValue::Ptr(p) => Ok(*p),
      StrictValue::Int(_) => Err(StrictError::TypeMismatch("pointer", "integer")),
      StrictValue::Float(_) => Err(StrictError::TypeMismatch("pointer", "float")),
      StrictValue::Double(_) => Err(StrictError::TypeMismatch("pointer", "double")),
    }
  }

  fn get_any(v: &Self::Value) -> u64 {
    match v {
      StrictValue::Int(i) => *i,
      StrictValue::Ptr(p) => (*p).into(),
      StrictValue::Float(f) => unsafe { *(f as *const _ as *const u32) as u64 },
      StrictValue::Double(d) => unsafe { *(d as *const _ as *const u64) },
    }
  }

  fn ptr_or_none(v: &Self::Value) -> Option<Ptr> {
    match v {
      StrictValue::Ptr(p) => Some(*p),
      _ => None,
    }
  }

  fn str_ptr_from_const(c: &HeapConst) -> Result<Ptr, Self::Error> {
    if c.kind() == ConstKind::Str {
      Ok(c.ptr())
    } else {
      Err(StrictError::InvalidConst(ConstKind::Str, c.kind()))
    }
  }

  fn obj_ptr_from_const(c: &HeapConst) -> Result<Ptr, Self::Error> {
    if c.kind() == ConstKind::Object {
      Ok(c.ptr())
    } else {
      Err(StrictError::InvalidConst(ConstKind::Object, c.kind()))
    }
  }

  fn unwrap_or<V, F, S>(v: Option<V>, f: F) -> Result<V, Self::Error>
  where
    F: FnOnce() -> S,
    S: Into<String>,
  {
    v.ok_or_else(|| StrictError::Other(f().into()))
  }

  fn check_div(divisor: u64) -> Result<(), Self::Error> {
    if divisor == 0 {
      Err(StrictError::ZeroDivision)
    } else {
      Ok(())
    }
  }

  fn report_err<S>(e: S) -> Result<(), Self::Error>
  where
    S: Into<String>,
  {
    Err(StrictError::Other(e.into()))
  }

  fn new_heap(&self) -> Self::Heap {
    H::new()
  }

  fn check_access(heap: &Self::Heap, p: Ptr, len: usize, align: usize) -> Result<(), Self::Error> {
    if heap.is_valid(p, len) {
      Ok(())
    } else {
      Err(StrictError::OutOfBounds(p, len, align))
    }
  }

  fn utf8_str(heap: &Self::Heap, ptr: Ptr) -> Result<&str, Self::Error> {
    Self::str(heap, ptr)?
      .to_str()
      .ok_or(StrictError::InvalidUtf8(ptr))
  }

  fn layout(size: usize, align: usize) -> Result<Layout, Self::Error> {
    Layout::from_size_align(size, align).map_err(|_| StrictError::InvalidLayout)
  }

  fn new_gc(&self) -> Self::GarbageCollector {
    GC::new()
  }

  fn should_collect(&self, heap: &Self::Heap) -> bool {
    heap.size() > self.gc_threshold
  }

  fn gc_success(&self, heap_size: usize) -> Result<(), Self::Error> {
    if heap_size > self.gc_threshold {
      Err(StrictError::OutOfHeap)
    } else {
      Ok(())
    }
  }
}

/// Value of [`Strict`] policy.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StrictValue {
  /// A integer.
  Int(u64),
  /// A pointer.
  Ptr(Ptr),
  /// A float (f32).
  Float(f32),
  /// A double (f64).
  Double(f64),
}

/// Error for [`Strict`] policy.
#[derive(Debug)]
pub enum StrictError {
  /// Type mismatch, with expected type and actual type.
  TypeMismatch(&'static str, &'static str),
  /// Divisor is zero.
  ZeroDivision,
  /// Memory access out of bounds, with pointer, length and alignment.
  OutOfBounds(Ptr, usize, usize),
  /// Out of heap memory, with heap size limit and actual size.
  OutOfHeap,
  /// Invalid constant, with expected kind and actual kind.
  InvalidConst(ConstKind, ConstKind),
  /// Invalid UTF-8 string, with the string pointer.
  InvalidUtf8(Ptr),
  /// Invalid allocation layout.
  InvalidLayout,
  /// Other error.
  Other(String),
}

impl fmt::Display for StrictError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::TypeMismatch(e, a) => write!(f, "value type mismatch, expected {e}, got {a}"),
      Self::ZeroDivision => write!(f, "divisor is zero"),
      Self::OutOfBounds(p, l, a) => write!(
        f,
        "memory access out of bounds at {p}, length {l}, alignment {a}"
      ),
      Self::OutOfHeap => write!(f, "out of heap memory"),
      Self::InvalidConst(e, a) => write!(f, "invalid constant, expected `{e:?}`, got `{a:?}`"),
      Self::InvalidUtf8(p) => write!(f, "invalid UTF-8 string {p}"),
      Self::InvalidLayout => write!(f, "invalid allocation layout"),
      Self::Other(e) => write!(f, "{e}"),
    }
  }
}

/// Strict policy with alignment checking.
///
/// Checks type of values, division, memory out of bounds and memory alignment.
pub struct StrictAlign<H, GC> {
  strict: Strict<H, GC>,
}

impl<H, GC> StrictAlign<H, GC> {
  /// Creates a new strict alignment policy.
  pub fn new(gc_threshold: usize) -> Self {
    Self {
      strict: Strict::new(gc_threshold),
    }
  }
}

impl<H, GC> Policy for StrictAlign<H, GC>
where
  H: CheckedHeap,
  GC: GarbageCollector,
{
  type Value = StrictValue;
  type Error = StrictAlignError;
  type Heap = H;
  type GarbageCollector = GC;

  fn int_val(i: u64) -> Self::Value {
    Strict::<H, GC>::int_val(i)
  }

  fn f32_val(f: f32) -> Self::Value {
    Strict::<H, GC>::f32_val(f)
  }

  fn f64_val(f: f64) -> Self::Value {
    Strict::<H, GC>::f64_val(f)
  }

  fn ptr_val(p: Ptr) -> Self::Value {
    Strict::<H, GC>::ptr_val(p)
  }

  fn get_int_ptr(v: &Self::Value) -> Result<u64, Self::Error> {
    Strict::<H, GC>::get_int_ptr(v).map_err(StrictAlignError::Strict)
  }

  fn get_f32(v: &Self::Value) -> Result<f32, Self::Error> {
    Strict::<H, GC>::get_f32(v).map_err(StrictAlignError::Strict)
  }

  fn get_f64(v: &Self::Value) -> Result<f64, Self::Error> {
    Strict::<H, GC>::get_f64(v).map_err(StrictAlignError::Strict)
  }

  fn get_ptr(v: &Self::Value) -> Result<Ptr, Self::Error> {
    Strict::<H, GC>::get_ptr(v).map_err(StrictAlignError::Strict)
  }

  fn get_any(v: &Self::Value) -> u64 {
    Strict::<H, GC>::get_any(v)
  }

  fn ptr_or_none(v: &Self::Value) -> Option<Ptr> {
    Strict::<H, GC>::ptr_or_none(v)
  }

  fn str_ptr_from_const(c: &HeapConst) -> Result<Ptr, Self::Error> {
    Strict::<H, GC>::str_ptr_from_const(c).map_err(StrictAlignError::Strict)
  }

  fn obj_ptr_from_const(c: &HeapConst) -> Result<Ptr, Self::Error> {
    Strict::<H, GC>::obj_ptr_from_const(c).map_err(StrictAlignError::Strict)
  }

  fn unwrap_or<V, F, S>(v: Option<V>, f: F) -> Result<V, Self::Error>
  where
    F: FnOnce() -> S,
    S: Into<String>,
  {
    Strict::<H, GC>::unwrap_or(v, f).map_err(StrictAlignError::Strict)
  }

  fn check_div(divisor: u64) -> Result<(), Self::Error> {
    Strict::<H, GC>::check_div(divisor).map_err(StrictAlignError::Strict)
  }

  fn report_err<S>(e: S) -> Result<(), Self::Error>
  where
    S: Into<String>,
  {
    Strict::<H, GC>::report_err(e).map_err(StrictAlignError::Strict)
  }

  fn new_heap(&self) -> Self::Heap {
    self.strict.new_heap()
  }

  fn check_access(heap: &Self::Heap, p: Ptr, len: usize, align: usize) -> Result<(), Self::Error> {
    Strict::<H, GC>::check_access(heap, p, len, align).map_err(StrictAlignError::Strict)?;
    if !align.is_power_of_two() || (u64::from(p) & (align as u64 - 1)) != 0 {
      Err(StrictAlignError::MisalignedAccess(p, len, align))
    } else {
      Ok(())
    }
  }

  fn utf8_str(heap: &Self::Heap, ptr: Ptr) -> Result<&str, Self::Error> {
    Strict::<H, GC>::utf8_str(heap, ptr).map_err(StrictAlignError::Strict)
  }

  fn layout(size: usize, align: usize) -> Result<Layout, Self::Error> {
    Strict::<H, GC>::layout(size, align).map_err(StrictAlignError::Strict)
  }

  fn new_gc(&self) -> Self::GarbageCollector {
    self.strict.new_gc()
  }

  fn should_collect(&self, heap: &Self::Heap) -> bool {
    self.strict.should_collect(heap)
  }

  fn gc_success(&self, heap_size: usize) -> Result<(), Self::Error> {
    self
      .strict
      .gc_success(heap_size)
      .map_err(StrictAlignError::Strict)
  }
}

/// Error for [`StrictAlign`] policy.
#[derive(Debug)]
pub enum StrictAlignError {
  /// Error returned by [`Strict`] policy.
  Strict(StrictError),
  /// Memory access is not aligned, with pointer, length and alignment.
  MisalignedAccess(Ptr, usize, usize),
}

impl fmt::Display for StrictAlignError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Strict(s) => write!(f, "{s}"),
      Self::MisalignedAccess(p, l, a) => write!(
        f,
        "memory access is not aligned at {p}, length {l}, alignment {a}"
      ),
    }
  }
}

/// No check policy.
///
/// Does not check anything.
///
/// # Notes
///
/// This policy can lead to a variety of undefined behaviours.
pub struct NoCheck<H, GC> {
  gc_threshold: usize,
  phantom: PhantomData<(H, GC)>,
}

impl<H, GC> NoCheck<H, GC> {
  /// Creates a new no check policy.
  pub fn new(gc_threshold: usize) -> Self {
    Self {
      gc_threshold,
      phantom: PhantomData,
    }
  }
}

impl<H, GC> Policy for NoCheck<H, GC>
where
  H: Heap,
  GC: GarbageCollector,
{
  type Value = NoCheckValue;
  type Error = NoCheckError;
  type Heap = H;
  type GarbageCollector = GC;

  fn int_val(i: u64) -> Self::Value {
    NoCheckValue::new(i)
  }

  fn f32_val(f: f32) -> Self::Value {
    let value = unsafe { *(&f as *const _ as *const u32) } as u64;
    NoCheckValue::new(value)
  }

  fn f64_val(f: f64) -> Self::Value {
    let value = unsafe { *(&f as *const _ as *const u64) };
    NoCheckValue::new(value)
  }

  fn ptr_val(p: Ptr) -> Self::Value {
    NoCheckValue::new_ptr(p)
  }

  fn get_int_ptr(v: &Self::Value) -> Result<u64, Self::Error> {
    Ok(v.value)
  }

  fn get_f32(v: &Self::Value) -> Result<f32, Self::Error> {
    Ok(unsafe { *(&v.value as *const _ as *const f32) })
  }

  fn get_f64(v: &Self::Value) -> Result<f64, Self::Error> {
    Ok(unsafe { *(&v.value as *const _ as *const f64) })
  }

  fn get_ptr(v: &Self::Value) -> Result<Ptr, Self::Error> {
    Ok(v.value.into())
  }

  fn get_any(v: &Self::Value) -> u64 {
    v.value
  }

  fn ptr_or_none(v: &Self::Value) -> Option<Ptr> {
    v.is_ptr.then_some(v.value.into())
  }

  fn str_ptr_from_const(c: &HeapConst) -> Result<Ptr, Self::Error> {
    Ok(c.ptr())
  }

  fn obj_ptr_from_const(c: &HeapConst) -> Result<Ptr, Self::Error> {
    Ok(c.ptr())
  }

  fn unwrap_or<V, F, S>(v: Option<V>, _: F) -> Result<V, Self::Error>
  where
    F: FnOnce() -> S,
    S: Into<String>,
  {
    Ok(unsafe { v.unwrap_unchecked() })
  }

  fn check_div(_: u64) -> Result<(), Self::Error> {
    Ok(())
  }

  fn report_err<S>(_: S) -> Result<(), Self::Error>
  where
    S: Into<String>,
  {
    Ok(())
  }

  fn new_heap(&self) -> Self::Heap {
    H::new()
  }

  fn check_access(_: &Self::Heap, _: Ptr, _: usize, _: usize) -> Result<(), Self::Error> {
    Ok(())
  }

  fn utf8_str(heap: &Self::Heap, ptr: Ptr) -> Result<&str, Self::Error> {
    Ok(unsafe { std::str::from_utf8_unchecked(&Self::str(heap, ptr)?.bytes) })
  }

  fn layout(size: usize, align: usize) -> Result<Layout, Self::Error> {
    Ok(unsafe { Layout::from_size_align_unchecked(size, align) })
  }

  fn new_gc(&self) -> Self::GarbageCollector {
    GC::new()
  }

  fn should_collect(&self, heap: &Self::Heap) -> bool {
    heap.size() > self.gc_threshold
  }

  /// Checks if the garbage collector succeeded in reducing the heap size.
  /// Returns an error if necessary.
  ///
  /// # Panics
  ///
  /// Panics if unsuccess.
  fn gc_success(&self, heap_size: usize) -> Result<(), Self::Error> {
    if heap_size > self.gc_threshold {
      panic!("out of heap memory");
    }
    Ok(())
  }
}

/// Value of [`NoCheck`] policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NoCheckValue {
  is_ptr: bool,
  value: u64,
}

impl NoCheckValue {
  /// Creates a new normal value.
  fn new(value: u64) -> Self {
    Self {
      is_ptr: false,
      value,
    }
  }

  /// Creates a new pointer.
  fn new_ptr(ptr: Ptr) -> Self {
    Self {
      is_ptr: true,
      value: ptr.into(),
    }
  }
}

/// Error for [`NoCheck`] policy.
#[derive(Debug)]
pub struct NoCheckError;

impl fmt::Display for NoCheckError {
  fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
    unreachable!("`NoCheck` should not return an error")
  }
}
