use crate::bytecode::consts::{ConstKind, HeapConst, Object};
use crate::interpreter::gc::{GarbageCollector, PotentialRoots};
use crate::interpreter::heap::{CheckedHeap, Heap};
use std::alloc::Layout;
use std::marker::PhantomData;
use std::{fmt, mem, ptr};

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
  fn ptr_val(p: u64) -> Self::Value;

  /// Extracts an integer value from the given value.
  ///
  /// Pointer values will be treat as integers.
  fn get_int_ptr(v: &Self::Value) -> Result<u64, Self::Error>;

  /// Extracts a 32-bit floating point value from the given value.
  fn get_f32(v: &Self::Value) -> Result<f32, Self::Error>;

  /// Extracts a 64-bit floating point value from the given value.
  fn get_f64(v: &Self::Value) -> Result<f64, Self::Error>;

  /// Extracts a pointer value from the given value.
  fn get_ptr(v: &Self::Value) -> Result<u64, Self::Error>;

  /// Extracts a 64-bit untyped value from the given value.
  fn get_any(v: &Self::Value) -> u64;

  /// Returns the pointer value if the given value is a pointer,
  /// otherwise [`None`].
  fn ptr_or_none(v: &Self::Value) -> Option<u64>;

  /// Returns an object metadata pointer from the given heap constant,
  /// returns an error if necessary.
  fn obj_ptr_from_const(c: &HeapConst) -> Result<u64, Self::Error>;

  /// Unwraps an [`Option<Value>`], returns an error if necessary.
  fn unwrap_val<V>(v: Option<V>) -> Result<V, Self::Error>;

  /// Checks the given integer divisor, returns an error if necessary.
  fn check_div(divisor: u64) -> Result<(), Self::Error>;

  /// Creates a new heap.
  fn new_heap(&self) -> Self::Heap;

  /// Checks whether the given memory access is valid,
  /// returns an error if necessary.
  fn check_access(heap: &Self::Heap, p: u64, len: usize) -> Result<(), Self::Error>;

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

  /// Returns a reference of object metadata by the given pointer.
  fn object(heap: &Self::Heap, ptr: u64) -> Result<&Object<[u64]>, Self::Error> {
    // read object metadata's length from heap
    let addr = heap.addr(ptr) as *const u64;
    let field_size = mem::size_of::<u64>();
    Self::check_access(heap, ptr, field_size * 3)?;
    let len = unsafe { *addr.offset(2) };
    // create object reference
    Self::check_access(heap, ptr + field_size as u64 * 3, field_size * len as usize)?;
    Ok(unsafe { &*ptr::from_raw_parts(addr as *const (), len as usize) })
  }

  /// Returns a layout for allocation by the given size and align.
  fn layout(size: usize, align: usize) -> Result<Layout, Self::Error>;

  /// Creates a new garbage collector.
  fn new_gc(&self) -> Self::GarbageCollector;

  /// Runs the garbage collector if necessary, and checks if
  /// the GC succeeded in reducing the heap size.
  ///
  /// Returns an error if necessary.
  fn collect(
    &self,
    gc: &mut Self::GarbageCollector,
    heap: &mut Self::Heap,
    proots: PotentialRoots<Self>,
  ) -> Result<(), Self::Error>;
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

  fn ptr_val(p: u64) -> Self::Value {
    StrictValue::Ptr(p)
  }

  fn get_int_ptr(v: &Self::Value) -> Result<u64, Self::Error> {
    match v {
      StrictValue::Int(i) => Ok(*i),
      StrictValue::Ptr(p) => Ok(*p),
      _ => Err(StrictError::TypeMismatch),
    }
  }

  fn get_f32(v: &Self::Value) -> Result<f32, Self::Error> {
    match v {
      StrictValue::Float(f) => Ok(*f),
      _ => Err(StrictError::TypeMismatch),
    }
  }

  fn get_f64(v: &Self::Value) -> Result<f64, Self::Error> {
    match v {
      StrictValue::Double(f) => Ok(*f),
      _ => Err(StrictError::TypeMismatch),
    }
  }

  fn get_ptr(v: &Self::Value) -> Result<u64, Self::Error> {
    match v {
      StrictValue::Ptr(p) => Ok(*p),
      _ => Err(StrictError::TypeMismatch),
    }
  }

  fn get_any(v: &Self::Value) -> u64 {
    match v {
      StrictValue::Int(i) => *i,
      StrictValue::Ptr(p) => *p,
      StrictValue::Float(f) => unsafe { *(f as *const _ as *const u32) as u64 },
      StrictValue::Double(d) => unsafe { *(d as *const _ as *const u64) },
    }
  }

  fn ptr_or_none(v: &Self::Value) -> Option<u64> {
    match v {
      StrictValue::Ptr(p) => Some(*p),
      _ => None,
    }
  }

  fn obj_ptr_from_const(c: &HeapConst) -> Result<u64, Self::Error> {
    if c.kind() == ConstKind::Object {
      Ok(c.ptr())
    } else {
      Err(StrictError::InvalidObject)
    }
  }

  fn unwrap_val<V>(v: Option<V>) -> Result<V, Self::Error> {
    v.ok_or(StrictError::ExpectedValue)
  }

  fn check_div(divisor: u64) -> Result<(), Self::Error> {
    if divisor == 0 {
      Err(StrictError::ZeroDivision)
    } else {
      Ok(())
    }
  }

  fn new_heap(&self) -> Self::Heap {
    H::new()
  }

  fn check_access(heap: &Self::Heap, p: u64, len: usize) -> Result<(), Self::Error> {
    if heap.is_valid(p, len) {
      Ok(())
    } else {
      Err(StrictError::OutOfBounds)
    }
  }

  fn layout(size: usize, align: usize) -> Result<Layout, Self::Error> {
    Layout::from_size_align(size, align).map_err(|_| StrictError::InvalidLayout)
  }

  fn new_gc(&self) -> Self::GarbageCollector {
    GC::new()
  }

  fn collect(
    &self,
    gc: &mut Self::GarbageCollector,
    heap: &mut Self::Heap,
    proots: PotentialRoots<Self>,
  ) -> Result<(), Self::Error> {
    if heap.size() > self.gc_threshold {
      gc.collect(heap, proots)?;
      if heap.size() > self.gc_threshold {
        return Err(StrictError::OutOfHeap);
      }
    }
    Ok(())
  }
}

/// Value of [`Strict`] policy.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StrictValue {
  Int(u64),
  Ptr(u64),
  Float(f32),
  Double(f64),
}

/// Error for [`Strict`] policy.
#[derive(Debug)]
pub enum StrictError {
  /// Type mismatch.
  TypeMismatch,
  /// Expected a value.
  ExpectedValue,
  /// Divisor is zero.
  ZeroDivision,
  /// Memory access out of bounds.
  OutOfBounds,
  /// Out of heap memory.
  OutOfHeap,
  /// Invalid object metadata.
  InvalidObject,
  /// Invalid allocation layout.
  InvalidLayout,
}

impl fmt::Display for StrictError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::TypeMismatch => write!(f, "value type mismatch"),
      Self::ExpectedValue => write!(f, "expected a value, got nothing"),
      Self::ZeroDivision => write!(f, "divisor is zero"),
      Self::OutOfBounds => write!(f, "memory access out of bounds"),
      Self::OutOfHeap => write!(f, "out of heap memory"),
      Self::InvalidObject => write!(f, "invalid object metadata"),
      Self::InvalidLayout => write!(f, "invalid allocation layout"),
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

  fn ptr_val(p: u64) -> Self::Value {
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

  fn get_ptr(v: &Self::Value) -> Result<u64, Self::Error> {
    Strict::<H, GC>::get_ptr(v).map_err(StrictAlignError::Strict)
  }

  fn get_any(v: &Self::Value) -> u64 {
    Strict::<H, GC>::get_any(v)
  }

  fn ptr_or_none(v: &Self::Value) -> Option<u64> {
    Strict::<H, GC>::ptr_or_none(v)
  }

  fn obj_ptr_from_const(c: &HeapConst) -> Result<u64, Self::Error> {
    Strict::<H, GC>::obj_ptr_from_const(c).map_err(StrictAlignError::Strict)
  }

  fn unwrap_val<V>(v: Option<V>) -> Result<V, Self::Error> {
    Strict::<H, GC>::unwrap_val(v).map_err(StrictAlignError::Strict)
  }

  fn check_div(divisor: u64) -> Result<(), Self::Error> {
    Strict::<H, GC>::check_div(divisor).map_err(StrictAlignError::Strict)
  }

  fn new_heap(&self) -> Self::Heap {
    self.strict.new_heap()
  }

  fn check_access(heap: &Self::Heap, p: u64, mut len: usize) -> Result<(), Self::Error> {
    Strict::<H, GC>::check_access(heap, p, len).map_err(StrictAlignError::Strict)?;
    // since the bytecode only defines memory access operation up to 8 bytes
    // we just check for alignment up to 8 bytes
    if len > mem::size_of::<u64>() {
      len = mem::size_of::<u64>();
    }
    if !len.is_power_of_two() || (p & (len as u64 - 1)) != 0 {
      Err(StrictAlignError::MisalignedAccess)
    } else {
      Ok(())
    }
  }

  fn layout(size: usize, align: usize) -> Result<Layout, Self::Error> {
    Strict::<H, GC>::layout(size, align).map_err(StrictAlignError::Strict)
  }

  fn new_gc(&self) -> Self::GarbageCollector {
    self.strict.new_gc()
  }

  fn collect(
    &self,
    gc: &mut Self::GarbageCollector,
    heap: &mut Self::Heap,
    proots: PotentialRoots<Self>,
  ) -> Result<(), Self::Error> {
    let proots = PotentialRoots {
      consts: proots.consts,
      values: proots.values,
      vars: proots.vars,
    };
    self
      .strict
      .collect(gc, heap, proots)
      .map_err(StrictAlignError::Strict)
  }
}

/// Error for [`StrictAlign`] policy.
#[derive(Debug)]
pub enum StrictAlignError {
  /// Error returned by [`Strict`] policy.
  Strict(StrictError),
  /// Memory access is not aligned.
  MisalignedAccess,
}

impl fmt::Display for StrictAlignError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Strict(s) => write!(f, "{s}"),
      Self::MisalignedAccess => write!(f, "memory access is not aligned"),
    }
  }
}

/// No check policy.
///
/// Does not check type of values, division and memory out of bounds.
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
  type Error = ();
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

  fn ptr_val(p: u64) -> Self::Value {
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

  fn get_ptr(v: &Self::Value) -> Result<u64, Self::Error> {
    Ok(v.value)
  }

  fn get_any(v: &Self::Value) -> u64 {
    v.value
  }

  fn ptr_or_none(v: &Self::Value) -> Option<u64> {
    v.is_ptr.then_some(v.value)
  }

  fn obj_ptr_from_const(c: &HeapConst) -> Result<u64, Self::Error> {
    Ok(c.ptr())
  }

  fn unwrap_val<V>(v: Option<V>) -> Result<V, Self::Error> {
    Ok(unsafe { v.unwrap_unchecked() })
  }

  fn check_div(_: u64) -> Result<(), Self::Error> {
    Ok(())
  }

  fn new_heap(&self) -> Self::Heap {
    H::new()
  }

  fn check_access(_: &Self::Heap, _: u64, _: usize) -> Result<(), Self::Error> {
    Ok(())
  }

  fn layout(size: usize, align: usize) -> Result<Layout, Self::Error> {
    Ok(unsafe { Layout::from_size_align_unchecked(size, align) })
  }

  fn new_gc(&self) -> Self::GarbageCollector {
    GC::new()
  }

  /// Runs the garbage collector if necessary, and checks if
  /// the GC succeeded in reducing the heap size.
  ///
  /// Returns an error if necessary.
  ///
  /// # Panics
  ///
  /// Panics if unsuccess.
  fn collect(
    &self,
    gc: &mut Self::GarbageCollector,
    heap: &mut Self::Heap,
    proots: PotentialRoots<Self>,
  ) -> Result<(), Self::Error> {
    if heap.size() > self.gc_threshold {
      gc.collect(heap, proots)?;
      if heap.size() > self.gc_threshold {
        panic!("out of heap memory");
      }
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
  fn new_ptr(value: u64) -> Self {
    Self {
      is_ptr: true,
      value,
    }
  }
}
