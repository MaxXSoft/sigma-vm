use crate::interpreter::gc::GarbageCollector;
use crate::interpreter::heap::{CheckedHeap, Heap};
use std::marker::PhantomData;

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
  fn get_int(v: &Self::Value) -> Result<u64, Self::Error>;

  /// Extracts a 32-bit floating point value from the given value.
  fn get_f32(v: &Self::Value) -> Result<f32, Self::Error>;

  /// Extracts a 64-bit floating point value from the given value.
  fn get_f64(v: &Self::Value) -> Result<f64, Self::Error>;

  /// Returns the pointer value if the given value is a pointer,
  /// otherwise [`None`].
  fn get_ptr(v: &Self::Value) -> Option<u64>;

  /// Checks the given integer divisor, returns an error if necessary.
  fn check_div(divisor: u64) -> Result<(), Self::Error>;

  /// Creates a new heap.
  fn new_heap(&self) -> Self::Heap;

  /// Checks whether the given memory access is valid,
  /// returns an error if necessary.
  fn check_access(heap: &Self::Heap, p: u64, len: usize) -> Result<(), Self::Error>;

  /// Creates a new garbage collector.
  fn new_gc(&self) -> Self::GarbageCollector;
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

  fn get_int(v: &Self::Value) -> Result<u64, Self::Error> {
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

  fn get_ptr(v: &Self::Value) -> Option<u64> {
    match v {
      StrictValue::Ptr(p) => Some(*p),
      _ => None,
    }
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

  fn new_gc(&self) -> Self::GarbageCollector {
    GC::new(self.gc_threshold)
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
  /// Divisor is zero.
  ZeroDivision,
  /// Memory access out of bounds.
  OutOfBounds,
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

  fn get_int(v: &Self::Value) -> Result<u64, Self::Error> {
    Strict::<H, GC>::get_int(v).map_err(StrictAlignError::Strict)
  }

  fn get_f32(v: &Self::Value) -> Result<f32, Self::Error> {
    Strict::<H, GC>::get_f32(v).map_err(StrictAlignError::Strict)
  }

  fn get_f64(v: &Self::Value) -> Result<f64, Self::Error> {
    Strict::<H, GC>::get_f64(v).map_err(StrictAlignError::Strict)
  }

  fn get_ptr(v: &Self::Value) -> Option<u64> {
    Strict::<H, GC>::get_ptr(v)
  }

  fn check_div(divisor: u64) -> Result<(), Self::Error> {
    Strict::<H, GC>::check_div(divisor).map_err(StrictAlignError::Strict)
  }

  fn new_heap(&self) -> Self::Heap {
    self.strict.new_heap()
  }

  fn check_access(heap: &Self::Heap, p: u64, len: usize) -> Result<(), Self::Error> {
    Strict::<H, GC>::check_access(heap, p, len).map_err(StrictAlignError::Strict)?;
    if !len.is_power_of_two() || (p & (len as u64 - 1)) != 0 {
      Err(StrictAlignError::MisalignedAccess)
    } else {
      Ok(())
    }
  }

  fn new_gc(&self) -> Self::GarbageCollector {
    self.strict.new_gc()
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

/// No check policy.
///
/// Does not check type of values, division and memory out of bounds.
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

  fn get_int(v: &Self::Value) -> Result<u64, Self::Error> {
    Ok(v.value)
  }

  fn get_f32(v: &Self::Value) -> Result<f32, Self::Error> {
    Ok(unsafe { *(&v.value as *const _ as *const f32) })
  }

  fn get_f64(v: &Self::Value) -> Result<f64, Self::Error> {
    Ok(unsafe { *(&v.value as *const _ as *const f64) })
  }

  fn get_ptr(v: &Self::Value) -> Option<u64> {
    v.is_ptr.then_some(v.value)
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

  fn new_gc(&self) -> Self::GarbageCollector {
    GC::new(self.gc_threshold)
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
