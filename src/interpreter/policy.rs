/// Execution policy of the VM (interpreter).
pub trait Policy {
  /// Type of all local/global values.
  type Value;

  /// Type of error.
  type Error;

  /// Type of managed heap.
  type Heap;

  /// Type of garbage collector.
  type GarbageCollector;

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

  /// Checks whether the given pointer is valid, returns an error if necessary.
  fn check_ptr(heap: &Self::Heap, p: u64) -> Result<(), Self::Error>;

  /// Creates a new garbage collector.
  fn new_gc(&self) -> Self::GarbageCollector;
}
