/// Garbage collector interface.
pub trait GarbageCollector {
  /// Creates a new garbage collector.
  fn new(threshold: usize) -> Self;
}
