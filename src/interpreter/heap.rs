/// Managed heap interface.
pub trait Heap {
  /// Creates a new heap.
  fn new() -> Self;
}

/// Managed heap with memory out of bounds checking.
pub trait CheckedHeap: Heap {
  //
}

/// Heap that uses system's allocator to allocate memory.
#[derive(Default)]
pub struct System {
  size: usize,
  mems: Vec<Mem>,
}

impl Heap for System {
  fn new() -> Self {
    Self::default()
  }
}

/// Allocated system heap memory.
pub struct Mem {
  obj: Option<Obj>,
  data: Box<[u8]>,
}

/// Object metadata for heap memory.
pub struct Obj {
  index: usize,
  is_array: bool,
}

/// Heap with memory out of bounds checking.
pub struct Checked<H> {
  heap: H,
}

impl<H> Heap for Checked<H>
where
  H: Heap,
{
  fn new() -> Self {
    Self { heap: H::new() }
  }
}

impl<H> CheckedHeap for Checked<H>
where
  H: Heap,
{
  // TODO
}
