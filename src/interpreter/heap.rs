/// Managed heap interface.
pub trait Heap {
  //
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

impl System {
  /// Creates a new heap.
  pub fn new() -> Self {
    Self::default()
  }
}

impl Heap for System {
  // TODO
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
  // TODO
}

impl<H> CheckedHeap for Checked<H>
where
  H: Heap,
{
  // TODO
}
