/// Managed heap interface.
pub trait Heap {
  //
}

/// Heap that do not check for memory out of bounds.
#[derive(Default)]
pub struct UncheckedHeap {
  size: usize,
  mems: Vec<Mem>,
}

impl UncheckedHeap {
  /// Creates a new heap.
  pub fn new() -> Self {
    Self::default()
  }
}

/// Allocated heap memory.
pub struct Mem {
  obj: Option<Obj>,
  data: Box<[u8]>,
}

/// Object metadata for heap memory.
pub struct Obj {
  index: usize,
  is_array: bool,
}
