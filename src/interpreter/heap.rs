/// Managed heap.
#[derive(Default)]
pub struct Heap {
  size: usize,
  mems: Vec<Mem>,
}

impl Heap {
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
