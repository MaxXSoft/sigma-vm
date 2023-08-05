/// Managed heap.
pub struct Heap {
  size: usize,
  mems: Vec<Mem>,
}

/// Allocated heap memory.
pub struct Mem {
  obj: Option<Obj>,
  data: Box<u8>,
}

/// Object metadata for heap memory.
pub struct Obj {
  index: usize,
  is_array: bool,
}
