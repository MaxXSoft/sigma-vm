use std::alloc::{self, Layout};
use std::collections::{BTreeMap, HashMap};
use std::slice;

/// Managed heap interface.
pub trait Heap {
  /// Creates a new heap.
  fn new() -> Self;

  /// Allocates a new memory with the given layout.
  /// Returns the pointer of the allocated memory.
  fn alloc(&mut self, layout: Layout) -> u64;

  /// Allocates a new memory with the given layout and object metadata.
  /// Returns the pointer of the allocated memory.
  fn alloc_obj(&mut self, layout: Layout, obj: Obj) -> u64;

  /// Deallocates the given pointer.
  fn dealloc(&mut self, ptr: u64);

  /// Returns the size of all allocated memory in bytes.
  fn size(&self) -> usize;

  /// Returns the immutable memory address of the given pointer.
  fn addr(&self, ptr: u64) -> *const ();

  /// Returns the mutable memory address of the given pointer.
  fn addr_mut(&mut self, ptr: u64) -> *mut ();

  /// Returns a reference to the heap object metadata of the given pointer, or
  /// [`None`] if the corresponding heap memory is not allocated for an object.
  fn obj(&self, ptr: u64) -> Option<&Obj>;

  /// Returns a vector of pointers of all allocated memory.
  fn ptrs(&self) -> Vec<u64>;
}

/// Object metadata for heap memory.
#[derive(Debug)]
pub struct Obj {
  kind: ObjKind,
  addr: ObjAddr,
}

impl Obj {
  /// Creates a new object metadata.
  pub fn new(kind: ObjKind, addr: ObjAddr) -> Self {
    Self { kind, addr }
  }
}

/// Kind of object.
#[derive(Debug)]
pub enum ObjKind {
  /// Just an object.
  Obj,
  /// An array of objects.
  ///
  /// With the length of the array.
  Array(usize),
}

/// Address of object metadata.
#[derive(Debug)]
pub enum ObjAddr {
  /// Object metadata is on the heap.
  ///
  /// With a heap memory pointer.
  Heap(u64),
  /// Object metadata is in the constant pool.
  ///
  /// With a constant pool index.
  Const(usize),
}

/// Managed heap with memory out of bounds checking.
pub trait CheckedHeap: Heap {
  /// Returns `true` if the given pointer and access length is valid.
  fn is_valid(&self, ptr: u64, len: usize) -> bool;
}

/// Heap that uses system's allocator to allocate memory.
#[derive(Default)]
pub struct System {
  mems: HashMap<u64, Mem>,
  size: usize,
}

impl System {
  /// Allocates a new memory.
  fn alloc(&mut self, layout: Layout, obj: Option<Obj>) -> u64 {
    let mem = unsafe { Mem::new(layout, obj) };
    let ptr = mem.data.as_ptr() as u64;
    self.mems.insert(ptr, mem);
    self.size += layout.size();
    ptr
  }
}

impl Heap for System {
  fn new() -> Self {
    Self::default()
  }

  fn alloc(&mut self, layout: Layout) -> u64 {
    self.alloc(layout, None)
  }

  fn alloc_obj(&mut self, layout: Layout, obj: Obj) -> u64 {
    self.alloc(layout, Some(obj))
  }

  fn dealloc(&mut self, ptr: u64) {
    if let Some(mem) = self.mems.remove(&ptr) {
      self.size -= mem.data.len();
    }
  }

  fn size(&self) -> usize {
    self.size
  }

  fn addr(&self, ptr: u64) -> *const () {
    ptr as *const ()
  }

  fn addr_mut(&mut self, ptr: u64) -> *mut () {
    ptr as *mut ()
  }

  fn obj(&self, ptr: u64) -> Option<&Obj> {
    self.mems.get(&ptr).and_then(|m| m.obj.as_ref())
  }

  fn ptrs(&self) -> Vec<u64> {
    self.mems.keys().copied().collect()
  }
}

/// Allocated system heap memory.
pub struct Mem {
  data: Box<[u8]>,
  obj: Option<Obj>,
}

impl Mem {
  /// Create a new memory from the given layout and object metadata.
  ///
  /// # Safety
  ///
  /// The allocated memory is uninitialized.
  unsafe fn new(layout: Layout, obj: Option<Obj>) -> Self {
    let ptr = alloc::alloc(layout);
    if ptr.is_null() {
      alloc::handle_alloc_error(layout);
    }
    let data = Box::from_raw(slice::from_raw_parts_mut(ptr, layout.size()));
    Self { data, obj }
  }
}

/// Heap with memory out of bounds checking.
pub struct Checked<H> {
  heap: H,
  ranges: BTreeMap<usize, usize>,
}

impl<H> Checked<H> {
  /// Adds a new range from the given address and size.
  fn add_range(&mut self, addr: *const (), size: usize) {
    let l = addr as usize;
    let r = l + size - 1;
    if let Some((_, rr)) = self.ranges.range_mut(..=l).next_back() {
      assert!(*rr < l, "overlapping memory allocated");
      if *rr + 1 == l {
        *rr = r;
        return;
      }
    }
    self.ranges.insert(l, r);
  }
}

impl<H> Heap for Checked<H>
where
  H: Heap,
{
  fn new() -> Self {
    Self {
      heap: H::new(),
      ranges: BTreeMap::new(),
    }
  }

  fn alloc(&mut self, layout: Layout) -> u64 {
    let ptr = self.heap.alloc(layout);
    self.add_range(self.addr(ptr), layout.size());
    ptr
  }

  fn alloc_obj(&mut self, layout: Layout, obj: Obj) -> u64 {
    let ptr = self.heap.alloc_obj(layout, obj);
    self.add_range(self.addr(ptr), layout.size());
    ptr
  }

  fn dealloc(&mut self, ptr: u64) {
    // get left bound and right bound
    let l = self.addr(ptr) as usize;
    let prev_size = self.size();
    self.heap.dealloc(ptr);
    let r = l + prev_size - self.size() - 1;
    // update the target range
    let (&ll, rr) = self.ranges.range_mut(..=l).next_back().unwrap();
    let prev_rr = *rr;
    if ll < l {
      *rr = l - 1;
    } else {
      self.ranges.remove(&ll);
    }
    if r < prev_rr {
      self.ranges.insert(r + 1, prev_rr);
    }
  }

  fn size(&self) -> usize {
    self.heap.size()
  }

  fn addr(&self, ptr: u64) -> *const () {
    self.heap.addr(ptr)
  }

  fn addr_mut(&mut self, ptr: u64) -> *mut () {
    self.heap.addr_mut(ptr)
  }

  fn obj(&self, ptr: u64) -> Option<&Obj> {
    self.heap.obj(ptr)
  }

  fn ptrs(&self) -> Vec<u64> {
    self.heap.ptrs()
  }
}

impl<H> CheckedHeap for Checked<H>
where
  H: Heap,
{
  fn is_valid(&self, ptr: u64, len: usize) -> bool {
    let l = self.heap.addr(ptr) as usize;
    match self.ranges.range(..=l).next_back() {
      Some((_, rr)) => l + len - 1 <= *rr,
      _ => false,
    }
  }
}
