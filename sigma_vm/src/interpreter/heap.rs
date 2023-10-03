use std::alloc::{self, Layout};
use std::collections::BTreeMap;
use std::{fmt, ops, slice};

/// Heap pointer.
#[repr(transparent)]
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ptr(u64);

impl Ptr {
  /// Returns a null pointer.
  pub fn null() -> Self {
    Self(0)
  }
}

impl From<Ptr> for u64 {
  fn from(ptr: Ptr) -> Self {
    ptr.0
  }
}

impl From<u64> for Ptr {
  fn from(value: u64) -> Self {
    Self(value)
  }
}

impl<E> From<Result<Self, E>> for Ptr {
  fn from(result: Result<Self, E>) -> Self {
    result.unwrap_or(Ptr::null())
  }
}

impl ops::Add<u64> for Ptr {
  type Output = Self;

  fn add(self, rhs: u64) -> Self::Output {
    Self(self.0 + rhs)
  }
}

impl ops::Add<Ptr> for u64 {
  type Output = Ptr;

  fn add(self, rhs: Ptr) -> Self::Output {
    Ptr(self + rhs.0)
  }
}

impl ops::AddAssign<u64> for Ptr {
  fn add_assign(&mut self, rhs: u64) {
    self.0 += rhs;
  }
}

impl ops::Add<i64> for Ptr {
  type Output = Self;

  fn add(self, rhs: i64) -> Self::Output {
    Self((self.0 as i64 + rhs) as u64)
  }
}

impl ops::Add<Ptr> for i64 {
  type Output = Ptr;

  fn add(self, rhs: Ptr) -> Self::Output {
    Ptr((self + rhs.0 as i64) as u64)
  }
}

impl ops::AddAssign<i64> for Ptr {
  fn add_assign(&mut self, rhs: i64) {
    self.0 = (self.0 as i64 + rhs) as u64;
  }
}

impl ops::Sub<u64> for Ptr {
  type Output = Self;

  fn sub(self, rhs: u64) -> Self::Output {
    Self(self.0 - rhs)
  }
}

impl ops::SubAssign<u64> for Ptr {
  fn sub_assign(&mut self, rhs: u64) {
    self.0 -= rhs;
  }
}

impl ops::Sub<i64> for Ptr {
  type Output = Self;

  fn sub(self, rhs: i64) -> Self::Output {
    Self((self.0 as i64 - rhs) as u64)
  }
}

impl ops::SubAssign<i64> for Ptr {
  fn sub_assign(&mut self, rhs: i64) {
    self.0 = (self.0 as i64 - rhs) as u64;
  }
}

impl fmt::Display for Ptr {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "0x{:x}", self.0)
  }
}

/// Managed heap interface.
pub trait Heap {
  /// Creates a new heap.
  fn new() -> Self;

  /// Allocates a new memory with the given layout and metadata.
  /// Returns the pointer of the allocated memory.
  fn alloc(&mut self, layout: Layout, meta: Meta) -> Ptr;

  /// Deallocates the given pointer.
  fn dealloc(&mut self, ptr: Ptr);

  /// Returns the size of all allocated memory in bytes.
  fn size(&self) -> usize;

  /// Returns the size of allocated memory of the given pointer, or [`None`]
  /// if the pointer is invalid.
  fn size_of(&self, ptr: Ptr) -> Option<usize>;

  /// Returns the immutable memory address of the given pointer.
  fn addr(&self, ptr: Ptr) -> *const ();

  /// Returns the mutable memory address of the given pointer.
  fn addr_mut(&mut self, ptr: Ptr) -> *mut ();

  /// Returns a reference to the metadata and the object pointer
  /// of the given heap pointer, or [`None`] if the given pointer is invalid.
  fn meta_ptr(&self, ptr: Ptr) -> Option<(&Meta, Ptr)>;

  /// Returns a reference to the metadata of the given heap pointer,
  /// or [`None`] if the given pointer is invalid or is not equal to
  /// the object pointer.
  fn meta(&self, ptr: Ptr) -> Option<&Meta> {
    self
      .meta_ptr(ptr)
      .and_then(|(m, p)| (ptr == p).then_some(m))
  }

  /// Returns a vector of pointers of all allocated memory.
  fn ptrs(&self) -> Vec<Ptr>;

  /// Resets the internal state.
  fn reset(&mut self);
}

/// Metadata for heap memory.
#[derive(Debug, Clone, Copy)]
pub enum Meta {
  /// Memory stores raw data.
  Raw,
  /// Memory stores an object.
  Obj(Obj),
  /// Memory stores a module handle.
  Module,
  /// Memory stores a native shared library handle.
  Native,
}

/// Object metadata for heap memory.
#[derive(Debug, Clone, Copy)]
pub struct Obj {
  pub kind: ObjKind,
  /// Pointer to the real object metadata.
  pub ptr: Ptr,
  /// Handle of the module where the object was allocated.
  pub module: Ptr,
}

/// Kind of object.
#[derive(Debug, Clone, Copy)]
pub enum ObjKind {
  /// Just an object.
  Obj,
  /// An array of objects.
  ///
  /// With the length of the array.
  Array(usize),
}

/// Managed heap with memory out of bounds checking.
pub trait CheckedHeap: Heap {
  /// Returns `true` if the given pointer and access length is valid.
  fn is_valid(&self, ptr: Ptr, len: usize) -> bool;
}

/// Heap that uses system's allocator to allocate memory.
#[derive(Default)]
pub struct System {
  mems: BTreeMap<Ptr, Mem>,
  size: usize,
}

impl Heap for System {
  fn new() -> Self {
    Self::default()
  }

  fn alloc(&mut self, layout: Layout, meta: Meta) -> Ptr {
    let mem = unsafe { Mem::new(layout, meta) };
    let ptr = (mem.data.as_ptr() as u64).into();
    self.mems.insert(ptr, mem);
    self.size += layout.size();
    ptr
  }

  fn dealloc(&mut self, ptr: Ptr) {
    if let Some(mem) = self.mems.remove(&ptr) {
      self.size -= mem.data.len();
    }
  }

  fn size(&self) -> usize {
    self.size
  }

  fn size_of(&self, ptr: Ptr) -> Option<usize> {
    self.mems.get(&ptr).map(|m| m.data.len())
  }

  fn addr(&self, ptr: Ptr) -> *const () {
    u64::from(ptr) as *const ()
  }

  fn addr_mut(&mut self, ptr: Ptr) -> *mut () {
    u64::from(ptr) as *mut ()
  }

  fn meta_ptr(&self, ptr: Ptr) -> Option<(&Meta, Ptr)> {
    match self.mems.range(..=ptr).next_back() {
      Some((p, mem)) if ptr < *p + mem.data.len() as u64 => Some((&mem.meta, *p)),
      _ => None,
    }
  }

  fn ptrs(&self) -> Vec<Ptr> {
    self.mems.keys().copied().collect()
  }

  fn reset(&mut self) {
    self.mems.clear();
    self.size = 0;
  }
}

/// Allocated system heap memory.
pub struct Mem {
  data: Box<[u8]>,
  meta: Meta,
}

impl Mem {
  /// Create a new memory from the given layout and metadata.
  ///
  /// # Safety
  ///
  /// The allocated memory is uninitialized, so it must be written
  /// before reading.
  unsafe fn new(layout: Layout, meta: Meta) -> Self {
    let ptr = alloc::alloc(layout);
    if ptr.is_null() {
      alloc::handle_alloc_error(layout);
    }
    let data = Box::from_raw(slice::from_raw_parts_mut(ptr, layout.size()));
    Self { data, meta }
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
    if size == 0 {
      return;
    }
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

  fn alloc(&mut self, layout: Layout, meta: Meta) -> Ptr {
    let ptr = self.heap.alloc(layout, meta);
    self.add_range(self.addr(ptr), layout.size());
    ptr
  }

  fn dealloc(&mut self, ptr: Ptr) {
    // get left bound and right bound
    let l = self.addr(ptr) as usize;
    let prev_size = self.size();
    self.heap.dealloc(ptr);
    if prev_size == self.size() {
      return;
    }
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

  fn size_of(&self, ptr: Ptr) -> Option<usize> {
    self.heap.size_of(ptr)
  }

  fn addr(&self, ptr: Ptr) -> *const () {
    self.heap.addr(ptr)
  }

  fn addr_mut(&mut self, ptr: Ptr) -> *mut () {
    self.heap.addr_mut(ptr)
  }

  fn meta_ptr(&self, ptr: Ptr) -> Option<(&Meta, Ptr)> {
    self.heap.meta_ptr(ptr)
  }

  fn ptrs(&self) -> Vec<Ptr> {
    self.heap.ptrs()
  }

  fn reset(&mut self) {
    self.heap.reset();
    self.ranges.clear();
  }
}

impl<H> CheckedHeap for Checked<H>
where
  H: Heap,
{
  fn is_valid(&self, ptr: Ptr, len: usize) -> bool {
    if len == 0 {
      false
    } else {
      let l = self.heap.addr(ptr) as usize;
      match self.ranges.range(..=l).next_back() {
        Some((_, rr)) => l + len - 1 <= *rr,
        _ => false,
      }
    }
  }
}
