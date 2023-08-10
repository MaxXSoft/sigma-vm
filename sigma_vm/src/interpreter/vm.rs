use crate::bytecode::consts::HeapConst;
use crate::interpreter::gc::PotentialRoots;
use crate::interpreter::heap::{Heap, Obj, ObjKind};
use crate::interpreter::loader::Loader;
use crate::interpreter::policy::Policy;
use crate::utils::IntoU64;
use std::mem;

/// Virtual machine for running bytecode.
pub struct VM<P: Policy> {
  global_heap: GlobalHeap<P>,
  loader: Loader,
}

impl<P: Policy> VM<P> {
  /// Creates a new virtual machine.
  pub fn new(policy: P) -> Self {
    Self {
      global_heap: GlobalHeap::new(policy),
      loader: Loader::new(),
    }
  }
}

/// Global heap for all contexts, containing a heap and a garbage collector.
pub struct GlobalHeap<P: Policy> {
  policy: P,
  heap: P::Heap,
  gc: P::GarbageCollector,
}

impl<P: Policy> GlobalHeap<P> {
  /// Creates a new global heap.
  pub fn new(policy: P) -> Self {
    let heap = policy.new_heap();
    let gc = policy.new_gc();
    Self { policy, heap, gc }
  }

  /// Loads the given pointer as type `T`.
  pub(super) fn load<T>(&mut self, ptr: u64) -> Result<u64, P>
  where
    T: Copy + IntoU64,
  {
    let len = mem::size_of::<T>();
    cfr!(P::check_access(&self.heap, ptr, len, len))?;
    Ok(unsafe { *(self.heap.addr(ptr) as *const T) }.into_u64())
  }

  /// Creates a value from a heap constant.
  pub(super) fn val_from_const(&self, c: &HeapConst) -> P::Value {
    P::val_from_const(&self.heap, c)
  }

  /// Stores the given value (of type `T`) to the memory
  /// pointed by the given pointer.
  pub(super) fn store<T>(&mut self, v: P::Value, ptr: u64) -> Result<(), P>
  where
    T: Copy,
  {
    let len = mem::size_of::<T>();
    cfr!(P::check_access(&self.heap, ptr, len, len))?;
    unsafe { *(self.heap.addr_mut(ptr) as *mut T) = *(&P::get_any(&v) as *const _ as *const T) };
    Ok(())
  }

  /// Checks if the heap should be collected.
  pub(super) fn should_collect(&self) -> Result<(), P> {
    if self.policy.should_collect(&self.heap) {
      Err(ControlFlow::GC)
    } else {
      Ok(())
    }
  }

  /// Allocates a new heap memory.
  pub(super) fn alloc(&mut self, size: u64, align: u64) -> Result<u64, P> {
    let layout = cfr!(P::layout(size as usize, align as usize))?;
    Ok(self.heap.alloc(layout))
  }

  /// Allocates heap memory for the given object metadata pointer.
  pub(super) fn new_object(&mut self, obj_ptr: u64) -> Result<u64, P> {
    let object = cfr!(P::object(&self.heap, obj_ptr))?;
    self.alloc_obj(object.size, object.align, ObjKind::Obj, obj_ptr)
  }

  /// Allocates array for the given object metadata pointer.
  pub(super) fn new_array(&mut self, obj_ptr: u64, len: u64) -> Result<u64, P> {
    let object = cfr!(P::object(&self.heap, obj_ptr))?;
    let size = if len != 0 {
      object.aligned_size() * (len - 1) + object.size
    } else {
      0
    };
    self.alloc_obj(size, object.align, ObjKind::Array(len as usize), obj_ptr)
  }

  /// Deallocates the given pointer.
  pub(super) fn dealloc(&mut self, ptr: u64) {
    self.heap.dealloc(ptr)
  }

  /// Allocates a new memory with object metadata.
  fn alloc_obj(&mut self, size: u64, align: u64, kind: ObjKind, obj_ptr: u64) -> Result<u64, P> {
    let layout = cfr!(P::layout(size as usize, align as usize))?;
    Ok(self.heap.alloc_obj(layout, Obj { kind, ptr: obj_ptr }))
  }

  /// Runs garbage collector.
  fn collect(&mut self, proots: PotentialRoots<P>) -> Result<(), P> {
    cfr!(self.policy.collect(&mut self.gc, &mut self.heap, proots))
  }
}

/// Control flow actions.
pub enum ControlFlow<P: Policy> {
  /// Error occurred.
  Error(P::Error),
  /// Stop execution.
  Stop,
  /// Requests a garbage collection.
  GC,
  /// Requests an external call, with a heap pointer to the call information.
  CallExt(u64),
}

/// Result that returns a control flow action as an error.
pub(super) type Result<T, P> = std::result::Result<T, ControlFlow<P>>;

/// Helper macro for converting policy results into control flow results.
macro_rules! cfr {
  ($pr:expr) => {
    $pr.map_err(crate::interpreter::vm::ControlFlow::Error)
  };
}
pub(super) use cfr;
