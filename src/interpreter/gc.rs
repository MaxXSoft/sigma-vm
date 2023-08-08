use crate::bytecode::consts::{HeapConst, Object};
use crate::interpreter::heap::{Heap, ObjKind};
use crate::interpreter::policy::Policy;
use crate::interpreter::vm::Vars;
use std::collections::HashSet;
use std::{mem, ptr};

/// Garbage collector interface.
pub trait GarbageCollector {
  /// Creates a new garbage collector.
  fn new(threshold: usize) -> Self;

  /// Collects garbage on the given heap.
  fn collect<P>(&mut self, heap: &mut P::Heap, proots: PotentialRoots<P>) -> Result<(), P::Error>
  where
    P: Policy;
}

/// Potential GC roots.
pub struct PotentialRoots<'gc, P: Policy> {
  pub consts: &'gc [HeapConst],
  pub values: &'gc [P::Value],
  pub locals: &'gc [Vars<P::Value>],
  pub globals: &'gc Vars<P::Value>,
}

impl<'gc, P: 'gc + Policy> PotentialRoots<'gc, P> {
  /// Returns an iterator of all GC roots (pointers).
  pub fn roots(&self) -> impl 'gc + Iterator<Item = u64> {
    self
      .consts
      .iter()
      .map(|c| c.ptr())
      .chain(self.values.iter().filter_map(P::ptr_or_none))
      .chain(
        self
          .locals
          .iter()
          .flat_map(|vs| vs.iter().filter_map(P::ptr_or_none)),
      )
      .chain(self.globals.iter().filter_map(P::ptr_or_none))
  }
}

/// Garbage collector that does nothing.
pub struct Nothing;

impl GarbageCollector for Nothing {
  fn new(_: usize) -> Self {
    Self
  }

  fn collect<P>(&mut self, _: &mut P::Heap, _: PotentialRoots<P>) -> Result<(), P::Error>
  where
    P: Policy,
  {
    Ok(())
  }
}

/// Mark-sweep garbage collector.
pub struct MarkSweep {
  threshold: usize,
}

impl MarkSweep {
  /// Returns a reference of object metadata by the given [`ObjAddr`].
  fn object<'a, P>(heap: &P::Heap, ptr: u64) -> Result<&'a Object<[u64]>, P::Error>
  where
    P: Policy,
  {
    // read object metadata's length from heap
    let addr = heap.addr(ptr) as *const u64;
    let field_size = mem::size_of::<u64>();
    P::check_access(heap, ptr, field_size * 3)?;
    let len = unsafe { *addr.offset(2) };
    // create object reference
    P::check_access(heap, ptr + field_size as u64 * 3, field_size * len as usize)?;
    Ok(unsafe { &*ptr::from_raw_parts(addr as *const (), len as usize) })
  }

  /// Pushes object pointer to the worklist by the given object metadata.
  fn extend_workist<P>(
    worklist: &mut Vec<u64>,
    object: &Object<[u64]>,
    heap: &P::Heap,
    ptr: u64,
  ) -> Result<(), P::Error>
  where
    P: Policy,
  {
    for o in &object.managed_ptr.offsets {
      let ptr_size = mem::size_of::<u64>() as u64;
      let ptr = ptr + o * ptr_size;
      P::check_access(heap, ptr, ptr_size as usize)?;
      worklist.push(unsafe { *(heap.addr(ptr) as *const u64) });
    }
    Ok(())
  }
}

impl GarbageCollector for MarkSweep {
  fn new(threshold: usize) -> Self {
    Self { threshold }
  }

  fn collect<P>(&mut self, heap: &mut P::Heap, proots: PotentialRoots<P>) -> Result<(), P::Error>
  where
    P: Policy,
  {
    if heap.size() <= self.threshold {
      return Ok(());
    }
    // mark reachable pointers
    let mut reachable = HashSet::new();
    let mut worklist: Vec<_> = proots.roots().collect();
    while let Some(ptr) = worklist.pop() {
      if !reachable.insert(ptr) {
        continue;
      }
      // get object metadata
      if let Some(obj) = heap.obj(ptr) {
        let object: &Object<[u64]> = Self::object::<P>(heap, obj.ptr)?;
        // mark object metadata
        worklist.push(obj.ptr);
        // handle by kind
        match obj.kind {
          ObjKind::Obj => Self::extend_workist::<P>(&mut worklist, object, heap, ptr)?,
          ObjKind::Array(len) => {
            // calculate step
            assert!(object.align.is_power_of_two(), "invalid alignment");
            let step = match object.size & (object.align - 1) {
              0 => object.size,
              r => object.size + object.align - r,
            };
            // visit all objects
            for i in 0..len as u64 {
              Self::extend_workist::<P>(&mut worklist, object, heap, ptr + i * step)?;
            }
          }
        };
      }
    }
    // deallocate unreachable pointers
    for ptr in heap.ptrs() {
      if !reachable.contains(&ptr) {
        heap.dealloc(ptr);
      }
    }
    Ok(())
  }
}
