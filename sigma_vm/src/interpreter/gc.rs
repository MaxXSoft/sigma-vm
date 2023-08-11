use crate::bytecode::consts::{HeapConst, Object};
use crate::interpreter::context::Vars;
use crate::interpreter::heap::{Heap, ObjKind};
use crate::interpreter::policy::Policy;
use std::collections::HashSet;
use std::mem;

/// Garbage collector interface.
pub trait GarbageCollector {
  /// Creates a new garbage collector.
  fn new() -> Self;

  /// Collects garbage on the given heap.
  fn collect<P>(&mut self, heap: &mut P::Heap, proots: PotentialRoots<P>) -> Result<(), P::Error>
  where
    P: Policy;

  /// Resets the internal state.
  fn reset(&mut self);
}

/// Potential GC roots.
pub struct PotentialRoots<'gc, P: ?Sized + Policy> {
  pub consts: &'gc [HeapConst],
  pub values: &'gc [P::Value],
  pub vars: &'gc [Vars<P::Value>],
}

impl<'gc, P> PotentialRoots<'gc, P>
where
  P: 'gc + ?Sized + Policy,
{
  /// Returns an iterator of all GC roots (pointers).
  pub fn roots(&self) -> impl 'gc + Iterator<Item = u64> {
    self
      .consts
      .iter()
      .map(|c| c.ptr())
      .chain(self.values.iter().filter_map(P::ptr_or_none))
      .chain(
        self
          .vars
          .iter()
          .flat_map(|vs| vs.iter().filter_map(P::ptr_or_none)),
      )
  }
}

/// Garbage collector that does nothing.
pub struct Nothing;

impl GarbageCollector for Nothing {
  fn new() -> Self {
    Self
  }

  fn collect<P>(&mut self, _: &mut P::Heap, _: PotentialRoots<P>) -> Result<(), P::Error>
  where
    P: Policy,
  {
    Ok(())
  }

  fn reset(&mut self) {}
}

/// Mark-sweep garbage collector.
pub struct MarkSweep;

impl MarkSweep {
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
      P::check_access(heap, ptr, ptr_size as usize, ptr_size as usize)?;
      worklist.push(unsafe { *(heap.addr(ptr) as *const u64) });
    }
    Ok(())
  }
}

impl GarbageCollector for MarkSweep {
  fn new() -> Self {
    Self
  }

  fn collect<P>(&mut self, heap: &mut P::Heap, proots: PotentialRoots<P>) -> Result<(), P::Error>
  where
    P: Policy,
  {
    // mark reachable pointers
    let mut reachable = HashSet::new();
    let mut worklist: Vec<_> = proots.roots().collect();
    while let Some(ptr) = worklist.pop() {
      if !reachable.insert(ptr) {
        continue;
      }
      // get object metadata
      if let Some(obj) = heap.obj(ptr) {
        let object: &Object<[u64]> = P::object(heap, obj.ptr)?;
        // mark object metadata
        worklist.push(obj.ptr);
        // handle by kind
        match obj.kind {
          ObjKind::Obj => Self::extend_workist::<P>(&mut worklist, object, heap, ptr)?,
          ObjKind::Array(len) => {
            // visit all objects
            let step = object.aligned_size();
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

  fn reset(&mut self) {}
}