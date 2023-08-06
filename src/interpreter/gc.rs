use crate::bytecode::consts::Const;
use crate::interpreter::heap::{Heap, Obj, ObjAddr, ObjKind};
use crate::interpreter::policy::Policy;
use crate::interpreter::vm::Vars;
use std::collections::HashSet;

/// Garbage collector interface.
pub trait GarbageCollector {
  /// Creates a new garbage collector.
  fn new(threshold: usize) -> Self;

  /// Collects garbage on the given heap.
  fn collect<P>(
    &mut self,
    heap: &mut P::Heap,
    consts: &[Const],
    proots: PotentialRoots<P>,
  ) -> Result<(), P::Error>
  where
    P: Policy;
}

/// Potential GC roots.
pub struct PotentialRoots<'gc, P: Policy> {
  pub values: &'gc [P::Value],
  pub locals: &'gc [Vars<P::Value>],
  pub globals: &'gc Vars<P::Value>,
}

impl<'gc, P: 'gc + Policy> PotentialRoots<'gc, P> {
  /// Returns an iterator of all GC roots (pointers).
  pub fn roots(&self) -> impl 'gc + Iterator<Item = u64> {
    self
      .values
      .iter()
      .filter_map(P::get_ptr)
      .chain(
        self
          .locals
          .iter()
          .flat_map(|vs| vs.iter().filter_map(P::get_ptr)),
      )
      .chain(self.globals.iter().filter_map(P::get_ptr))
  }
}

// /// Returns an iterator of all pointers in the given object.
// pub fn ptrs<P>(
//   heap: &P::Heap,
//   consts: &[Const],
//   addr: *const (),
//   obj: &Obj,
// ) -> Result<impl Iterator<Item = u64>, P::Error>
// where
//   P: Policy,
// {
//   // get object metadata
//   let object = match obj.addr {
//     ObjAddr::Heap(ptr) => todo!(),
//     ObjAddr::Const(index) => unsafe { P::object(consts, index) }?,
//   };
//   todo!()
// }

/// Garbage collector that does nothing.
pub struct Nothing;

impl GarbageCollector for Nothing {
  fn new(_: usize) -> Self {
    Self
  }

  fn collect<P>(
    &mut self,
    _: &mut P::Heap,
    _: &[Const],
    _: PotentialRoots<P>,
  ) -> Result<(), P::Error>
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

impl GarbageCollector for MarkSweep {
  fn new(threshold: usize) -> Self {
    Self { threshold }
  }

  fn collect<P>(
    &mut self,
    heap: &mut P::Heap,
    consts: &[Const],
    proots: PotentialRoots<P>,
  ) -> Result<(), P::Error>
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
        todo!()
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
