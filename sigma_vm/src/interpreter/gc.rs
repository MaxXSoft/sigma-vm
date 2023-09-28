use crate::bytecode::consts::{HeapConst, Object};
use crate::interpreter::heap::{Heap, Meta, ObjKind, Ptr};
use crate::interpreter::policy::Policy;
use crate::interpreter::vm::Vars;
use std::collections::HashSet;
use std::{iter, mem};

/// Garbage collector interface.
pub trait GarbageCollector {
  /// Creates a new garbage collector.
  fn new() -> Self;

  /// Collects garbage on the given heap.
  ///
  /// Returns heap pointers that should be deallocated.
  fn collect<'gc, P, M, C>(
    &mut self,
    heap: &P::Heap,
    roots: Roots<'gc, P, M, C>,
  ) -> Result<Vec<Ptr>, P::Error>
  where
    P: 'gc + Policy,
    M: 'gc + Iterator<Item = ModuleRoots<'gc, P>>,
    C: 'gc + Iterator<Item = ContextRoots<'gc, P>>;

  /// Resets the internal state.
  fn reset(&mut self);
}

/// Garbage collection roots.
pub struct Roots<'gc, P, M, C>
where
  P: ?Sized + Policy,
  M: Iterator<Item = ModuleRoots<'gc, P>>,
  C: Iterator<Item = ContextRoots<'gc, P>>,
{
  pub values: &'gc [P::Value],
  pub mroots: M,
  pub croots: C,
}

impl<'gc, P, M, C> Roots<'gc, P, M, C>
where
  P: 'gc + ?Sized + Policy,
  M: 'gc + Iterator<Item = ModuleRoots<'gc, P>>,
  C: 'gc + Iterator<Item = ContextRoots<'gc, P>>,
{
  /// Returns an iterator of all garbage collection roots
  /// (pointers and their module handles).
  fn roots(self) -> impl 'gc + Iterator<Item = (Ptr, Option<Ptr>)> {
    self
      .values
      .iter()
      .filter_map(|v| P::ptr_or_none(v).map(|p| (p, None)))
      .chain(self.mroots.flat_map(|mr| mr.roots()))
      .chain(self.croots.flat_map(|cr| cr.roots()))
  }
}

/// Garbage collection roots of modules.
pub struct ModuleRoots<'gc, P: ?Sized + Policy> {
  pub handle: Ptr,
  pub consts: &'gc [HeapConst],
  pub globals: &'gc Vars<P::Value>,
}

impl<'gc, P> ModuleRoots<'gc, P>
where
  P: 'gc + ?Sized + Policy,
{
  fn roots(self) -> impl 'gc + Iterator<Item = (Ptr, Option<Ptr>)> {
    self.consts.iter().map(|c| (c.ptr(), None)).chain(
      self
        .globals
        .iter()
        .filter_map(move |v| P::ptr_or_none(v).map(|p| (p, Some(self.handle)))),
    )
  }
}

/// Garbage collection roots of contexts.
pub struct ContextRoots<'gc, P: ?Sized + Policy> {
  pub module: Ptr,
  pub vars: &'gc [Vars<P::Value>],
}

impl<'gc, P> ContextRoots<'gc, P>
where
  P: 'gc + ?Sized + Policy,
{
  fn roots(self) -> impl 'gc + Iterator<Item = (Ptr, Option<Ptr>)> {
    self
      .vars
      .iter()
      .flat_map(|vs| vs.iter().filter_map(P::ptr_or_none))
      .chain(iter::once(self.module))
      .map(|p| (p, None))
  }
}

/// Garbage collector that does nothing.
pub struct Nothing;

impl GarbageCollector for Nothing {
  fn new() -> Self {
    Self
  }

  fn collect<'gc, P, M, C>(
    &mut self,
    _: &P::Heap,
    _: Roots<'gc, P, M, C>,
  ) -> Result<Vec<Ptr>, P::Error>
  where
    P: 'gc + Policy,
    M: 'gc + Iterator<Item = ModuleRoots<'gc, P>>,
    C: 'gc + Iterator<Item = ContextRoots<'gc, P>>,
  {
    Ok(vec![])
  }

  fn reset(&mut self) {}
}

/// Mark-sweep garbage collector.
pub struct MarkSweep;

impl MarkSweep {
  /// Pushes object pointer to the worklist by the given object metadata.
  fn extend_workist<P>(
    worklist: &mut Vec<(Ptr, Option<Ptr>)>,
    object: &Object<[u64]>,
    heap: &P::Heap,
    ptr: Ptr,
    handle: Option<Ptr>,
  ) -> Result<(), P::Error>
  where
    P: Policy,
  {
    for o in &object.managed_ptr.offsets {
      let ptr_size = mem::size_of::<u64>() as u64;
      let ptr = ptr + o * ptr_size;
      P::check_access(heap, ptr, ptr_size as usize, ptr_size as usize)?;
      worklist.push((unsafe { *(heap.addr(ptr) as *const Ptr) }, handle));
    }
    Ok(())
  }
}

impl GarbageCollector for MarkSweep {
  fn new() -> Self {
    Self
  }

  fn collect<'gc, P, M, C>(
    &mut self,
    heap: &P::Heap,
    roots: Roots<'gc, P, M, C>,
  ) -> Result<Vec<Ptr>, P::Error>
  where
    P: 'gc + Policy,
    M: 'gc + Iterator<Item = ModuleRoots<'gc, P>>,
    C: 'gc + Iterator<Item = ContextRoots<'gc, P>>,
  {
    // mark reachable pointers
    let mut reachable = HashSet::new();
    let mut worklist: Vec<_> = roots.roots().collect();
    while let Some((ptr, handle)) = worklist.pop() {
      // skip if the pointer is the same as the module handle,
      // or the pointer has already been marked
      if Some(ptr) == handle || !reachable.insert(ptr) {
        continue;
      }
      // get object metadata
      if let Some(Meta::Obj(obj)) = heap.meta(ptr) {
        let object: &Object<[u64]> = P::object(heap, obj.ptr)?;
        // mark object metadata and module handle
        worklist.push((obj.ptr, handle));
        worklist.push((obj.module, handle));
        // handle by kind
        match obj.kind {
          ObjKind::Obj => Self::extend_workist::<P>(&mut worklist, object, heap, ptr, handle)?,
          ObjKind::Array(len) => {
            // visit all objects
            let step = object.aligned_size();
            for i in 0..len as u64 {
              Self::extend_workist::<P>(&mut worklist, object, heap, ptr + i * step, handle)?;
            }
          }
        };
      }
    }
    // return unreachable pointers
    let mut ptrs = heap.ptrs();
    ptrs.retain(|p| !reachable.contains(p));
    Ok(ptrs)
  }

  fn reset(&mut self) {}
}
