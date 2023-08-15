use crate::interpreter::heap::Heap;
use crate::interpreter::loader::{Loader, Source};
use crate::interpreter::policy::Policy;
use crate::interpreter::vm::Vars;
use std::collections::HashMap;

/// System call handler.
pub type Handler<'vm, P, H> =
  Box<dyn FnMut(VmState<'vm, P, H>) -> Result<ControlFlow, <P as Policy>::Error>>;

/// Virtual machine state.
pub struct VmState<'vm, P: Policy, H: Heap> {
  pub loader: &'vm mut Loader,
  pub heap: &'vm mut H,
  pub value_stack: &'vm mut Vec<P::Value>,
  pub module_globals: &'vm mut HashMap<Source, Vars<P::Value>>,
}

/// Control flow after the system call.
pub enum ControlFlow {
  /// Continue the execution.
  Continue,
  /// Terminate the execution.
  Terminate,
  /// Run the garbage collector, and then continue.
  GC,
}

/// System call resolver.
pub struct Resolver<'vm, P: Policy, H: Heap> {
  handlers: HashMap<i64, Handler<'vm, P, H>>,
}

impl<'vm, P, H> Resolver<'vm, P, H>
where
  P: Policy,
  H: Heap,
{
  /// Creates a new system resolver.
  pub fn new() -> Self {
    Self {
      handlers: HashMap::new(),
    }
  }

  /// Calls the given system call.
  pub(super) fn call(
    &mut self,
    syscall: i64,
    state: VmState<'vm, P, H>,
  ) -> Result<ControlFlow, P::Error> {
    match syscall {
      0 => Self::native_call(state),
      1 => Ok(ControlFlow::Terminate),
      2 => Ok(ControlFlow::GC),
      3 => Self::stack_size(state),
      4 => Self::del(state),
      5 => Self::unload(state),
      _ => match self.handlers.get_mut(&syscall) {
        Some(handler) => handler(state),
        None => P::report_invalid_syscall().map(|_| ControlFlow::Continue),
      },
    }
  }

  /// Registers a custom system call handler. `syscall` must be negative.
  /// If multiple handlers are registered for the same system call number,
  /// only the last handler is kept.
  ///
  /// # Panics
  ///
  /// Panics if `syscall` is not positive.
  pub fn register(&mut self, syscall: i64, handler: Handler<'vm, P, H>) {
    if syscall >= 0 {
      panic!("`syscall` must be negative");
    }
    self.handlers.insert(syscall, handler);
  }

  /// Performs a native function call.
  fn native_call(state: VmState<'vm, P, H>) -> Result<ControlFlow, P::Error> {
    todo!();
    Ok(ControlFlow::Continue)
  }

  /// Returns size of stack.
  fn stack_size(state: VmState<'vm, P, H>) -> Result<ControlFlow, P::Error> {
    state
      .value_stack
      .push(P::int_val(state.value_stack.len() as u64));
    Ok(ControlFlow::Continue)
  }

  /// Deletes pointer s0.
  fn del(state: VmState<'vm, P, H>) -> Result<ControlFlow, P::Error> {
    let s0 = P::unwrap_val(state.value_stack.pop())?;
    let ptr = P::get_ptr(&s0)?;
    state.heap.dealloc(ptr);
    Ok(ControlFlow::Continue)
  }

  /// Unloads module handle s0.
  fn unload(state: VmState<'vm, P, H>) -> Result<ControlFlow, P::Error> {
    let s0 = P::unwrap_val(state.value_stack.pop())?;
    let source = Source::from(P::get_int_ptr(&s0)?);
    state.loader.unload(source);
    state.module_globals.remove(&source);
    Ok(ControlFlow::Continue)
  }
}
