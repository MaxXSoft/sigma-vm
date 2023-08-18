use crate::interpreter::heap::{Heap, Meta, Ptr};
use crate::interpreter::loader::Loader;
use crate::interpreter::native::NativeLoader;
use crate::interpreter::policy::Policy;
use crate::interpreter::vm::Vars;
use std::collections::HashMap;
use std::io::{stderr, stdin, stdout, Read, Write};
use std::slice;

/// System call handler.
pub trait Handler<P, H>
where
  P: Policy<Heap = H>,
  H: Heap,
{
  /// Handles the system call request with the given state of virtual machine.
  fn handle(&mut self, state: VmState<P, H>) -> Result<ControlFlow, P::Error>;
}

/// Virtual machine state.
pub struct VmState<'vm, P, H>
where
  P: Policy<Heap = H>,
  H: Heap,
{
  /// Module loader.
  pub loader: &'vm mut Loader,
  /// Native library loader.
  pub native_loader: &'vm mut NativeLoader,
  /// Heap.
  pub heap: &'vm mut H,
  /// Value stack.
  pub value_stack: &'vm mut Vec<P::Value>,
  /// Handle of all initialized modules, and their global variables.
  pub module_globals: &'vm mut HashMap<Ptr, Vars<P::Value>>,
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
pub struct Resolver<P, H>
where
  P: Policy<Heap = H>,
  H: Heap,
{
  handlers: HashMap<i64, Box<dyn Handler<P, H>>>,
}

impl<P, H> Resolver<P, H>
where
  P: Policy<Heap = H>,
  H: Heap,
{
  /// Creates a new system resolver.
  pub(super) fn new() -> Self {
    Self {
      handlers: HashMap::new(),
    }
  }

  /// Calls the given system call.
  pub(super) fn call(
    &mut self,
    syscall: i64,
    state: VmState<P, H>,
  ) -> Result<ControlFlow, P::Error> {
    match syscall {
      0 => self.native_load(state),
      1 => self.native_unload(state),
      2 => self.native_call(state),
      3 => Ok(ControlFlow::Terminate),
      4 => Ok(ControlFlow::GC),
      5 => Self::stack_length(state),
      6 => Self::del(state),
      7 => Self::unload(state),
      8 => Self::read(state),
      9 => Self::write(state, stdout()),
      10 => Self::write(state, stderr()),
      _ => match self.handlers.get_mut(&syscall) {
        Some(handler) => handler.handle(state),
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
  pub fn register(&mut self, syscall: i64, handler: Box<dyn Handler<P, H>>) {
    if syscall >= 0 {
      panic!("`syscall` must be negative");
    }
    self.handlers.insert(syscall, handler);
  }

  /// Loads a native shared library.
  ///
  /// Stack layout:
  /// * s0 (TOS): pointer to library path.
  ///
  /// Stack layout after call:
  /// * s0 (TOS): library handle or zero (failed).
  fn native_load(&mut self, state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    // get library path
    let path_ptr = P::get_ptr(&P::unwrap_val(state.value_stack.pop())?)?;
    let path = P::utf8_str(state.heap, path_ptr)?.to_string();
    // load library
    let handle = Ptr::from(state.native_loader.load(state.heap, &path));
    // update stack
    state.value_stack.push(P::ptr_val(handle));
    Ok(ControlFlow::Continue)
  }

  /// Unloads a native shared library.
  ///
  /// Stack layout:
  /// * s0 (TOS): library handle.
  fn native_unload(&mut self, state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    // get handle
    let handle = P::get_ptr(&P::unwrap_val(state.value_stack.pop())?)?;
    // remove the corresponding library
    state.native_loader.unload(state.heap, handle);
    Ok(ControlFlow::Continue)
  }

  /// Performs a native function call.
  ///
  /// Stack layout:
  /// * s0 (TOS): pointer to function name.
  /// * s1: library handle.
  /// * s2: argument number.
  /// * s3: arguments n - 1.
  /// * ...
  /// * s{n + 2}: arguments 0.
  fn native_call(&self, state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    // get name and handle
    let name_ptr = P::get_ptr(&P::unwrap_val(state.value_stack.pop())?)?;
    let name = P::utf8_str(state.heap, name_ptr)?.to_string();
    let handle = P::get_ptr(&P::unwrap_val(state.value_stack.pop())?)?;
    // get arguments
    let num_args = P::get_int_ptr(&P::unwrap_val(state.value_stack.pop())?)?;
    let mut args = vec![];
    for _ in 0..num_args {
      args.push(P::get_any(&P::unwrap_module(state.value_stack.pop())?));
    }
    args.reverse();
    // call the native function
    let rets = unsafe { state.native_loader.call(handle, &name, state.heap, &args) };
    let rets = P::unwrap_module(rets.ok())?;
    // push return values to stack
    state
      .value_stack
      .extend(rets.iter().map(|v| P::int_val(*v)));
    Ok(ControlFlow::Continue)
  }

  /// Returns length of stack.
  fn stack_length(state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    state
      .value_stack
      .push(P::int_val(state.value_stack.len() as u64));
    Ok(ControlFlow::Continue)
  }

  /// Deletes pointer s0.
  fn del(state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    let s0 = P::unwrap_val(state.value_stack.pop())?;
    let ptr = P::get_ptr(&s0)?;
    match state.heap.meta(ptr) {
      Some(Meta::Module) => {
        state.loader.unload(state.heap, ptr);
      }
      Some(Meta::Native) => state.native_loader.unload(state.heap, ptr),
      _ => state.heap.dealloc(ptr),
    };
    Ok(ControlFlow::Continue)
  }

  /// Unloads module handle s0.
  fn unload(state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    let s0 = P::unwrap_val(state.value_stack.pop())?;
    let handle = P::get_ptr(&s0)?;
    state.loader.unload(state.heap, handle);
    state.module_globals.remove(&handle);
    Ok(ControlFlow::Continue)
  }

  /// Reads bytes from the standard input.
  ///
  /// Stack layout:
  /// * s0 (TOS): length of array.
  /// * s1: array.
  ///
  /// Stack layout after call:
  /// * s0 (TOS): length read, negative if error.
  fn read(state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    // get byte array
    let len = P::get_int_ptr(&P::unwrap_val(state.value_stack.pop())?)? as usize;
    let array = P::get_ptr(&P::unwrap_val(state.value_stack.pop())?)?;
    P::check_access(state.heap, array, len, 1)?;
    let buf = unsafe { slice::from_raw_parts_mut(state.heap.addr_mut(array) as *mut u8, len) };
    // read to array
    let result = stdin().read(buf).unwrap_or(usize::MAX);
    state.value_stack.push(P::int_val(result as u64));
    Ok(ControlFlow::Continue)
  }

  /// Writes bytes to the given writer.
  ///
  /// Stack layout:
  /// * s0 (TOS): length to write.
  /// * s1: array.
  ///
  /// Stack layout after call:
  /// * s0 (TOS): length wrote, negative if error.
  fn write<W>(state: VmState<P, H>, mut w: W) -> Result<ControlFlow, P::Error>
  where
    W: Write,
  {
    // get byte array
    let len = P::get_int_ptr(&P::unwrap_val(state.value_stack.pop())?)? as usize;
    let array = P::get_ptr(&P::unwrap_val(state.value_stack.pop())?)?;
    P::check_access(state.heap, array, len, 1)?;
    let buf = unsafe { slice::from_raw_parts(state.heap.addr(array) as *const u8, len) };
    // write to writer
    let result = w.write(buf).unwrap_or(usize::MAX);
    state.value_stack.push(P::int_val(result as u64));
    Ok(ControlFlow::Continue)
  }
}
