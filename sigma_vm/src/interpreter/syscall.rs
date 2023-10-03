use crate::bytecode::consts::Const;
use crate::interpreter::heap::{Heap, Meta, Ptr};
use crate::interpreter::loader::Loader;
use crate::interpreter::native::NativeLoader;
use crate::interpreter::policy::Policy;
use crate::interpreter::vm::Vars;
use std::collections::HashMap;
use std::io::{stderr, stdin, stdout, Read, Write};
use std::num::NonZeroU64;
use std::path::PathBuf;
use std::{process, slice};

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

impl<'vm, P, H> VmState<'vm, P, H>
where
  P: Policy<Heap = H>,
  H: Heap,
{
  fn pop(&mut self, e: &'static str) -> Result<P::Value, P::Error> {
    P::unwrap(self.value_stack.pop(), e)
  }
}

/// Control flow after the system call.
pub enum ControlFlow {
  /// Continue the execution.
  Continue,
  /// Terminate the execution.
  Terminate,
  /// Run the garbage collector, and then continue.
  GC,
  /// Print stack trace and panic.
  Panic,
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
      11 => Self::exit(state),
      12 => Ok(ControlFlow::Panic),
      13 => Self::bytes_eq(state),
      14 => Self::itoa(state),
      15 => Self::ftoa(state),
      16 => Self::dtoa(state),
      _ => match self.handlers.get_mut(&syscall) {
        Some(handler) => handler.handle(state),
        None => {
          P::report_err(format!("invalid system call {syscall}")).map(|_| ControlFlow::Continue)
        }
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
  fn native_load(&mut self, mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    // get library path
    let path_ptr = P::get_ptr(&state.pop("failed to get library path")?)?;
    let path: PathBuf = P::utf8_str(state.heap, path_ptr)?.split('/').collect();
    // load library
    let handle = Ptr::from(state.native_loader.load(state.heap, path));
    // update stack
    state.value_stack.push(P::ptr_val(handle));
    Ok(ControlFlow::Continue)
  }

  /// Unloads a native shared library.
  ///
  /// Stack layout:
  /// * s0 (TOS): library handle.
  fn native_unload(&mut self, mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    // get handle
    let handle = P::get_ptr(&state.pop("failed to get library handle")?)?;
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
  ///
  /// Stack layout after call:
  /// * s0 (TOS): zero if native call succeeded.
  /// * s1 if s0 is zero: return value n - 1.
  /// * ...
  /// * s{n} if s0 is zero: return value 0.
  fn native_call(&self, mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    // get name and handle
    let name_ptr = P::get_ptr(&state.pop("failed to get function name pointer")?)?;
    let name = P::utf8_str(state.heap, name_ptr)?.to_string();
    let handle = P::get_ptr(&state.pop("failed to get library handle")?)?;
    // get arguments
    let num_args = P::get_int_ptr(&state.pop("failed to get argument number")?)?;
    let mut args = vec![];
    for _ in 0..num_args {
      args.push(P::get_any(&state.pop("failed to get argument")?));
    }
    args.reverse();
    // call the native function
    let rets = match unsafe { state.native_loader.call(handle, &name, state.heap, &args) } {
      Ok(rets) => rets,
      Err(e) => {
        state
          .value_stack
          .push(P::int_val(NonZeroU64::from(e).get()));
        return Ok(ControlFlow::Continue);
      }
    };
    // push return values to stack
    state
      .value_stack
      .extend(rets.iter().map(|v| P::int_val(*v)));
    state.value_stack.push(P::int_val(0));
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
  fn del(mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    let ptr = P::get_ptr(&state.pop("failed to get the pointer")?)?;
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
  fn unload(mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    let handle = P::get_ptr(&state.pop("failed to get module handle")?)?;
    state.loader.unload(state.heap, handle);
    state.module_globals.remove(&handle);
    Ok(ControlFlow::Continue)
  }

  /// Reads bytes from the standard input.
  ///
  /// Stack layout:
  /// * s0 (TOS): length to read.
  /// * s1: array.
  ///
  /// Stack layout after call:
  /// * s0 (TOS): length read, negative if error.
  fn read(mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    // get byte array
    let len = P::get_int_ptr(&state.pop("failed to get length")?)? as usize;
    let array = P::get_ptr(&state.pop("failed to get array pointer")?)?;
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
  fn write<W>(mut state: VmState<P, H>, mut w: W) -> Result<ControlFlow, P::Error>
  where
    W: Write,
  {
    // get byte array
    let len = P::get_int_ptr(&state.pop("failed to get length")?)? as usize;
    let array = P::get_ptr(&state.pop("failed to get array pointer")?)?;
    P::check_access(state.heap, array, len, 1)?;
    let buf = unsafe { slice::from_raw_parts(state.heap.addr(array) as *const u8, len) };
    // write to writer
    let result = w.write(buf).unwrap_or(usize::MAX);
    state.value_stack.push(P::int_val(result as u64));
    Ok(ControlFlow::Continue)
  }

  /// Terminates the current process with an exit code.
  ///
  /// Stack layout:
  /// * s0 (TOS): exit code.
  fn exit(mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    let code = P::get_int_ptr(&state.pop("failed to get exit code")?)?;
    process::exit(code as i32)
  }

  /// Checks if the given two bytes-like objects are equal.
  ///
  /// Stack layout:
  /// * s0 (TOS): object.
  /// * s1 (TOS): another object.
  ///
  /// Stack layout after call:
  /// * s0 (TOS): 0 for unequal, 1 for equal.
  fn bytes_eq(mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    // get bytes to be compared
    let p1 = P::get_ptr(&state.pop("failed to get the pointer")?)?;
    let p2 = P::get_ptr(&state.pop("failed to get the pointer")?)?;
    let s1 = P::str(state.heap, p1)?;
    let s2 = P::str(state.heap, p2)?;
    // perform comparison
    state.value_stack.push(P::int_val((s1 == s2) as u64));
    Ok(ControlFlow::Continue)
  }

  /// Converts the given integer to string.
  ///
  /// Stack layout:
  /// * s0 (TOS): base.
  /// * s1: integer.
  ///
  /// Stack layout after call:
  /// * s0 (TOS): string.
  fn itoa(mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    let base = P::get_int_ptr(&state.pop("failed to get base")?)?;
    if base > 36 {
      P::report_err(format!("invalid base {base}"))?;
    }
    let mut i = P::get_int_ptr(&state.pop("failed to get the integer")?)?;
    let mut s = String::new();
    loop {
      let d = i % base;
      i /= base;
      s.push(P::unwrap(
        char::from_digit(d as u32, base as u32),
        format!("invalid digit {d} for base {base}"),
      )?);
      if i == 0 {
        break;
      }
    }
    let hc = Const::from(s).into_heap_const(state.heap);
    state.value_stack.push(P::ptr_val(hc.ptr()));
    Ok(ControlFlow::Continue)
  }

  /// Converts the given float to string.
  ///
  /// Stack layout:
  /// * s0 (TOS): float.
  ///
  /// Stack layout after call:
  /// * s0 (TOS): string.
  fn ftoa(mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    let f = P::get_f32(&state.pop("faild to get the float")?)?;
    let hc = Const::from(format!("{f}")).into_heap_const(state.heap);
    state.value_stack.push(P::ptr_val(hc.ptr()));
    Ok(ControlFlow::Continue)
  }

  /// Converts the given double to string.
  ///
  /// Stack layout:
  /// * s0 (TOS): double.
  ///
  /// Stack layout after call:
  /// * s0 (TOS): string.
  fn dtoa(mut state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    let d = P::get_f64(&state.pop("faild to get the double")?)?;
    let hc = Const::from(format!("{d}")).into_heap_const(state.heap);
    state.value_stack.push(P::ptr_val(hc.ptr()));
    Ok(ControlFlow::Continue)
  }
}
