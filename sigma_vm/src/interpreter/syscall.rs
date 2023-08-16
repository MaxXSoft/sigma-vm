use crate::interpreter::heap::Heap;
use crate::interpreter::loader::{Loader, Source};
use crate::interpreter::policy::Policy;
use crate::interpreter::vm::Vars;
use libloading::{Library, Symbol};
use std::collections::HashMap;
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
  /// Heap.
  pub heap: &'vm mut H,
  /// Value stack.
  pub value_stack: &'vm mut Vec<P::Value>,
  /// Handle of all initialized modules, and their global variables.
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
      0 => Self::native_call(state),
      1 => Ok(ControlFlow::Terminate),
      2 => Ok(ControlFlow::GC),
      3 => Self::stack_length(state),
      4 => Self::del(state),
      5 => Self::unload(state),
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

  /// Performs a native function call.
  ///
  /// Stack layout:
  /// * s0 (TOS): pointer to function name.
  /// * s1 (TOS): pointer to library path.
  /// * s2: argument number.
  /// * s3: arguments n - 1.
  /// * ...
  /// * s{n + 2}: arguments 0.
  fn native_call(state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    // get name and path
    let name_ptr = P::get_ptr(&P::unwrap_val(state.value_stack.pop())?)?;
    let name = P::utf8_str(state.heap, name_ptr)?;
    let path_ptr = P::get_ptr(&P::unwrap_val(state.value_stack.pop())?)?;
    let path = P::utf8_str(state.heap, path_ptr)?;
    // get arguments
    let num_args = P::get_int_ptr(&P::unwrap_val(state.value_stack.pop())?)?;
    let mut args = vec![];
    for _ in 0..num_args {
      args.push(P::get_any(&P::unwrap_module(state.value_stack.pop())?));
    }
    args.reverse();
    // load library and call the native function
    let ret_vals = unsafe {
      let lib = P::unwrap_module(Library::new(path).ok())?;
      let func: Symbol<ffi::NativeFn> = P::unwrap_module(lib.get(name.as_bytes()).ok())?;
      func(ffi::VmState {
        heap: &mut (state.heap as &mut dyn ffi::HeapWrapper),
        num_args: num_args as usize,
        args: args.as_ptr(),
      })
    };
    // push return values to stack
    let rets = unsafe { slice::from_raw_parts(ret_vals.rets, ret_vals.num_rets) };
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
    state.heap.dealloc(ptr);
    Ok(ControlFlow::Continue)
  }

  /// Unloads module handle s0.
  fn unload(state: VmState<P, H>) -> Result<ControlFlow, P::Error> {
    let s0 = P::unwrap_val(state.value_stack.pop())?;
    let source = Source::from(P::get_int_ptr(&s0)?);
    state.loader.unload(source);
    state.module_globals.remove(&source);
    Ok(ControlFlow::Continue)
  }
}

/// FFI for native calls.
mod ffi {
  use crate::interpreter::heap::Heap;
  use std::alloc::Layout;
  use std::ffi::c_void;

  /// Function type of native functions.
  pub type NativeFn = unsafe extern "C" fn(VmState) -> RetVals;

  /// Virtual machine state.
  #[repr(C)]
  pub struct VmState<'vm> {
    pub heap: &'vm mut &'vm mut dyn HeapWrapper,
    pub num_args: usize,
    pub args: *const u64,
  }

  /// Return values.
  #[repr(C)]
  pub struct RetVals {
    pub num_rets: usize,
    pub rets: *const u64,
  }

  /// Wrapper trait for heaps.
  pub trait HeapWrapper {
    /// Allocates a new memory with the given size and align.
    /// Returns the pointer of the allocated memory.
    ///
    /// # Panics
    ///
    /// Panics if size or align are invalid.
    fn alloc(&mut self, size: usize, align: usize) -> u64;

    /// Returns the mutable memory address of the given pointer.
    fn addr_mut(&mut self, ptr: u64) -> *mut ();
  }

  impl<H> HeapWrapper for H
  where
    H: Heap,
  {
    fn alloc(&mut self, size: usize, align: usize) -> u64 {
      self.alloc(Layout::from_size_align(size, align).unwrap())
    }

    fn addr_mut(&mut self, ptr: u64) -> *mut () {
      self.addr_mut(ptr)
    }
  }

  /// Allocates a new memory with the given size and align.
  /// Returns the heap pointer of the allocated memory.
  ///
  /// # Panics
  ///
  /// Panics if size or align are invalid.
  #[no_mangle]
  pub extern "C" fn sigma_vm_heap_alloc(
    heap: &mut &mut dyn HeapWrapper,
    size: usize,
    align: usize,
  ) -> u64 {
    heap.alloc(size, align)
  }

  /// Returns the memory address of the given pointer.
  #[no_mangle]
  pub extern "C" fn sigma_vm_heap_addr(heap: &mut &mut dyn HeapWrapper, ptr: u64) -> *mut c_void {
    heap.addr_mut(ptr) as *mut c_void
  }
}
