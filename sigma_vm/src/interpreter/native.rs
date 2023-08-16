use crate::interpreter::heap::Heap;
use libloading::{Error as Loading, Library, Symbol};
use std::collections::HashMap;
use std::num::NonZeroU64;
use std::{fmt, slice};

/// Native library loader.
pub struct NativeLoader {
  resolved_paths: HashMap<String, Native>,
  loaded_libs: HashMap<Native, Library>,
  next_handle: u64,
}

impl NativeLoader {
  /// Creates a new native library loader.
  pub fn new() -> Self {
    Self {
      resolved_paths: HashMap::new(),
      loaded_libs: HashMap::new(),
      next_handle: 1,
    }
  }

  /// Loads a native shared library by the given path,
  /// return the handle of loaded library, or a invalid handle.
  pub fn load(&mut self, path: &str) -> Result<Native, Error> {
    if let Some(handle) = self.resolved_paths.get(path) {
      Ok(*handle)
    } else {
      match unsafe { Library::new(path) } {
        Ok(lib) => {
          let handle = Native::from(self.next_handle);
          self.next_handle += 1;
          self.resolved_paths.insert(path.into(), handle);
          self.loaded_libs.insert(handle, lib);
          Ok(handle)
        }
        Err(e) => Err(Error::Loading(e)),
      }
    }
  }

  /// Unloads a loaded native shared library by the given handle.
  pub fn unload(&mut self, handle: Native) {
    self.resolved_paths.retain(|_, h| *h != handle);
    self.loaded_libs.remove(&handle);
  }

  /// Unloads all loaded native shared library.
  pub fn unload_all(&mut self) {
    self.resolved_paths.clear();
    self.loaded_libs.clear();
    self.next_handle = 1;
  }

  /// Calls a function in the native shared library by the given handle.
  ///
  /// # Safety
  ///
  /// The signature of the given function must match the FFI of native calls.
  pub unsafe fn call<H>(
    &self,
    handle: Native,
    name: &str,
    heap: &mut H,
    args: &[u64],
  ) -> Result<&[u64], Error>
  where
    H: Heap,
  {
    // get library
    let lib = self.loaded_libs.get(&handle).ok_or(Error::LibNotFound)?;
    // call the native function
    let ret_vals = unsafe {
      let func: Symbol<ffi::NativeFn> = lib.get(name.as_bytes()).map_err(Error::Loading)?;
      func(ffi::VmState {
        heap: &mut (heap as &mut dyn ffi::HeapWrapper),
        num_args: args.len(),
        args: args.as_ptr(),
      })
    };
    // extract return values
    Ok(unsafe { slice::from_raw_parts(ret_vals.rets, ret_vals.num_rets) })
  }
}

/// Errors for the native library loader.
#[derive(Debug)]
pub enum Error {
  /// Library loading error.
  Loading(Loading),
  /// Library not found.
  LibNotFound,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Loading(e) => write!(f, "{e}"),
      Self::LibNotFound => write!(f, "library not found"),
    }
  }
}

/// Native library handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Native {
  /// Invalid handle.
  Invalid,
  /// Handle.
  Handle(NonZeroU64),
}

impl From<Native> for u64 {
  fn from(handle: Native) -> Self {
    match handle {
      Native::Invalid => 0,
      Native::Handle(h) => h.get(),
    }
  }
}

impl From<u64> for Native {
  fn from(value: u64) -> Self {
    NonZeroU64::new(value)
      .map(Self::Handle)
      .unwrap_or(Self::Invalid)
  }
}

impl<E> From<Result<Native, E>> for Native {
  fn from(result: Result<Native, E>) -> Self {
    result.unwrap_or(Self::Invalid)
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
      self
        .alloc(Layout::from_size_align(size, align).unwrap())
        .into()
    }

    fn addr_mut(&mut self, ptr: u64) -> *mut () {
      self.addr_mut(ptr.into())
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
