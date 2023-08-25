use crate::interpreter::heap::{Heap, Meta, Ptr};
use libloading::{Error as Loading, Library, Symbol};
use std::alloc::Layout;
use std::collections::HashMap;
use std::num::NonZeroU64;
use std::{fmt, slice};

/// Native library loader.
pub struct NativeLoader {
  resolved_paths: HashMap<String, Ptr>,
  loaded_libs: HashMap<Ptr, Library>,
}

impl NativeLoader {
  /// Creates a new native library loader.
  pub fn new() -> Self {
    Self {
      resolved_paths: HashMap::new(),
      loaded_libs: HashMap::new(),
    }
  }

  /// Loads a native shared library by the given path,
  /// return the handle of loaded library, or a invalid handle.
  pub fn load<H>(&mut self, heap: &mut H, path: &str) -> Result<Ptr, Error>
  where
    H: Heap,
  {
    if let Some(handle) = self.resolved_paths.get(path) {
      Ok(*handle)
    } else {
      match unsafe { Library::new(path) } {
        Ok(lib) => {
          let handle = heap.alloc(Layout::from_size_align(1, 1).unwrap(), Meta::Native);
          self.resolved_paths.insert(path.into(), handle);
          self.loaded_libs.insert(handle, lib);
          Ok(handle)
        }
        Err(e) => Err(Error::Loading(e)),
      }
    }
  }

  /// Unloads a loaded native shared library by the given handle,
  /// also deallocates the handle.
  pub fn unload<H>(&mut self, heap: &mut H, handle: Ptr)
  where
    H: Heap,
  {
    if self.loaded_libs.remove(&handle).is_some() {
      self.resolved_paths.retain(|_, h| *h != handle);
      heap.dealloc(handle);
    }
  }

  /// Unloads all loaded native shared library,
  /// the handles will not be deallocated.
  pub(super) fn unload_all(&mut self) {
    self.resolved_paths.clear();
    self.loaded_libs.clear();
  }

  /// Calls a function in the native shared library by the given handle.
  ///
  /// # Safety
  ///
  /// The signature of the given function must match the FFI of native calls.
  pub unsafe fn call<H>(
    &self,
    handle: Ptr,
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
    let func: Symbol<ffi::NativeFn> = lib.get(name.as_bytes()).map_err(Error::Loading)?;
    let ret_vals = func(&ffi::VmState {
      heap: &mut (heap as &mut dyn ffi::HeapWrapper),
      num_args: args.len(),
      args: args.as_ptr(),
      heap_alloc: ffi::heap_alloc as *const _,
      heap_addr: ffi::heap_addr as *const _,
    });
    // extract return values
    Ok(slice::from_raw_parts(ret_vals.rets, ret_vals.num_rets))
  }
}

impl Default for NativeLoader {
  fn default() -> Self {
    Self::new()
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

impl From<Error> for NonZeroU64 {
  fn from(e: Error) -> Self {
    Self::new(match e {
      Error::Loading(_) => 1,
      Error::LibNotFound => 2,
    })
    .unwrap()
  }
}

/// FFI for native calls.
mod ffi {
  use crate::interpreter::heap::{Heap, Meta};
  use std::alloc::Layout;
  use std::ffi::c_void;

  /// Function type of native functions.
  pub type NativeFn = unsafe extern "C" fn(*const VmState) -> RetVals;

  /// Virtual machine state.
  #[repr(C)]
  pub struct VmState<'vm> {
    pub heap: &'vm mut &'vm mut dyn HeapWrapper,
    pub num_args: usize,
    pub args: *const u64,
    pub heap_alloc: *const c_void,
    pub heap_addr: *const c_void,
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
        .alloc(Layout::from_size_align(size, align).unwrap(), Meta::Raw)
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
  pub(super) fn heap_alloc(heap: &mut &mut dyn HeapWrapper, size: usize, align: usize) -> u64 {
    heap.alloc(size, align)
  }

  /// Returns the memory address of the given pointer.
  pub(super) fn heap_addr(heap: &mut &mut dyn HeapWrapper, ptr: u64) -> *mut c_void {
    heap.addr_mut(ptr) as *mut c_void
  }
}
