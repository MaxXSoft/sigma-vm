use crate::bytecode::module::{Module, StaticModule};
use crate::bytecode::reader::{Error as ReaderError, Reader};
use crate::interpreter::heap::{Heap, Meta, Ptr};
use std::alloc::Layout;
use std::collections::HashMap;
use std::io::Error as IoError;
use std::path::{Path, PathBuf};
use std::{fmt, mem};

/// Module loader for dynamically loading modules at runtime.
#[derive(Debug, Default)]
pub struct Loader {
  search_paths: Vec<PathBuf>,
  resolved_paths: HashMap<PathBuf, Ptr>,
  loaded_mods: HashMap<Ptr, Module>,
}

impl Loader {
  /// Creates a new loader.
  pub fn new() -> Self {
    Self::default()
  }

  /// Adds the given path to search paths.
  pub fn add_search_path<P>(&mut self, path: P)
  where
    P: AsRef<Path>,
  {
    self.search_paths.push(path.as_ref().into())
  }

  /// Loads a module from the given path.
  pub fn load_from_path<P, H>(&mut self, heap: &mut H, path: P) -> Result<Ptr, Error>
  where
    P: AsRef<Path>,
    H: Heap,
  {
    // get the final path
    let path = path.as_ref();
    let final_path = if path.is_absolute() {
      path.exists().then(|| path.into())
    } else {
      self.search_paths.iter().find_map(|p| {
        let full = p.join(path);
        full.exists().then_some(full)
      })
    }
    .ok_or(Error::InvalidPath(path.into()))?;
    // update resolved path, return if the module has already been loaded
    if let Some(handle) = self.resolved_paths.get(&final_path) {
      return Ok(*handle);
    }
    // read bytecode from the path
    let mut reader = Reader::from_path(final_path.clone()).map_err(Error::IO)?;
    reader.read().map_err(Error::Reader)?;
    // create a new handle
    let handle = Self::new_handle(heap, Source::File);
    // add to loaded modules
    self.resolved_paths.insert(final_path, handle);
    self
      .loaded_mods
      .insert(handle, StaticModule::from(reader).into_module(heap));
    Ok(handle)
  }

  /// Loads a module from the given bytes.
  pub fn load_from_bytes<H>(&mut self, heap: &mut H, bytes: &[u8]) -> Result<Ptr, Error>
  where
    H: Heap,
  {
    // read bytecode from bytes
    let mut reader = Reader::from(bytes);
    reader.read().map_err(Error::Reader)?;
    // add to loaded modules
    let handle = Self::new_handle(heap, Source::Other);
    self
      .loaded_mods
      .insert(handle, StaticModule::from(reader).into_module(heap));
    Ok(handle)
  }

  /// Loads a module from the standard input.
  pub fn load_from_stdin<H>(&mut self, heap: &mut H) -> Result<Ptr, Error>
  where
    H: Heap,
  {
    // read bytecode from bytes
    let mut reader = Reader::from_stdin();
    reader.read().map_err(Error::Reader)?;
    // add to loaded modules
    let handle = Self::new_handle(heap, Source::Other);
    self
      .loaded_mods
      .insert(handle, StaticModule::from(reader).into_module(heap));
    Ok(handle)
  }

  /// Creates a module from the given static module.
  pub fn new_module<H>(&mut self, heap: &mut H, module: StaticModule) -> Result<Ptr, Error>
  where
    H: Heap,
  {
    let handle = Self::new_handle(heap, Source::Other);
    self.loaded_mods.insert(handle, module.into_module(heap));
    Ok(handle)
  }

  /// Unloads a module by the given handle, also deallocates the handle.
  pub fn unload<H>(&mut self, heap: &mut H, handle: Ptr) -> Option<Module>
  where
    H: Heap,
  {
    let module = self.loaded_mods.remove(&handle);
    if module.is_some() {
      if Self::source(heap, handle) == Source::File {
        self.resolved_paths.retain(|_, h| *h != handle);
      }
      heap.dealloc(handle);
    }
    module
  }

  /// Unloads all loaded modules, the handles will not be deallocated.
  pub(super) fn unload_all(&mut self) {
    self.resolved_paths.clear();
    self.loaded_mods.clear();
  }

  /// Returns a loaded module by the given handle.
  pub fn module(&self, handle: Ptr) -> Option<&Module> {
    self.loaded_mods.get(&handle)
  }

  /// Creates a new handle.
  fn new_handle<H>(heap: &mut H, source: Source) -> Ptr
  where
    H: Heap,
  {
    let handle = heap.alloc(
      Layout::from_size_align(mem::size_of_val(&source), mem::align_of_val(&source)).unwrap(),
      Meta::Module,
    );
    unsafe { *(heap.addr_mut(handle) as *mut Source) = source };
    handle
  }

  /// Returns the source of the given handle.
  fn source<H>(heap: &H, handle: Ptr) -> Source
  where
    H: Heap,
  {
    unsafe { *(heap.addr(handle) as *const Source) }
  }

  /// Returns information of the given handle as a string.
  ///
  /// This method can be used to print the stack trace.
  pub(super) fn module_info(&self, handle: Ptr) -> String {
    let path = self
      .resolved_paths
      .iter()
      .find_map(|(p, h)| (*h == handle).then_some(p));
    if let Some(path) = path {
      format!("module {}", path.display())
    } else {
      format!("module 0x{:x}", u64::from(handle))
    }
  }
}

/// Source identifier of the loaded module.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Source {
  /// Module is loaded from file.
  File,
  /// Module is loaded from other sources.
  Other,
}

/// Error for the module loader.
#[derive(Debug)]
pub enum Error {
  /// Invalid path.
  InvalidPath(PathBuf),
  /// I/O error.
  IO(IoError),
  /// Bytecode reader error.
  Reader(ReaderError),
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::InvalidPath(p) => write!(f, "invalid path: {}", p.display()),
      Self::IO(e) => write!(f, "{e}"),
      Self::Reader(e) => write!(f, "{e}"),
    }
  }
}
