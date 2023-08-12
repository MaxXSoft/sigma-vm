use crate::bytecode::consts::Const;
use crate::bytecode::export::ExportInfo;
use crate::bytecode::insts::Inst;
use crate::bytecode::module::Module;
use crate::bytecode::reader::{Error as ReaderError, Reader};
use crate::interpreter::heap::Heap;
use std::collections::HashMap;
use std::fmt;
use std::io::Error as IoError;
use std::path::{Path, PathBuf};

/// Module loader for dynamically loading modules at runtime.
#[derive(Debug, Default)]
pub struct Loader {
  search_paths: Vec<PathBuf>,
  resolved_paths: HashMap<PathBuf, u32>,
  loaded_mods: HashMap<Source, Module>,
  next_file_id: u32,
  next_mem_id: u32,
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
  pub fn load_from_path<P, H>(&mut self, path: P, heap: &mut H) -> Result<Source, Error>
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
    if let Some(id) = self.resolved_paths.get(&final_path) {
      return Ok(Source::File(*id));
    }
    // read bytecode from the path
    let mut reader = Reader::from_path(final_path.clone()).map_err(Error::IO)?;
    reader.read().map_err(Error::Reader)?;
    // add to loaded modules
    let id = self.next_file_id;
    self.next_file_id += 1;
    let source = Source::File(id);
    self.resolved_paths.insert(final_path, id);
    self.loaded_mods.insert(source, reader.into_module(heap));
    Ok(source)
  }

  /// Loads a module from the given bytes.
  pub fn load_from_bytes<H>(&mut self, bytes: &[u8], heap: &mut H) -> Result<Source, Error>
  where
    H: Heap,
  {
    let source = Source::Memory(self.next_mem_id);
    self.next_mem_id += 1;
    // read bytecode from bytes
    let mut reader = Reader::from(bytes);
    reader.read().map_err(Error::Reader)?;
    // add to loaded modules
    self.loaded_mods.insert(source, reader.into_module(heap));
    Ok(source)
  }

  /// Loads a module from the standard input.
  pub fn load_from_stdin<H>(&mut self, heap: &mut H) -> Result<Source, Error>
  where
    H: Heap,
  {
    // read bytecode from bytes
    let mut reader = Reader::from_stdin();
    reader.read().map_err(Error::Reader)?;
    // add to loaded modules
    let source = Source::Stdin;
    self.loaded_mods.insert(source, reader.into_module(heap));
    Ok(source)
  }

  /// Creates a module from the given constants and instructions.
  pub fn new_module<H>(
    &mut self,
    consts: Box<[Const]>,
    exports: ExportInfo,
    insts: Box<[Inst]>,
    heap: &mut H,
  ) -> Result<Source, Error>
  where
    H: Heap,
  {
    let source = Source::Memory(self.next_mem_id);
    self.next_mem_id += 1;
    // create module
    let module = Module {
      consts: consts
        .into_vec()
        .into_iter()
        .map(|c| c.into_heap_const(heap))
        .collect(),
      exports,
      insts,
    };
    // add to loaded modules
    self.loaded_mods.insert(source, module);
    Ok(source)
  }

  /// Unloads a module by the given source.
  pub fn unload(&mut self, source: Source) -> Option<Module> {
    if let Source::File(id) = source {
      self.resolved_paths.retain(|_, v| *v != id);
    }
    self.loaded_mods.remove(&source)
  }

  /// Unloads all loaded modules.
  pub fn unload_all(&mut self) {
    self.resolved_paths.clear();
    self.loaded_mods.clear();
    self.next_mem_id = 0;
  }

  /// Returns a loaded module by the given source.
  pub fn module(&self, source: Source) -> Option<&Module> {
    self.loaded_mods.get(&source)
  }
}

/// Source identifier of the loaded module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Source {
  /// Invalid source.
  Invalid,
  /// Module is loaded from file.
  File(u32),
  /// Module is loaded from memory.
  Memory(u32),
  /// Module is loaded from standard input.
  Stdin,
}

impl From<Source> for u64 {
  fn from(source: Source) -> Self {
    match source {
      Source::Invalid => 0,
      Source::File(id) => (1 << 32) | id as u64,
      Source::Memory(id) => (2 << 32) | id as u64,
      Source::Stdin => 3 << 32,
    }
  }
}

impl From<u64> for Source {
  fn from(value: u64) -> Self {
    match value >> 32 {
      1 => Self::File(value as u32),
      2 => Self::Memory(value as u32),
      3 if value as u32 == 0 => Self::Stdin,
      _ => Self::Invalid,
    }
  }
}

impl<E> From<Result<Source, E>> for Source {
  fn from(result: Result<Source, E>) -> Self {
    result.unwrap_or(Self::Invalid)
  }
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
