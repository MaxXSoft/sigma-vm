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
    let id = self.resolved_paths.len() as u32;
    match self.resolved_paths.get(&final_path) {
      Some(id) => return Ok(Source::File(*id)),
      None => self.resolved_paths.insert(final_path.clone(), id),
    };
    // read bytecode from the path
    let mut reader = Reader::from_path(final_path).map_err(Error::IO)?;
    reader.read().map_err(Error::Reader)?;
    // add to loaded modules
    let source = Source::File(id);
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
      Source::File(id) => (0 << 32) | id as u64,
      Source::Memory(id) => (1 << 32) | id as u64,
      Source::Stdin => 2 << 32,
    }
  }
}

impl TryFrom<u64> for Source {
  type Error = ();

  fn try_from(value: u64) -> Result<Self, Self::Error> {
    match value >> 32 {
      0 => Ok(Self::File(value as u32)),
      1 => Ok(Self::Memory(value as u32)),
      2 if value as u32 == 0 => Ok(Self::Stdin),
      _ => Err(()),
    }
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
