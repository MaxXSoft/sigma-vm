use crate::utils::impl_try_from_int;
use std::collections::HashMap;
use std::path::PathBuf;

/// Module loader for dynamically loading modules at runtime.
pub struct Loader {
  search_paths: Vec<PathBuf>,
  resolved_paths: HashMap<PathBuf, u32>,
  loaded: HashMap<Source, ()>, // TODO
}

/// Source identifier of the loaded module.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Source {
  kind: SourceKind,
  id: u32,
}

impl From<Source> for u64 {
  fn from(source: Source) -> Self {
    ((source.kind as u64) << 32) | source.id as u64
  }
}

impl TryFrom<u64> for Source {
  type Error = ();

  fn try_from(value: u64) -> Result<Self, Self::Error> {
    Ok(Self {
      kind: ((value >> 32) as u32).try_into()?,
      id: value as u32,
    })
  }
}

/// Helper macro for defining kind of the module source.
macro_rules! source_kind {
  ($($(#[$a:meta])* $kind:ident),+ $(,)?) => {
    /// Kind of the module source.
    #[repr(u32)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub enum SourceKind {
      $($(#[$a])* $kind),+
    }

    impl_try_from_int! {
      impl TryFrom<u32> for SourceKind {
        $($kind),+
      }
    }
  };
}

source_kind! {
  /// Module is loaded from file.
  File,
  /// Module is loaded from memory.
  Memory,
}
