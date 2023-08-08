pub mod consts;
pub mod insts;
pub mod reader;
pub mod writer;

/// Magic number of the bytecode file.
const MAGIC: [u8; 4] = [b'S', b'g', b'm', b'a'];

/// Current version of the bytecode file.
const VERSION: [u64; 3] = [
  crate::utils::str_to_u64(env!("CARGO_PKG_VERSION_MAJOR")),
  crate::utils::str_to_u64(env!("CARGO_PKG_VERSION_MINOR")),
  crate::utils::str_to_u64(env!("CARGO_PKG_VERSION_PATCH")),
];
