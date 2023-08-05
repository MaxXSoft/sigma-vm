pub mod consts;
pub mod insts;
pub mod reader;
pub mod writer;

/// Magic number of the bytecode file.
const MAGIC: [u8; 4] = [b'S', b'g', b'm', b'a'];
