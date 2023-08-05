mod consts;
mod insts;
mod reader;
mod writer;

/// Magic number of the bytecode file.
pub const MAGIC: [u8; 4] = [b'S', b'g', b'm', b'a'];
