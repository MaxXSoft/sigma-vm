use crate::bytecode::consts::{Array, Str};

/// Export information.
///
/// With function's program counter, number of returned values,
/// and a string ([`Str`]) of function name.
#[repr(C)]
#[derive(Debug)]
pub struct Export<Bytes: ?Sized + Array<u8>> {
  pub pc: u64,
  pub num_rets: u64,
  pub name: Str<Bytes>,
}
