use crate::bytecode::consts::{Array, Str};
use std::collections::HashMap;

/// Export information.
pub type ExportInfo = HashMap<String, PcRets>;

/// Export information entry.
///
/// With function's program counter, number of returned values,
/// and a string ([`Str`]) of function name.
#[repr(C)]
#[derive(Debug)]
pub struct Export<Bytes: ?Sized + Array<u8>> {
  pub pc_rets: PcRets,
  pub name: Str<Bytes>,
}

/// Pair of function's program counter and number of returned values.
#[repr(C)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PcRets {
  pub pc: u64,
  pub num_rets: u64,
}
