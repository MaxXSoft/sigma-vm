use crate::bytecode::consts::{Array, Str};
use std::collections::HashMap;
use std::num::NonZeroU64;

/// Exported call site information.
pub type ExportInfo = HashMap<String, CallSite>;

/// Export information.
///
/// With call site information and a string ([`Str`]) of function name.
#[repr(C)]
#[derive(Debug)]
pub struct Export<Bytes: ?Sized + Array<u8>> {
  pub call_site: CallSite,
  pub name: Str<Bytes>,
}

/// Exported call site.
///
/// With function's program counter, number of arguments
/// and number of returned values.
#[repr(C)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallSite {
  pub pc: u64,
  pub num_args: NumArgs,
  pub num_rets: u64,
}

/// Number of arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumArgs {
  /// Variadic, the actual argument number
  /// will be placed on the top of the stack.
  Variadic,
  /// Number of arguments plus one.
  PlusOne(NonZeroU64),
}

impl From<u64> for NumArgs {
  fn from(n: u64) -> Self {
    NonZeroU64::new(n)
      .map(Self::PlusOne)
      .unwrap_or(Self::Variadic)
  }
}

impl From<NumArgs> for u64 {
  fn from(num_args: NumArgs) -> Self {
    match num_args {
      NumArgs::Variadic => 0,
      NumArgs::PlusOne(n) => n.get(),
    }
  }
}
