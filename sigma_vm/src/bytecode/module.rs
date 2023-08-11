use crate::bytecode::consts::HeapConst;
use crate::bytecode::export::{CallSite, ExportInfo};
use crate::bytecode::insts::Inst;

/// Module, contains all static data in a bytecode file,
/// including constants, instructions, etc.
#[derive(Debug)]
pub struct Module {
  pub(crate) consts: Box<[HeapConst]>,
  pub(crate) exports: ExportInfo,
  pub(crate) insts: Box<[Inst]>,
}

impl Module {
  /// Returns a reference to the constant pool.
  pub fn consts(&self) -> &[HeapConst] {
    &self.consts
  }

  /// Returns a reference to the call site information of the given function.
  pub fn call_site(&self, name: &str) -> Option<&CallSite> {
    self.exports.get(name)
  }

  /// Returns a reference to the instruction list.
  pub fn insts(&self) -> &[Inst] {
    &self.insts
  }
}
