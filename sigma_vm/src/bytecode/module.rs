use crate::bytecode::consts::HeapConst;
use crate::bytecode::insts::Inst;

/// Module, contains all static data in a bytecode file,
/// including constants, instructions, etc.
#[derive(Debug)]
pub struct Module {
  pub(in crate::bytecode) consts: Box<[HeapConst]>,
  pub(in crate::bytecode) insts: Box<[Inst]>,
}

impl Module {
  /// Returns a reference to the constant pool.
  pub fn consts(&self) -> &[HeapConst] {
    &self.consts
  }

  /// Returns a reference to the instruction list.
  pub fn insts(&self) -> &[Inst] {
    &self.insts
  }
}
