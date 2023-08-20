use crate::bytecode::consts::{Const, HeapConst};
use crate::bytecode::export::{CallSite, ExportInfo};
use crate::bytecode::insts::Inst;
use crate::interpreter::heap::Heap;

/// Module, contains all static data in a bytecode file,
/// including constants, instructions, etc.
///
/// [`Module`] can be executed directly by the virtual machine.
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

/// Static module, which can not be executed directly by the virtual machine
/// without converting into a [`Module`].
pub struct StaticModule {
  pub consts: Box<[Const]>,
  pub exports: ExportInfo,
  pub insts: Box<[Inst]>,
  pub custom: Box<[u8]>,
}

impl StaticModule {
  /// Converts the current static module into a [`Module`].
  pub fn into_module<H>(self, heap: &mut H) -> Module
  where
    H: Heap,
  {
    Module {
      consts: self
        .consts
        .into_vec()
        .into_iter()
        .map(|c| c.into_heap_const(heap))
        .collect(),
      exports: self.exports,
      insts: self.insts,
    }
  }
}
