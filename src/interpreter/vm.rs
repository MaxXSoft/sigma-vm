use crate::bytecode::consts::Const;
use crate::bytecode::insts::Inst;

/// Virtual machine for running bytecode.
pub struct VM {
  consts: Box<[Const]>,
  insts: Box<[Inst]>,
  pc: u64,
  value_stack: Vec<Value>,
  local_stack: Vec<Vars>,
  globals: Vars,
}

impl VM {
  /// Creates a new virtual machine from the given constants and instructions.
  pub fn new(consts: Box<[Const]>, insts: Box<[Inst]>) -> Self {
    Self {
      consts,
      insts,
      pc: 0,
      value_stack: vec![],
      local_stack: vec![],
      globals: Default::default(),
    }
  }
}

/// Value.
struct Value {
  is_ptr: bool,
  value: u64,
}

/// Variable storage.
#[derive(Default)]
struct Vars {
  vars: Vec<Value>,
}
