use crate::bytecode::consts::Const;
use crate::bytecode::insts::Inst;
use crate::bytecode::reader::Reader;
use crate::interpreter::policy::Policy;

/// Virtual machine for running bytecode.
pub struct VM<P: Policy> {
  policy: P,
  consts: Box<[Const]>,
  insts: Box<[Inst]>,
  pc: u64,
  value_stack: Vec<P::Value>,
  local_stack: Vec<Vars<P::Value>>,
  globals: Vars<P::Value>,
  heap: P::Heap,
  gc: P::GarbageCollector,
}

impl<P: Policy> VM<P> {
  /// Creates a new virtual machine from the given constants and instructions.
  pub fn new(policy: P, consts: Box<[Const]>, insts: Box<[Inst]>) -> Self {
    let heap = policy.new_heap();
    let gc = policy.new_gc();
    Self {
      policy,
      consts,
      insts,
      pc: 0,
      value_stack: vec![],
      local_stack: vec![],
      globals: Vars::new(),
      heap,
      gc,
    }
  }

  /// Creates a new virtual machine from the given [`Reader`].
  pub fn from_reader<R>(policy: P, reader: Reader<R>) -> Self {
    let (consts, insts) = reader.into_consts_insts();
    Self::new(policy, consts, insts)
  }
}

/// Variable storage.
struct Vars<V> {
  vars: Vec<V>,
}

impl<V> Vars<V> {
  /// Creates a new variable storage.
  fn new() -> Self {
    Self { vars: vec![] }
  }
}
