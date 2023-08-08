use crate::bytecode::consts::{Const, HeapConst};
use crate::bytecode::insts::Inst;
use crate::bytecode::reader::Reader;
use crate::interpreter::policy::Policy;
use std::slice::Iter;

/// Virtual machine for running bytecode.
pub struct VM<P: Policy> {
  policy: P,
  consts: Box<[HeapConst]>,
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
    let mut heap = policy.new_heap();
    let consts = consts
      .into_vec()
      .into_iter()
      .map(|c| c.into_heap_const(&mut heap))
      .collect();
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
#[derive(Debug)]
pub struct Vars<V> {
  vars: Vec<V>,
}

impl<V> Vars<V> {
  /// Creates a new variable storage.
  fn new() -> Self {
    Self { vars: vec![] }
  }

  /// Returns an iterator of all variables.
  pub fn iter<'a>(&'a self) -> Iter<'a, V> {
    self.vars.iter()
  }
}

impl<'a, V> IntoIterator for &'a Vars<V> {
  type Item = &'a V;
  type IntoIter = Iter<'a, V>;

  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}
