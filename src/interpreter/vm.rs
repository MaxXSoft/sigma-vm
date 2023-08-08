use crate::bytecode::consts::{Const, HeapConst};
use crate::bytecode::insts::Inst;
use crate::bytecode::reader::Reader;
use crate::interpreter::policy::Policy;
use std::iter::Flatten;
use std::mem;
use std::slice::Iter;

/// Virtual machine for running bytecode.
pub struct VM<P: Policy> {
  policy: P,
  consts: Box<[HeapConst]>,
  insts: Box<[Inst]>,
  pc: u64,
  value_stack: Vec<P::Value>,
  local_stack: Vec<Vars<P::Value>>,
  ra_stack: Vec<u64>,
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
      ra_stack: vec![],
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

impl<P: Policy> VM<P>
where
  P::Value: Clone,
{
  /// Runs the virtual machine.
  pub fn run(&mut self) -> Result<(), P::Error> {
    loop {
      match self.run_inst(self.insts[self.pc as usize])? {
        InstAction::NextPC => self.pc += 1,
        InstAction::SetPC(pc) => self.pc = pc,
        InstAction::Stop => return Ok(()),
      }
    }
  }

  /// Runs the current instruction.
  ///
  /// Returns `false` if the instruction requires to stop execution.
  fn run_inst(&mut self, inst: Inst) -> Result<InstAction, P::Error> {
    Ok(match inst {
      Inst::Nop => InstAction::NextPC,
      Inst::PushI(opr) => {
        self.push_int(opr as u64);
        InstAction::NextPC
      }
      Inst::PushU(opr) => {
        self.push_int(opr);
        InstAction::NextPC
      }
      Inst::Pop => {
        self.pop()?;
        InstAction::NextPC
      }
      Inst::Dup => {
        self.push(self.peek_s0()?.clone());
        InstAction::NextPC
      }
      Inst::Swap => {
        let mut s0 = self.pop()?;
        let s1 = self.peek_s0_mut()?;
        mem::swap(&mut s0, s1);
        self.push(s0);
        InstAction::NextPC
      }
      _ => todo!(),
    })
  }

  /// Pushes a value to the value stack.
  fn push(&mut self, v: P::Value) {
    self.value_stack.push(v)
  }

  /// Pushes an integer to the value stack.
  fn push_int(&mut self, i: u64) {
    self.push(P::int_val(i))
  }

  /// Pushes a 32-bit floating point to the value stack.
  fn push_f32(&mut self, f: f32) {
    self.push(P::f32_val(f))
  }

  /// Pushes a 64-bit floating point to the value stack.
  fn push_f64(&mut self, f: f64) {
    self.push(P::f64_val(f))
  }

  /// Pushes a pointer to the value stack.
  fn push_ptr(&mut self, p: u64) {
    self.push(P::ptr_val(p))
  }

  /// Pops a value from the value stack.
  fn pop(&mut self) -> Result<P::Value, P::Error> {
    P::unwrap_val(self.value_stack.pop())
  }

  /// Pops an integer from the value stack.
  fn pop_int(&mut self) -> Result<u64, P::Error> {
    self.pop().and_then(|v| P::get_int(&v))
  }

  /// Pops a 32-bit floating point from the value stack.
  fn pop_f32(&mut self) -> Result<f32, P::Error> {
    self.pop().and_then(|v| P::get_f32(&v))
  }

  /// Pops a 64-bit floating point from the value stack.
  fn pop_f64(&mut self) -> Result<f64, P::Error> {
    self.pop().and_then(|v| P::get_f64(&v))
  }

  /// Peeks the value at the given index in the value stack.
  fn peek(&self, index: usize) -> Result<&P::Value, P::Error> {
    P::unwrap_val(self.value_stack.get(index))
  }

  /// Peeks the mutable value at the given index in the value stack.
  fn peek_mut(&mut self, index: usize) -> Result<&mut P::Value, P::Error> {
    P::unwrap_val(self.value_stack.get_mut(index))
  }

  /// Peeks the last value in the value stack.
  fn peek_s0(&self) -> Result<&P::Value, P::Error> {
    P::unwrap_val(self.value_stack.last())
  }

  /// Peeks the last mutable value in the value stack.
  fn peek_s0_mut(&mut self) -> Result<&mut P::Value, P::Error> {
    P::unwrap_val(self.value_stack.last_mut())
  }
}

/// Variable storage.
#[derive(Debug)]
pub struct Vars<V> {
  vars: Vec<Option<V>>,
}

impl<V> Vars<V> {
  /// Creates a new variable storage.
  fn new() -> Self {
    Self { vars: vec![] }
  }

  /// Returns a reference of the variable at the given index,
  /// or [`None`] if no such variable.
  pub fn get(&self, index: usize) -> Option<&V> {
    match self.vars.get(index) {
      Some(v) => v.as_ref(),
      None => None,
    }
  }

  /// Returns a mutable reference of the variable at the given index,
  /// or [`None`] if no such variable.
  pub fn get_mut(&mut self, index: usize) -> Option<&mut V> {
    match self.vars.get_mut(index) {
      Some(v) => v.as_mut(),
      None => None,
    }
  }

  /// Sets the variable at the given index to the given value.
  /// Creates a new variable with the value if no such variable.
  pub fn set_or_create(&mut self, index: usize, value: V) {
    if let Some(v) = self.get_mut(index) {
      *v = value;
    } else {
      self.vars.resize_with(index + 1, || None);
      self.vars[index] = Some(value);
    }
  }

  /// Returns an iterator of all variables.
  pub fn iter<'a>(&'a self) -> Flatten<Iter<'a, Option<V>>> {
    self.vars.iter().flatten()
  }
}

impl<'a, V> IntoIterator for &'a Vars<V> {
  type Item = &'a V;
  type IntoIter = Flatten<Iter<'a, Option<V>>>;

  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

/// Action of an instruction.
enum InstAction {
  NextPC,
  SetPC(u64),
  Stop,
}
