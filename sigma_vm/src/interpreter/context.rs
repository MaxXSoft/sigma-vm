use crate::interpreter::policy::Policy;
use crate::interpreter::vm::Vars;
use std::marker::PhantomData;

/// Execution context of virtual machine.
pub struct Context<P: Policy> {
  policy: PhantomData<P>,
  pc: u64,
  value_stack: Vec<P::Value>,
  var_stack: Vec<Vars<P::Value>>,
  ra_stack: Vec<u64>,
}
