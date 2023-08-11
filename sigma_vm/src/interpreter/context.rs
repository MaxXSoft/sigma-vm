use crate::bytecode::insts::Inst;
use crate::bytecode::module::Module;
use crate::interpreter::gc::PotentialRoots;
use crate::interpreter::policy::Policy;
use crate::interpreter::vm::{ControlFlow, GlobalHeap};
use std::iter::Flatten;
use std::mem;
use std::slice::Iter;

/// Execution context of virtual machine.
pub struct Context<P: Policy> {
  pc: u64,
  value_stack: Vec<P::Value>,
  var_stack: Vec<Vars<P::Value>>,
  ra_stack: Vec<u64>,
}

impl<P: Policy> Context<P> {
  /// Creates a new context.
  pub fn new() -> Self {
    Self {
      pc: 0,
      value_stack: vec![],
      var_stack: vec![Vars::new()],
      ra_stack: vec![],
    }
  }

  /// Returns a reference to the value stack.
  pub fn value_stack(&self) -> &[P::Value] {
    &self.value_stack
  }

  /// Adds the given value to the value stack.
  pub fn add_value(&mut self, value: P::Value) {
    self.value_stack.push(value)
  }

  /// Adds the given pointer to the value stack.
  pub(super) fn add_ptr(&mut self, ptr: u64) {
    self.value_stack.push(P::ptr_val(ptr))
  }

  /// Resets the state of the current context.
  pub fn reset(&mut self) {
    self.pc = 0;
    self.value_stack.clear();
    self.var_stack.clear();
    self.var_stack.push(Vars::new());
    self.ra_stack.clear();
  }

  /// Returns the current PC.
  pub fn pc(&self) -> u64 {
    self.pc
  }

  /// Sets the PC to the given value.
  pub fn set_pc(&mut self, pc: u64) {
    self.pc = pc;
  }

  /// Returns potential garbage collection roots of the current context.
  pub fn proots(&self) -> PotentialRoots<P> {
    PotentialRoots {
      values: &self.value_stack,
      vars: &self.var_stack,
    }
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

  /// Pops an integer/pointer from the value stack.
  fn pop_int_ptr(&mut self) -> Result<u64, P::Error> {
    P::get_int_ptr(&self.pop()?)
  }

  /// Pops a 32-bit floating point from the value stack.
  fn pop_f32(&mut self) -> Result<f32, P::Error> {
    P::get_f32(&self.pop()?)
  }

  /// Pops a 64-bit floating point from the value stack.
  fn pop_f64(&mut self) -> Result<f64, P::Error> {
    P::get_f64(&self.pop()?)
  }

  /// Pops a pointer from the value stack.
  fn pop_ptr(&mut self) -> Result<u64, P::Error> {
    P::get_ptr(&self.pop()?)
  }

  /// Pops a untyped value from the value stack.
  fn pop_any(&mut self) -> Result<u64, P::Error> {
    Ok(P::get_any(&self.pop()?))
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

impl<P: Policy> Context<P>
where
  P::Value: Clone,
{
  /// Adds the given values to the value stack.
  pub fn add_values(&mut self, values: &[P::Value]) {
    self.value_stack.extend(values.iter().cloned())
  }

  /// Runs the virtual machine.
  pub fn run(
    &mut self,
    module: &Module,
    heap: &mut GlobalHeap<P>,
  ) -> Result<ControlFlow, P::Error> {
    loop {
      match self.run_inst(module, heap, module.insts[self.pc as usize])? {
        PcUpdate::Next => self.pc += 1,
        PcUpdate::Set(pc) => self.pc = pc,
        PcUpdate::ControlFlow(c) => return Ok(c),
      }
    }
  }

  /// Runs the current instruction.
  ///
  /// Returns `false` if the instruction requires to stop execution.
  fn run_inst(
    &mut self,
    module: &Module,
    heap: &mut GlobalHeap<P>,
    inst: Inst,
  ) -> Result<PcUpdate, P::Error> {
    /// Helper macro for manipulating stack.
    macro_rules! stack {
      (pop($v:ident: u64)) => {
        let $v = self.pop_int_ptr()?;
      };
      (pop($v:ident: _)) => {
        let $v = self.pop_any()?;
      };
      (push($v:expr, u64)) => {
        self.push_int($v);
      };
      (pop($v:ident: f32)) => {
        let $v = self.pop_f32()?;
      };
      (push($v:expr, f32)) => {
        self.push_f32($v);
      };
      (pop($v:ident: f64)) => {
        let $v = self.pop_f64()?;
      };
      (push($v:expr, f64)) => {
        self.push_f64($v);
      };
    }

    /// Helper macro for unary operations.
    macro_rules! unary {
      ($s0:ident: $ty:tt, $result:expr) => {{
        stack!(pop($s0: $ty));
        stack!(push($result, $ty));
        PcUpdate::Next
      }};
      ($s0:ident: $ty:tt, $ty2:tt: $result:expr) => {{
        stack!(pop($s0: $ty));
        stack!(push($result, $ty2));
        PcUpdate::Next
      }};
    }

    /// Helper macro for binary operations.
    macro_rules! binary {
      (($lhs:ident, $rhs:ident): $ty:tt, $result:expr) => {{
        stack!(pop($rhs: $ty));
        stack!(pop($lhs: $ty));
        stack!(push($result, $ty));
        PcUpdate::Next
      }};
      (($lhs:ident, $rhs:ident): $ty:tt, $ty2:tt: $result:expr) => {{
        stack!(pop($rhs: $ty));
        stack!(pop($lhs: $ty));
        stack!(push($result, $ty2));
        PcUpdate::Next
      }};
    }

    Ok(match inst {
      Inst::Nop => PcUpdate::Next,
      Inst::PushI(opr) => {
        self.push_int(opr as u64);
        PcUpdate::Next
      }
      Inst::PushU(opr) => {
        self.push_int(opr);
        PcUpdate::Next
      }
      Inst::Pop => {
        self.pop()?;
        PcUpdate::Next
      }
      Inst::Dup => {
        self.push(self.peek_s0()?.clone());
        PcUpdate::Next
      }
      Inst::Swap => {
        let mut s0 = self.pop()?;
        let s1 = self.peek_s0_mut()?;
        mem::swap(&mut s0, s1);
        self.push(s0);
        PcUpdate::Next
      }
      Inst::LdB => {
        let ptr = self.pop_ptr()?;
        self.push_int(heap.load::<i8>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdBU => {
        let ptr = self.pop_ptr()?;
        self.push_int(heap.load::<u8>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdH => {
        let ptr = self.pop_ptr()?;
        self.push_int(heap.load::<i16>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdHU => {
        let ptr = self.pop_ptr()?;
        self.push_int(heap.load::<u16>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdW => {
        let ptr = self.pop_ptr()?;
        self.push_int(heap.load::<i32>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdWU => {
        let ptr = self.pop_ptr()?;
        self.push_int(heap.load::<u32>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdD => {
        let ptr = self.pop_ptr()?;
        self.push_int(heap.load::<u64>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdP => {
        let ptr = self.pop_ptr()?;
        self.push_ptr(heap.load::<u64>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdBO(opr) => {
        let offset = opr * mem::size_of::<i8>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.push_int(heap.load::<i8>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdBUO(opr) => {
        let offset = opr * mem::size_of::<u8>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.push_int(heap.load::<u8>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdHO(opr) => {
        let offset = opr * mem::size_of::<i16>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.push_int(heap.load::<i16>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdHUO(opr) => {
        let offset = opr * mem::size_of::<u16>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.push_int(heap.load::<u16>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdWO(opr) => {
        let offset = opr * mem::size_of::<i32>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.push_int(heap.load::<i32>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdWUO(opr) => {
        let offset = opr * mem::size_of::<u32>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.push_int(heap.load::<u32>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdDO(opr) => {
        let offset = opr * mem::size_of::<u64>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.push_int(heap.load::<u64>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdPO(opr) => {
        let offset = opr * mem::size_of::<u64>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.push_ptr(heap.load::<u64>(ptr)?);
        PcUpdate::Next
      }
      Inst::LdV(opr) => {
        let locals = P::unwrap_val(self.var_stack.last())?;
        let var = P::unwrap_val(locals.get(opr as usize))?;
        self.push(var.clone());
        PcUpdate::Next
      }
      Inst::LdG(opr) => {
        let globals = P::unwrap_val(self.var_stack.first())?;
        let var = P::unwrap_val(globals.get(opr as usize))?;
        self.push(var.clone());
        PcUpdate::Next
      }
      Inst::LdC(opr) => {
        let c = P::unwrap_val(module.consts.get(opr as usize))?;
        self.push(heap.val_from_const(c));
        PcUpdate::Next
      }
      Inst::LaC(opr) => {
        let c = P::unwrap_val(module.consts.get(opr as usize))?;
        self.push_ptr(c.ptr());
        PcUpdate::Next
      }
      Inst::StB => {
        let v = self.pop()?;
        let ptr = self.pop_ptr()?;
        heap.store::<u8>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StH => {
        let v = self.pop()?;
        let ptr = self.pop_ptr()?;
        heap.store::<u16>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StW => {
        let v = self.pop()?;
        let ptr = self.pop_ptr()?;
        heap.store::<u32>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StD => {
        let v = self.pop()?;
        let ptr = self.pop_ptr()?;
        heap.store::<u64>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StBO(opr) => {
        let v = self.pop()?;
        let offset = opr * mem::size_of::<u8>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        heap.store::<u8>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StHO(opr) => {
        let v = self.pop()?;
        let offset = opr * mem::size_of::<u16>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        heap.store::<u16>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StWO(opr) => {
        let v = self.pop()?;
        let offset = opr * mem::size_of::<u32>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        heap.store::<u32>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StDO(opr) => {
        let v = self.pop()?;
        let offset = opr * mem::size_of::<u64>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        heap.store::<u64>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StV(opr) => {
        let v = self.pop()?;
        let locals = P::unwrap_val(self.var_stack.last_mut())?;
        locals.set_or_create(opr as usize, v);
        PcUpdate::Next
      }
      Inst::StG(opr) => {
        let v = self.pop()?;
        let globals = P::unwrap_val(self.var_stack.first_mut())?;
        globals.set_or_create(opr as usize, v);
        PcUpdate::Next
      }
      Inst::StA(opr) => {
        for index in (0..=opr as usize).rev() {
          let v = self.pop()?;
          P::unwrap_val(self.var_stack.last_mut())?.set_or_create(index, v);
        }
        PcUpdate::Next
      }
      Inst::New => {
        if heap.should_collect() {
          return Ok(PcUpdate::ControlFlow(ControlFlow::GC));
        }
        let align = self.pop_int_ptr()?;
        let size = self.pop_int_ptr()?;
        self.push_ptr(heap.alloc(size, align)?);
        PcUpdate::Next
      }
      Inst::NewO => {
        if heap.should_collect() {
          return Ok(PcUpdate::ControlFlow(ControlFlow::GC));
        }
        let obj_ptr = self.pop_ptr()?;
        heap.new_object(obj_ptr)?;
        PcUpdate::Next
      }
      Inst::NewOC(opr) => {
        if heap.should_collect() {
          return Ok(PcUpdate::ControlFlow(ControlFlow::GC));
        }
        let c = P::unwrap_val(module.consts.get(opr as usize))?;
        let obj_ptr = P::obj_ptr_from_const(c)?;
        heap.new_object(obj_ptr)?;
        PcUpdate::Next
      }
      Inst::NewA => {
        if heap.should_collect() {
          return Ok(PcUpdate::ControlFlow(ControlFlow::GC));
        }
        let len = self.pop_int_ptr()?;
        let obj_ptr = self.pop_ptr()?;
        heap.new_array(obj_ptr, len)?;
        PcUpdate::Next
      }
      Inst::NewAC(opr) => {
        if heap.should_collect() {
          return Ok(PcUpdate::ControlFlow(ControlFlow::GC));
        }
        let len = self.pop_int_ptr()?;
        let c = P::unwrap_val(module.consts.get(opr as usize))?;
        let obj_ptr = P::obj_ptr_from_const(c)?;
        heap.new_array(obj_ptr, len)?;
        PcUpdate::Next
      }
      Inst::Del => {
        let ptr = self.pop_ptr()?;
        heap.dealloc(ptr);
        PcUpdate::Next
      }
      Inst::Load => {
        let ptr = self.pop_ptr()?;
        return Ok(PcUpdate::ControlFlow(ControlFlow::LoadModule(ptr)));
      }
      Inst::LoadC(opr) => {
        let c = P::unwrap_val(module.consts.get(opr as usize))?;
        let ptr = P::str_ptr_from_const(c)?;
        return Ok(PcUpdate::ControlFlow(ControlFlow::LoadModule(ptr)));
      }
      Inst::Unload => {
        let handle = self.pop_int_ptr()?;
        return Ok(PcUpdate::ControlFlow(ControlFlow::UnloadModule(handle)));
      }
      Inst::Bz(opr) => {
        if self.pop_any()? == 0 {
          PcUpdate::Set((self.pc as i64 + opr) as u64)
        } else {
          PcUpdate::Next
        }
      }
      Inst::Bnz(opr) => {
        if self.pop_any()? != 0 {
          PcUpdate::Set((self.pc as i64 + opr) as u64)
        } else {
          PcUpdate::Next
        }
      }
      Inst::Jmp(opr) => PcUpdate::Set((self.pc as i64 + opr) as u64),
      Inst::Call(opr) => {
        self.var_stack.push(Vars::new());
        self.ra_stack.push(self.pc + 1);
        PcUpdate::Set((self.pc as i64 + opr) as u64)
      }
      Inst::CallExt => {
        let ptr = self.pop_ptr()?;
        let handle = self.pop_int_ptr()?;
        return Ok(PcUpdate::ControlFlow(ControlFlow::CallExt(handle, ptr)));
      }
      Inst::CallExtC(opr) => {
        let handle = self.pop_int_ptr()?;
        let c = P::unwrap_val(module.consts.get(opr as usize))?;
        let ptr = P::str_ptr_from_const(c)?;
        return Ok(PcUpdate::ControlFlow(ControlFlow::CallExt(handle, ptr)));
      }
      Inst::Ret => {
        let pcu = match self.ra_stack.pop() {
          Some(pc) => PcUpdate::Set(pc),
          None => return Ok(PcUpdate::ControlFlow(ControlFlow::Stop)),
        };
        self.var_stack.pop();
        pcu
      }
      Inst::Sys(_) => unimplemented!("system call"),
      Inst::Break => unimplemented!("breakpoint"),
      Inst::Not => unary!(s0: u64, !s0),
      Inst::LNot => unary!(s0: u64, (s0 == 0) as u64),
      Inst::And => binary!((lhs, rhs): u64, lhs & rhs),
      Inst::Or => binary!((lhs, rhs): u64, lhs | rhs),
      Inst::Xor => binary!((lhs, rhs): u64, lhs ^ rhs),
      Inst::Shl => binary!((lhs, rhs): u64, lhs << rhs),
      Inst::Shr => binary!((lhs, rhs): u64, lhs >> rhs),
      Inst::Sar => binary!((lhs, rhs): u64, (lhs as i64 >> rhs) as u64),
      Inst::Sext(opr) => {
        unary!(s0: u64, if opr <= 64 {
          let s = 64 - opr;
          ((s0 as i64) << s >> s) as u64
        } else {
          s0
        })
      }
      Inst::Zext(opr) => unary!(s0: u64, if opr <= 64 { s0 & !((1 << opr) - 1) } else { s0 }),
      Inst::Eq => binary!((lhs, rhs): _, u64: (lhs == rhs) as u64),
      Inst::Ne => binary!((lhs, rhs): _, u64: (lhs != rhs) as u64),
      Inst::Lt => binary!((lhs, rhs): u64, ((lhs as i64) < rhs as i64) as u64),
      Inst::Le => binary!((lhs, rhs): u64, (lhs as i64 <= rhs as i64) as u64),
      Inst::Gt => binary!((lhs, rhs): u64, (lhs as i64 > rhs as i64) as u64),
      Inst::Ge => binary!((lhs, rhs): u64, (lhs as i64 >= rhs as i64) as u64),
      Inst::LtU => binary!((lhs, rhs): u64, (lhs < rhs) as u64),
      Inst::LeU => binary!((lhs, rhs): u64, (lhs <= rhs) as u64),
      Inst::GtU => binary!((lhs, rhs): u64, (lhs > rhs) as u64),
      Inst::GeU => binary!((lhs, rhs): u64, (lhs >= rhs) as u64),
      Inst::Neg => unary!(s0: u64, !s0 + 1),
      Inst::Add => {
        let rhs = self.pop()?;
        let lhs = self.pop()?;
        let sum = P::get_int_ptr(&lhs)?.wrapping_add(P::get_int_ptr(&rhs)?);
        if P::ptr_or_none(&lhs).is_some() ^ P::ptr_or_none(&rhs).is_some() {
          self.push_ptr(sum);
        } else {
          self.push_int(sum);
        }
        PcUpdate::Next
      }
      Inst::Sub => {
        let rhs = self.pop()?;
        let lhs = self.pop()?;
        let sub = P::get_int_ptr(&lhs)?.wrapping_sub(P::get_int_ptr(&rhs)?);
        if P::ptr_or_none(&lhs).is_some() {
          self.push_ptr(sub);
        } else {
          self.push_int(sub);
        }
        PcUpdate::Next
      }
      Inst::Mul => binary!((lhs, rhs): u64, lhs.wrapping_mul(rhs)),
      Inst::Div => binary!((lhs, rhs): u64, {
        P::check_div(rhs)?;
        (lhs as i64).wrapping_div(rhs as i64) as u64
      }),
      Inst::DivU => binary!((lhs, rhs): u64, {
        P::check_div(rhs)?;
        lhs / rhs
      }),
      Inst::Mod => binary!((lhs, rhs): u64, {
        P::check_div(rhs)?;
        (lhs as i64).wrapping_rem(rhs as i64) as u64
      }),
      Inst::ModU => binary!((lhs, rhs): u64, {
        P::check_div(rhs)?;
        lhs % rhs
      }),
      Inst::LtF => binary!((lhs, rhs): f32, u64: (lhs < rhs) as u64),
      Inst::LeF => binary!((lhs, rhs): f32, u64: (lhs <= rhs) as u64),
      Inst::GtF => binary!((lhs, rhs): f32, u64: (lhs > rhs) as u64),
      Inst::GeF => binary!((lhs, rhs): f32, u64: (lhs >= rhs) as u64),
      Inst::NegF => unary!(s0: f32, -s0),
      Inst::AddF => binary!((lhs, rhs): f32, lhs + rhs),
      Inst::SubF => binary!((lhs, rhs): f32, lhs - rhs),
      Inst::MulF => binary!((lhs, rhs): f32, lhs * rhs),
      Inst::DivF => binary!((lhs, rhs): f32, lhs / rhs),
      Inst::ModF => binary!((lhs, rhs): f32, lhs % rhs),
      Inst::LtD => binary!((lhs, rhs): f64, u64: (lhs < rhs) as u64),
      Inst::LeD => binary!((lhs, rhs): f64, u64: (lhs <= rhs) as u64),
      Inst::GtD => binary!((lhs, rhs): f64, u64: (lhs > rhs) as u64),
      Inst::GeD => binary!((lhs, rhs): f64, u64: (lhs >= rhs) as u64),
      Inst::NegD => unary!(s0: f64, -s0),
      Inst::AddD => binary!((lhs, rhs): f64, lhs + rhs),
      Inst::SubD => binary!((lhs, rhs): f64, lhs - rhs),
      Inst::MulD => binary!((lhs, rhs): f64, lhs * rhs),
      Inst::DivD => binary!((lhs, rhs): f64, lhs / rhs),
      Inst::ModD => binary!((lhs, rhs): f64, lhs % rhs),
      Inst::I2F => unary!(s0: u64, f32: s0 as f32),
      Inst::I2D => unary!(s0: u64, f64: s0 as f64),
      Inst::F2I => unary!(s0: f32, u64: s0 as u64),
      Inst::F2D => unary!(s0: f32, f64: s0 as f64),
      Inst::D2I => unary!(s0: f64, u64: s0 as u64),
      Inst::D2F => unary!(s0: f64, f32: s0 as f32),
      Inst::ITF => unary!(s0: u64, f32: unsafe { *(&s0 as *const _ as *const f32) }),
      Inst::ITD => unary!(s0: u64, f64: unsafe { *(&s0 as *const _ as *const f64) }),
    })
  }
}

impl<P: Policy> Default for Context<P> {
  fn default() -> Self {
    Self::new()
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
  pub fn set_or_create(&mut self, index: usize, v: V) {
    if let Some(var) = self.vars.get_mut(index) {
      *var = Some(v);
    } else {
      self.vars.resize_with(index + 1, || None);
      self.vars[index] = Some(v);
    }
  }

  /// Returns an iterator of all variables.
  pub fn iter(&self) -> Flatten<Iter<Option<V>>> {
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

/// PC update actions.
enum PcUpdate {
  Next,
  Set(u64),
  ControlFlow(ControlFlow),
}
