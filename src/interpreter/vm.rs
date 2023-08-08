use crate::bytecode::consts::{Const, HeapConst};
use crate::bytecode::insts::Inst;
use crate::bytecode::reader::Reader;
use crate::interpreter::heap::{Heap, Obj, ObjKind};
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
  var_stack: Vec<Vars<P::Value>>,
  ra_stack: Vec<u64>,
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
      var_stack: vec![Vars::new()],
      ra_stack: vec![],
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
        InstAction::NextPC
      }};
      ($s0:ident: $ty:tt, $ty2:tt: $result:expr) => {{
        stack!(pop($s0: $ty));
        stack!(push($result, $ty2));
        InstAction::NextPC
      }};
    }

    /// Helper macro for binary operations.
    macro_rules! binary {
      (($lhs:ident, $rhs:ident): $ty:tt, $result:expr) => {{
        stack!(pop($rhs: $ty));
        stack!(pop($lhs: $ty));
        stack!(push($result, $ty));
        InstAction::NextPC
      }};
      (($lhs:ident, $rhs:ident): $ty:tt, $ty2:tt: $result:expr) => {{
        stack!(pop($rhs: $ty));
        stack!(pop($lhs: $ty));
        stack!(push($result, $ty2));
        InstAction::NextPC
      }};
    }

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
      Inst::LdB => {
        let ptr = self.pop_ptr()?;
        self.load::<i8>(ptr)?
      }
      Inst::LdBU => {
        let ptr = self.pop_ptr()?;
        self.load::<u8>(ptr)?
      }
      Inst::LdH => {
        let ptr = self.pop_ptr()?;
        self.load::<i16>(ptr)?
      }
      Inst::LdHU => {
        let ptr = self.pop_ptr()?;
        self.load::<u16>(ptr)?
      }
      Inst::LdW => {
        let ptr = self.pop_ptr()?;
        self.load::<i32>(ptr)?
      }
      Inst::LdWU => {
        let ptr = self.pop_ptr()?;
        self.load::<u32>(ptr)?
      }
      Inst::LdD => {
        let ptr = self.pop_ptr()?;
        self.load::<u64>(ptr)?
      }
      Inst::LdP => {
        let ptr = self.pop_ptr()?;
        self.load_ptr(ptr)?
      }
      Inst::LdBO(opr) => {
        let offset = opr * mem::size_of::<i8>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.load::<i8>(ptr)?
      }
      Inst::LdBUO(opr) => {
        let offset = opr * mem::size_of::<u8>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.load::<u8>(ptr)?
      }
      Inst::LdHO(opr) => {
        let offset = opr * mem::size_of::<i16>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.load::<i16>(ptr)?
      }
      Inst::LdHUO(opr) => {
        let offset = opr * mem::size_of::<u16>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.load::<u16>(ptr)?
      }
      Inst::LdWO(opr) => {
        let offset = opr * mem::size_of::<i32>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.load::<i32>(ptr)?
      }
      Inst::LdWUO(opr) => {
        let offset = opr * mem::size_of::<u32>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.load::<u32>(ptr)?
      }
      Inst::LdDO(opr) => {
        let offset = opr * mem::size_of::<u64>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.load::<u64>(ptr)?
      }
      Inst::LdPO(opr) => {
        let offset = opr * mem::size_of::<u64>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.load_ptr(ptr)?
      }
      Inst::LdV(opr) => {
        let var = P::unwrap_val(self.var_stack.last().unwrap().get(opr as usize))?;
        self.push(var.clone());
        InstAction::NextPC
      }
      Inst::LdG(opr) => {
        let var = P::unwrap_val(self.var_stack.first().unwrap().get(opr as usize))?;
        self.push(var.clone());
        InstAction::NextPC
      }
      Inst::LdC(opr) => {
        let c = P::unwrap_val(self.consts.get(opr as usize))?;
        self.push(P::val_from_const(&self.heap, c));
        InstAction::NextPC
      }
      Inst::LaC(opr) => {
        let c = P::unwrap_val(self.consts.get(opr as usize))?;
        self.push_ptr(c.ptr());
        InstAction::NextPC
      }
      Inst::StB => {
        let v = self.pop()?;
        let ptr = self.pop_ptr()?;
        self.store::<u8>(v, ptr)?
      }
      Inst::StH => {
        let v = self.pop()?;
        let ptr = self.pop_ptr()?;
        self.store::<u16>(v, ptr)?
      }
      Inst::StW => {
        let v = self.pop()?;
        let ptr = self.pop_ptr()?;
        self.store::<u32>(v, ptr)?
      }
      Inst::StD => {
        let v = self.pop()?;
        let ptr = self.pop_ptr()?;
        self.store::<u64>(v, ptr)?
      }
      Inst::StBO(opr) => {
        let v = self.pop()?;
        let offset = opr * mem::size_of::<u8>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.store::<u8>(v, ptr)?
      }
      Inst::StHO(opr) => {
        let v = self.pop()?;
        let offset = opr * mem::size_of::<u16>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.store::<u16>(v, ptr)?
      }
      Inst::StWO(opr) => {
        let v = self.pop()?;
        let offset = opr * mem::size_of::<u32>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.store::<u32>(v, ptr)?
      }
      Inst::StDO(opr) => {
        let v = self.pop()?;
        let offset = opr * mem::size_of::<u64>() as i64;
        let ptr = (self.pop_ptr()? as i64 + offset) as u64;
        self.store::<u64>(v, ptr)?
      }
      Inst::StV(opr) => {
        let v = self.pop()?;
        self
          .var_stack
          .last_mut()
          .unwrap()
          .set_or_create(opr as usize, v);
        InstAction::NextPC
      }
      Inst::StG(opr) => {
        let v = self.pop()?;
        self
          .var_stack
          .first_mut()
          .unwrap()
          .set_or_create(opr as usize, v);
        InstAction::NextPC
      }
      Inst::StA(opr) => {
        for index in (0..=opr as usize).rev() {
          let v = self.pop()?;
          self.var_stack.last_mut().unwrap().set_or_create(index, v);
        }
        InstAction::NextPC
      }
      Inst::New => {
        let align = self.pop_int_ptr()?;
        let size = self.pop_int_ptr()?;
        let ptr = self.heap.alloc(P::layout(size as usize, align as usize)?);
        self.push_ptr(ptr);
        InstAction::NextPC
      }
      Inst::NewO => {
        let obj_ptr = self.pop_ptr()?;
        self.new_object(obj_ptr)?
      }
      Inst::NewOC(opr) => {
        let c = P::unwrap_val(self.consts.get(opr as usize))?;
        let obj_ptr = P::obj_ptr_from_const(c)?;
        self.new_object(obj_ptr)?
      }
      Inst::NewA => {
        let len = self.pop_int_ptr()?;
        let obj_ptr = self.pop_ptr()?;
        self.new_array(obj_ptr, len)?
      }
      Inst::NewAC(opr) => {
        let len = self.pop_int_ptr()?;
        let c = P::unwrap_val(self.consts.get(opr as usize))?;
        let obj_ptr = P::obj_ptr_from_const(c)?;
        self.new_array(obj_ptr, len)?
      }
      Inst::Del => {
        let ptr = self.pop_ptr()?;
        self.heap.dealloc(ptr);
        InstAction::NextPC
      }
      Inst::Bnz(opr) => {
        if self.pop_any()? != 0 {
          InstAction::SetPC((self.pc as i64 + opr) as u64)
        } else {
          InstAction::NextPC
        }
      }
      Inst::Jmp(opr) => InstAction::SetPC((self.pc as i64 + opr) as u64),
      Inst::Call(opr) => {
        self.var_stack.push(Vars::new());
        self.ra_stack.push(self.pc + 1);
        InstAction::SetPC((self.pc as i64 + opr) as u64)
      }
      Inst::Ret => {
        self.var_stack.pop();
        match self.ra_stack.pop() {
          Some(pc) => InstAction::SetPC(pc),
          None => InstAction::Stop,
        }
      }
      Inst::Sys(opr) => unimplemented!("system call"),
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
      Inst::Lt => binary!((lhs, rhs): u64, (lhs < rhs) as u64),
      Inst::Le => binary!((lhs, rhs): u64, (lhs <= rhs) as u64),
      Inst::Gt => binary!((lhs, rhs): u64, (lhs > rhs) as u64),
      Inst::Ge => binary!((lhs, rhs): u64, (lhs >= rhs) as u64),
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
        InstAction::NextPC
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
        InstAction::NextPC
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
    self.pop().and_then(|v| P::get_int_ptr(&v))
  }

  /// Pops a 32-bit floating point from the value stack.
  fn pop_f32(&mut self) -> Result<f32, P::Error> {
    self.pop().and_then(|v| P::get_f32(&v))
  }

  /// Pops a 64-bit floating point from the value stack.
  fn pop_f64(&mut self) -> Result<f64, P::Error> {
    self.pop().and_then(|v| P::get_f64(&v))
  }

  /// Pops a pointer from the value stack.
  fn pop_ptr(&mut self) -> Result<u64, P::Error> {
    self.pop().and_then(|v| P::get_ptr(&v))
  }

  /// Pops a untyped value from the value stack.
  fn pop_any(&mut self) -> Result<u64, P::Error> {
    self.pop().map(|v| P::get_any(&v))
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

  /// Loads the given pointer as type `T`.
  fn load<T>(&mut self, ptr: u64) -> Result<InstAction, P::Error>
  where
    T: Copy + IntoU64,
  {
    P::check_access(&self.heap, ptr, mem::size_of::<T>())?;
    self.push_int(unsafe { *(self.heap.addr(ptr) as *const T) }.into_u64());
    Ok(InstAction::NextPC)
  }

  /// Loads the given pointer as a pointer.
  fn load_ptr(&mut self, ptr: u64) -> Result<InstAction, P::Error> {
    P::check_access(&self.heap, ptr, mem::size_of::<u64>())?;
    self.push_ptr(unsafe { *(self.heap.addr(ptr) as *const u64) });
    Ok(InstAction::NextPC)
  }

  /// Stores the given value (of type `T`) to the memory
  /// pointed by the given pointer.
  fn store<T>(&mut self, v: P::Value, ptr: u64) -> Result<InstAction, P::Error>
  where
    T: Copy,
  {
    P::check_access(&self.heap, ptr, mem::size_of::<T>())?;
    unsafe { *(self.heap.addr_mut(ptr) as *mut T) = *(&P::get_any(&v) as *const _ as *const T) };
    Ok(InstAction::NextPC)
  }

  /// Allocates heap memory for the given object metadata pointer.
  fn new_object(&mut self, obj_ptr: u64) -> Result<InstAction, P::Error> {
    let object = P::object(&self.heap, obj_ptr)?;
    self.alloc_obj(object.size, object.align, ObjKind::Obj, obj_ptr)
  }

  /// Allocates array for the given object metadata pointer.
  fn new_array(&mut self, obj_ptr: u64, len: u64) -> Result<InstAction, P::Error> {
    let object = P::object(&self.heap, obj_ptr)?;
    let size = if len != 0 {
      object.aligned_size() * (len - 1) + object.size
    } else {
      0
    };
    self.alloc_obj(size, object.align, ObjKind::Array(len as usize), obj_ptr)
  }

  /// Allocates a new memory with object metadata.
  fn alloc_obj(
    &mut self,
    size: u64,
    align: u64,
    kind: ObjKind,
    obj_ptr: u64,
  ) -> Result<InstAction, P::Error> {
    let layout = P::layout(size as usize, align as usize)?;
    let ptr = self.heap.alloc_obj(layout, Obj { kind, ptr: obj_ptr });
    self.push_ptr(ptr);
    Ok(InstAction::NextPC)
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
    if let Some(var) = self.get_mut(index) {
      *var = v;
    } else {
      self.vars.resize_with(index + 1, || None);
      self.vars[index] = Some(v);
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

/// Converts the given value into a 64-bit unsigned integer.
trait IntoU64 {
  fn into_u64(self) -> u64;
}

/// Helper macros for implementing [`IntoU64`] for the given type.
macro_rules! impl_into_u64 {
  ($ty:ty) => {
    impl IntoU64 for $ty {
      fn into_u64(self) -> u64 {
        self as u64
      }
    }
  };
}

impl_into_u64!(i8);
impl_into_u64!(u8);
impl_into_u64!(i16);
impl_into_u64!(u16);
impl_into_u64!(i32);
impl_into_u64!(u32);
impl_into_u64!(u64);
