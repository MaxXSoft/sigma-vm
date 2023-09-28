use crate::bytecode::insts::Inst;
use crate::bytecode::module::Module;
use crate::interpreter::gc::ContextRoots;
use crate::interpreter::heap::Ptr;
use crate::interpreter::policy::Policy;
use crate::interpreter::vm::{ControlFlow, GlobalHeap, Vars};
use std::mem;

/// Execution context of virtual machine.
pub(super) struct Context<P: Policy> {
  pub(super) module: Ptr,
  pub(super) pc: u64,
  pub(super) destructor_kind: Option<DestructorKind>,
  var_stack: Vec<Vars<P::Value>>,
  ra_stack: Vec<u64>,
}

impl<P: Policy> Context<P> {
  /// Creates a new context for initialization.
  pub(super) fn init(module: Ptr) -> Self {
    Self {
      module,
      pc: 0,
      destructor_kind: None,
      var_stack: vec![Vars::new()],
      ra_stack: vec![],
    }
  }

  /// Creates a new context for function call.
  pub(super) fn call(module: Ptr, pc: u64) -> Self {
    Self {
      module,
      pc,
      destructor_kind: None,
      var_stack: vec![Vars::new()],
      ra_stack: vec![],
    }
  }

  /// Creates a new context for terminator.
  pub(super) fn terminator() -> Self {
    Self {
      module: Ptr::null(),
      pc: 0,
      destructor_kind: Some(DestructorKind::Terminator),
      var_stack: vec![],
      ra_stack: vec![],
    }
  }

  /// Converts the current context into a new one for destructor.
  pub(super) fn into_destructor(self) -> Self {
    Self {
      module: self.module,
      pc: self.pc,
      destructor_kind: Some(DestructorKind::Destructor),
      var_stack: self.var_stack,
      ra_stack: self.ra_stack,
    }
  }

  /// Converts the current context into a new one for continue.
  pub(super) fn into_cont(self) -> Self {
    Self {
      module: self.module,
      pc: self.pc + 1,
      destructor_kind: None,
      var_stack: self.var_stack,
      ra_stack: self.ra_stack,
    }
  }

  /// Returns GC roots of the current context.
  pub(super) fn roots(&self) -> ContextRoots<P> {
    ContextRoots {
      module: self.module,
      vars: &self.var_stack,
    }
  }
}

impl<P: Policy> Context<P>
where
  P::Value: Clone,
{
  /// Runs and consumes the current context.
  pub(super) fn run(&mut self, mut gctx: GlobalContext<P>) -> Result<ControlFlow, P::Error> {
    loop {
      let inst = gctx.inst(self.pc);
      match self.run_inst(&mut gctx, inst)? {
        PcUpdate::Next => self.pc += 1,
        PcUpdate::Set(pc) => self.pc = pc,
        PcUpdate::ControlFlow(c) => return Ok(c),
      }
    }
  }

  /// Runs the current instruction.
  ///
  /// Returns `false` if the instruction requires to stop execution.
  fn run_inst(&mut self, gctx: &mut GlobalContext<P>, inst: Inst) -> Result<PcUpdate, P::Error> {
    /// Helper macro for manipulating stack.
    macro_rules! stack {
      (pop($v:ident: u64)) => {
        let $v = gctx.pop_int_ptr()?;
      };
      (push($v:expr, u64)) => {
        gctx.push_int($v);
      };
      (pop($v:ident: f32)) => {
        let $v = gctx.pop_f32()?;
      };
      (push($v:expr, f32)) => {
        gctx.push_f32($v);
      };
      (pop($v:ident: f64)) => {
        let $v = gctx.pop_f64()?;
      };
      (push($v:expr, f64)) => {
        gctx.push_f64($v);
      };
      (pop($v:ident: _)) => {
        let $v = gctx.pop_any()?;
      };
      (push($v:expr, Ptr)) => {
        gctx.push_ptr($v);
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
        gctx.push_int(opr as u64);
        PcUpdate::Next
      }
      Inst::PushU(opr) => {
        gctx.push_int(opr);
        PcUpdate::Next
      }
      Inst::Pop => {
        gctx.pop()?;
        PcUpdate::Next
      }
      Inst::Dup => {
        gctx.push(gctx.peek_s0()?.clone());
        PcUpdate::Next
      }
      Inst::Swap => {
        let mut s0 = gctx.pop()?;
        let s1 = gctx.peek_s0_mut()?;
        mem::swap(&mut s0, s1);
        gctx.push(s0);
        PcUpdate::Next
      }
      Inst::LdB => {
        let ptr = gctx.pop_ptr()?;
        let data = gctx.global_heap.load::<i8>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdBU => {
        let ptr = gctx.pop_ptr()?;
        let data = gctx.global_heap.load::<u8>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdH => {
        let ptr = gctx.pop_ptr()?;
        let data = gctx.global_heap.load::<i16>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdHU => {
        let ptr = gctx.pop_ptr()?;
        let data = gctx.global_heap.load::<u16>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdW => {
        let ptr = gctx.pop_ptr()?;
        let data = gctx.global_heap.load::<i32>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdWU => {
        let ptr = gctx.pop_ptr()?;
        let data = gctx.global_heap.load::<u32>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdD => {
        let ptr = gctx.pop_ptr()?;
        let data = gctx.global_heap.load::<u64>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdP => {
        let ptr = gctx.pop_ptr()?;
        let data = gctx.global_heap.load::<u64>(ptr)?;
        gctx.push_ptr(data.into());
        PcUpdate::Next
      }
      Inst::LdBO(opr) => {
        let offset = opr * mem::size_of::<i8>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        let data = gctx.global_heap.load::<i8>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdBUO(opr) => {
        let offset = opr * mem::size_of::<u8>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        let data = gctx.global_heap.load::<u8>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdHO(opr) => {
        let offset = opr * mem::size_of::<i16>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        let data = gctx.global_heap.load::<i16>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdHUO(opr) => {
        let offset = opr * mem::size_of::<u16>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        let data = gctx.global_heap.load::<u16>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdWO(opr) => {
        let offset = opr * mem::size_of::<i32>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        let data = gctx.global_heap.load::<i32>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdWUO(opr) => {
        let offset = opr * mem::size_of::<u32>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        let data = gctx.global_heap.load::<u32>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdDO(opr) => {
        let offset = opr * mem::size_of::<u64>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        let data = gctx.global_heap.load::<u64>(ptr)?;
        gctx.push_int(data);
        PcUpdate::Next
      }
      Inst::LdPO(opr) => {
        let offset = opr * mem::size_of::<u64>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        let data = gctx.global_heap.load::<u64>(ptr)?;
        gctx.push_ptr(data.into());
        PcUpdate::Next
      }
      Inst::LdV(opr) => {
        let locals = P::unwrap_val(self.var_stack.last())?;
        let var = P::unwrap_val(locals.get(opr as usize))?;
        gctx.push(var.clone());
        PcUpdate::Next
      }
      Inst::LdG(opr) => {
        let var = P::unwrap_val(gctx.global_vars.get(opr as usize))?;
        gctx.push(var.clone());
        PcUpdate::Next
      }
      Inst::LdC(opr) => {
        let c = P::unwrap_val(gctx.module.consts.get(opr as usize))?;
        gctx.push(gctx.global_heap.val_from_const(c));
        PcUpdate::Next
      }
      Inst::LaC(opr) => {
        let c = P::unwrap_val(gctx.module.consts.get(opr as usize))?;
        gctx.push_ptr(c.ptr());
        PcUpdate::Next
      }
      Inst::StB => {
        let v = gctx.pop()?;
        let ptr = gctx.pop_ptr()?;
        gctx.global_heap.store::<u8>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StH => {
        let v = gctx.pop()?;
        let ptr = gctx.pop_ptr()?;
        gctx.global_heap.store::<u16>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StW => {
        let v = gctx.pop()?;
        let ptr = gctx.pop_ptr()?;
        gctx.global_heap.store::<u32>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StD => {
        let v = gctx.pop()?;
        let ptr = gctx.pop_ptr()?;
        gctx.global_heap.store::<u64>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StBO(opr) => {
        let v = gctx.pop()?;
        let offset = opr * mem::size_of::<u8>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        gctx.global_heap.store::<u8>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StHO(opr) => {
        let v = gctx.pop()?;
        let offset = opr * mem::size_of::<u16>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        gctx.global_heap.store::<u16>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StWO(opr) => {
        let v = gctx.pop()?;
        let offset = opr * mem::size_of::<u32>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        gctx.global_heap.store::<u32>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StDO(opr) => {
        let v = gctx.pop()?;
        let offset = opr * mem::size_of::<u64>() as i64;
        let ptr = gctx.pop_ptr()? + offset;
        gctx.global_heap.store::<u64>(v, ptr)?;
        PcUpdate::Next
      }
      Inst::StV(opr) => {
        let v = gctx.pop()?;
        let locals = P::unwrap_val(self.var_stack.last_mut())?;
        locals.set_or_create(opr as usize, v);
        PcUpdate::Next
      }
      Inst::StG(opr) => {
        let v = gctx.pop()?;
        gctx.global_vars.set_or_create(opr as usize, v);
        PcUpdate::Next
      }
      Inst::StA(opr) => {
        for index in (0..=opr as usize).rev() {
          let v = gctx.pop()?;
          P::unwrap_val(self.var_stack.last_mut())?.set_or_create(index, v);
        }
        PcUpdate::Next
      }
      Inst::New => {
        if gctx.global_heap.should_collect() {
          return ControlFlow::GC.into();
        }
        let align = gctx.pop_int_ptr()?;
        let size = gctx.pop_int_ptr()?;
        let ptr = gctx.global_heap.alloc(size, align)?;
        gctx.push_ptr(ptr);
        PcUpdate::Next
      }
      Inst::NewO => {
        if gctx.global_heap.should_collect() {
          return ControlFlow::GC.into();
        }
        let obj_ptr = gctx.pop_ptr()?;
        let ptr = gctx.global_heap.new_object(obj_ptr, self.module)?;
        gctx.push_ptr(ptr);
        PcUpdate::Next
      }
      Inst::NewOC(opr) => {
        if gctx.global_heap.should_collect() {
          return ControlFlow::GC.into();
        }
        let c = P::unwrap_val(gctx.module.consts.get(opr as usize))?;
        let obj_ptr = P::obj_ptr_from_const(c)?;
        let ptr = gctx.global_heap.new_object(obj_ptr, self.module)?;
        gctx.push_ptr(ptr);
        PcUpdate::Next
      }
      Inst::NewA => {
        if gctx.global_heap.should_collect() {
          return ControlFlow::GC.into();
        }
        let len = gctx.pop_int_ptr()?;
        let obj_ptr = gctx.pop_ptr()?;
        let ptr = gctx.global_heap.new_array(obj_ptr, len, self.module)?;
        gctx.push_ptr(ptr);
        PcUpdate::Next
      }
      Inst::NewAC(opr) => {
        if gctx.global_heap.should_collect() {
          return ControlFlow::GC.into();
        }
        let len = gctx.pop_int_ptr()?;
        let c = P::unwrap_val(gctx.module.consts.get(opr as usize))?;
        let obj_ptr = P::obj_ptr_from_const(c)?;
        let ptr = gctx.global_heap.new_array(obj_ptr, len, self.module)?;
        gctx.push_ptr(ptr);
        PcUpdate::Next
      }
      Inst::Load => {
        let ptr = gctx.pop_ptr()?;
        return ControlFlow::LoadModule(ptr).into();
      }
      Inst::LoadC(opr) => {
        let c = P::unwrap_val(gctx.module.consts.get(opr as usize))?;
        let ptr = P::str_ptr_from_const(c)?;
        return ControlFlow::LoadModule(ptr).into();
      }
      Inst::LoadM => {
        let size = gctx.pop_int_ptr()?;
        let ptr = gctx.pop_ptr()?;
        return ControlFlow::LoadModuleMem(ptr, size).into();
      }
      Inst::Bz(opr) => {
        if gctx.pop_any()? == 0 {
          PcUpdate::Set((self.pc as i64 + opr) as u64)
        } else {
          PcUpdate::Next
        }
      }
      Inst::Bnz(opr) => {
        if gctx.pop_any()? != 0 {
          PcUpdate::Set((self.pc as i64 + opr) as u64)
        } else {
          PcUpdate::Next
        }
      }
      Inst::Jmp(opr) => PcUpdate::Set((self.pc as i64 + opr) as u64),
      Inst::JmpS => PcUpdate::Set(gctx.pop_int_ptr()?),
      Inst::Call(opr) => {
        self.var_stack.push(Vars::new());
        self.ra_stack.push(self.pc + 1);
        PcUpdate::Set((self.pc as i64 + opr) as u64)
      }
      Inst::CallS => {
        self.var_stack.push(Vars::new());
        self.ra_stack.push(self.pc + 1);
        PcUpdate::Set(gctx.pop_int_ptr()?)
      }
      Inst::CallExt => {
        let ptr = gctx.pop_ptr()?;
        let handle = gctx.pop_ptr()?;
        return ControlFlow::CallExt(handle, ptr).into();
      }
      Inst::CallExtS => {
        let pc = gctx.pop_int_ptr()?;
        let handle = gctx.pop_ptr()?;
        return ControlFlow::CallExtPc(handle, pc).into();
      }
      Inst::CallExtC(opr) => {
        let handle = gctx.pop_ptr()?;
        let c = P::unwrap_val(gctx.module.consts.get(opr as usize))?;
        let ptr = P::str_ptr_from_const(c)?;
        return ControlFlow::CallExt(handle, ptr).into();
      }
      Inst::Ret => {
        let pcu = if let Some(pc) = self.ra_stack.pop() {
          PcUpdate::Set(pc)
        } else {
          return ControlFlow::Stop.into();
        };
        self.var_stack.pop();
        pcu
      }
      Inst::Sys(opr) => return ControlFlow::Syscall(opr).into(),
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
        let rhs = gctx.pop()?;
        let lhs = gctx.pop()?;
        let sum = P::get_int_ptr(&lhs)?.wrapping_add(P::get_int_ptr(&rhs)?);
        if P::ptr_or_none(&lhs).is_some() ^ P::ptr_or_none(&rhs).is_some() {
          gctx.push_ptr(sum.into());
        } else {
          gctx.push_int(sum);
        }
        PcUpdate::Next
      }
      Inst::Sub => {
        let rhs = gctx.pop()?;
        let lhs = gctx.pop()?;
        let sub = P::get_int_ptr(&lhs)?.wrapping_sub(P::get_int_ptr(&rhs)?);
        if P::ptr_or_none(&lhs).is_some() {
          gctx.push_ptr(sub.into());
        } else {
          gctx.push_int(sub);
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
      Inst::ITP => unary!(s0: u64, Ptr: s0.into()),
    })
  }
}

/// Kind of destructor.
#[derive(PartialEq, Eq)]
pub(super) enum DestructorKind {
  /// Destructor.
  Destructor,
  /// Terminator, for destructing all heap objects.
  Terminator,
}

/// Global context, shared by multiple contexts.
pub(super) struct GlobalContext<'vm, P: Policy> {
  pub(super) module: &'vm Module,
  pub(super) global_heap: &'vm mut GlobalHeap<P>,
  pub(super) global_vars: &'vm mut Vars<P::Value>,
  pub(super) value_stack: &'vm mut Vec<P::Value>,
}

impl<'vm, P: Policy> GlobalContext<'vm, P> {
  /// Returns the instruction at the given PC.
  fn inst(&self, pc: u64) -> Inst {
    self.module.insts[pc as usize]
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
  fn push_ptr(&mut self, p: Ptr) {
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
  fn pop_ptr(&mut self) -> Result<Ptr, P::Error> {
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

/// PC update actions.
enum PcUpdate {
  Next,
  Set(u64),
  ControlFlow(ControlFlow),
}

impl<E> From<ControlFlow> for Result<PcUpdate, E> {
  fn from(cf: ControlFlow) -> Self {
    Ok(PcUpdate::ControlFlow(cf))
  }
}
