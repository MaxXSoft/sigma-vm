pub mod gc;
pub mod heap;
pub mod policy;
pub mod vm;

#[cfg(test)]
mod test {
  use crate::bytecode::consts::{Const, ManagedPtr, Object};
  use crate::bytecode::insts::Inst;
  use crate::interpreter::gc::MarkSweep;
  use crate::interpreter::heap::{Checked, System};
  use crate::interpreter::policy::{Policy, StrictAlign};
  use crate::interpreter::vm::VM;

  /// Helper macro for constructing constant pool.
  macro_rules! consts {
    ($($e:expr),* $(,)?) => {
      vec![$(consts!(@const $e)),*].into_boxed_slice()
    };
    (@const $e:expr) => { Const::from($e) };
  }

  /// Helper macro for constructing instruction list.
  macro_rules! insts {
    ($($opc:ident $(($opr:expr))?),* $(,)?) => {
      vec![$(Inst::$opc $(($opr))?),*].into_boxed_slice()
    };
  }

  /// Helper macro for constructing values.
  macro_rules! value {
    (u64: $e:expr) => {
      SAP::int_val($e)
    };
    (f32: $e:expr) => {
      SAP::f32_val($e)
    };
    (f64: $e:expr) => {
      SAP::f64_val($e)
    };
  }

  /// Helper macro for extracting values.
  macro_rules! result {
    (u64: $e:expr) => {
      SAP::get_int_ptr($e).unwrap()
    };
    (f32: $e:expr) => {
      SAP::get_f32($e).unwrap()
    };
    (f64: $e:expr) => {
      SAP::get_f64($e).unwrap()
    };
  }

  /// Helper macro for running VM.
  macro_rules! vm {
    {
      insts: [$($opc:ident $(($opr:expr))?),* $(,)?],
      consts: [$($cs:tt)*],
      args: [$($aty:tt: $ae:expr),* $(,)?],
      results: ($($rs:tt),*) $(,)?
    } => {{
      let insts = insts![$($opc $(($opr))?),*];
      let mut vm = VM::new(SAP::new(1024), consts![$($cs)*], insts);
      vm.add_values(&[$(value!($aty: $ae)),*]);
      vm.run().unwrap();
      let values = vm.value_stack();
      let mut i = 0;
      #[allow(unused_assignments)]
      ($(vm!(@result values, i, $rs)),*)
    }};
    (@result $values:ident, $i:ident, $ty:tt) => {{
      let result = result!($ty: &$values[$i]);
      $i += 1;
      result
    }};
  }

  /// Strict align policy, with checked system heap and mark-sweep GC.
  type SAP = StrictAlign<Checked<System>, MarkSweep>;

  #[test]
  fn a_plus_b() {
    fn a_plus_b(a: u64, b: u64) -> u64 {
      vm! {
        insts: [StA(1), LdV(0), LdV(1), Add, Ret],
        consts: [],
        args: [u64: a, u64: b],
        results: (u64),
      }
    }

    assert_eq!(a_plus_b(1, 2), 3);
    assert_eq!(a_plus_b(0, 0), 0);
    assert_eq!(a_plus_b(1, u64::MAX), 0);
  }
}
