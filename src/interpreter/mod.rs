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

  #[test]
  fn fib_recursive() {
    fn fib(n: u64) -> u64 {
      vm! {
        insts: [
          StA(0),
          Call(19), // main
          Ret,
        // fib:
          StA(0),
          LdV(0),
          PushU(2),
          GtU,
          Bnz(3), // fib_else
          PushU(1),
          Ret,
        // fib_else:
          LdV(0),
          PushU(1),
          Sub,
          Call(-10), // fib
          LdV(0),
          PushU(2),
          Sub,
          Call(-14), // fib
          Add,
          Ret,
        // main:
          LdG(0),
          Call(-18), // fib
          Ret,
        ],
        consts: [],
        args: [u64: n],
        results: (u64),
      }
    }

    assert_eq!(fib(0), 1);
    assert_eq!(fib(1), 1);
    assert_eq!(fib(2), 1);
    assert_eq!(fib(3), 2);
    assert_eq!(fib(4), 3);
    assert_eq!(fib(5), 5);
    assert_eq!(fib(10), 55);
    assert_eq!(fib(20), 6765);
  }
}
