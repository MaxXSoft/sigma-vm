pub mod gc;
pub mod heap;
pub mod policy;
pub mod vm;

#[cfg(test)]
mod test {
  use crate::bytecode::consts::{Const, ConstKind, ManagedPtr, Object};
  use crate::bytecode::insts::Inst;
  use crate::interpreter::gc::MarkSweep;
  use crate::interpreter::heap::{Checked, System};
  use crate::interpreter::policy::{Policy, StrictAlign};
  use crate::interpreter::vm::VM;

  /// Helper macro for constructing constant pool.
  macro_rules! consts {
    ($($t:tt),* $(,)?) => { vec![$(consts!(@const $t)),*].into_boxed_slice() };
    (@const Object { size: $s:expr, align: $a:expr, offsets: [$($o:expr),* $(,)?] $(,)? }) => {
      Const::from(Object::<[u64; consts!(@counter $($o),*)]> {
        size: $s,
        align: $a,
        managed_ptr: ManagedPtr {
          len: consts!(@counter $($o),*),
          offsets: [$($o),*],
        },
      })
    };
    (@const $e:expr) => { Const::from($e) };
    (@counter $e:expr $(,$rest:expr)*) => {
      1 + consts!(@counter $($rest),*)
    };
    (@counter) => {
      0
    };
  }

  /// Helper macro for constructing instruction list.
  macro_rules! insts {
    ($($opc:ident $(($opr:expr))?),* $(,)?) => { vec![$(Inst::$opc $(($opr))?),*].into_boxed_slice() };
  }

  type SAP = StrictAlign<Checked<System>, MarkSweep>;

  /// Creates a new VM with strict align policy and mark-sweep GC.
  fn vm(consts: Box<[Const]>, insts: Box<[Inst]>) -> VM<SAP> {
    VM::new(StrictAlign::new(1024), consts, insts)
  }

  #[test]
  fn a_plus_b() {
    fn a_plus_b(a: u64, b: u64) -> u64 {
      let mut vm = vm(consts![], insts![StA(1), LdV(0), LdV(1), Add, Ret]);
      vm.add_values(&[SAP::int_val(a), SAP::int_val(b)]);
      vm.run().unwrap();
      SAP::get_int_ptr(vm.value_stack().last().unwrap()).unwrap()
    }

    assert_eq!(a_plus_b(1, 2), 3);
  }
}
