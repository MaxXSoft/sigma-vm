pub mod gc;
pub mod heap;
pub mod loader;
pub mod native;
pub mod policy;
pub mod syscall;
pub mod vm;

mod context;

#[cfg(test)]
mod test {
  use crate::bytecode::consts::{Const, ManagedPtr, Object, Str};
  use crate::bytecode::export::{CallSite, ExportInfo, NumArgs};
  use crate::bytecode::insts::Inst;
  use crate::bytecode::module::StaticModule;
  use crate::interpreter::gc::MarkSweep;
  use crate::interpreter::heap::{Checked, System};
  use crate::interpreter::policy::{Policy, StrictAlign};
  use crate::interpreter::vm::VM;
  use std::num::NonZeroU64;

  /// Helper macro for constructing constant pool.
  macro_rules! consts {
    ($($e:expr),* $(,)?) => {
      vec![$(consts!(@const $e)),*].into_boxed_slice()
    };
    (@const $e:expr) => { Const::from($e) };
  }

  /// Helper macro for constructing export information.
  macro_rules! exports {
    ($($name:literal => {
      pc: $pc:expr,
      num_args: $t:tt,
      num_rets: $num_rets:expr $(,)?
    }),* $(,)?) => {{
      let mut exports = ExportInfo::new();
      $(exports.insert($name.into(), CallSite {
        pc: $pc,
        num_args: exports!(@num_args $t),
        num_rets: $num_rets,
      });)*
      exports
    }};
    (@num_args va) => { NumArgs::Variadic };
    (@num_args $e:expr) => { NumArgs::PlusOne(NonZeroU64::new($e + 1).unwrap()) };
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
      Sap::int_val($e)
    };
    (Ptr: $e:expr) => {
      Sap::ptr_val($e)
    };
    (f32: $e:expr) => {
      Sap::f32_val($e)
    };
    (f64: $e:expr) => {
      Sap::f64_val($e)
    };
  }

  /// Helper macro for extracting values.
  macro_rules! result {
    (u64: $e:expr) => {
      Sap::get_int_ptr($e).unwrap()
    };
    (f32: $e:expr) => {
      Sap::get_f32($e).unwrap()
    };
    (f64: $e:expr) => {
      Sap::get_f64($e).unwrap()
    };
  }

  /// Helper macro for running VM.
  macro_rules! vm {
    {
      modules: {
        $($src:ident: {
          insts: [$($insts:tt)*],
          consts: [$($consts:tt)*],
          exports: [$($exports:tt)*] $(,)?
        }),* $(,)?
      },
      main: $main:ident,
      args: [$($aty:tt: $ae:expr),* $(,)?],
      results: $($rs:tt)*
    } => {{
      let mut vm = VM::new(Sap::new(1024));
      $(let $src = vm.new_module(StaticModule {
        consts: consts![$($consts)*],
        exports: exports![$($exports)*],
        insts: insts![$($insts)*],
        custom: Box::new([]),
      }).unwrap();)*
      let _rets = vm.call($main, "main", [$(value!($aty: $ae)),*]).unwrap();
      vm.terminate().unwrap();
      vm!(@results vm, $main, _rets, $($rs)*)
    }};
    (@results $vm:ident, $main:ident, $values:ident, vm_main $(,)?) => { ($vm, $main) };
    (@results $vm:ident, $main:ident, $values:ident, () $(,)?) => {{}};
    (@results $vm:ident, $main:ident, $values:ident, ($($rs:tt),+) $(,)?) => {{
      let mut _i = 0;
      ($(vm!(@result $values, _i, $rs)),+)
    }};
    (@result $values:ident, $i:ident, $ty:tt) => {{
      let result = result!($ty: &$values[$i]);
      $i += 1;
      result
    }};
  }

  /// Strict align policy, with checked system heap and mark-sweep GC.
  type Sap = StrictAlign<Checked<System>, MarkSweep>;

  #[test]
  fn a_plus_b() {
    fn a_plus_b(a: u64, b: u64) -> u64 {
      vm! {
        modules: {
          main: {
            insts: [Pop, Ret, StA(1), LdV(0), LdV(1), Add, Ret],
            consts: [],
            exports: ["main" => { pc: 2, num_args: 2, num_rets: 1 }],
          },
        },
        main: main,
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
        modules: {
          main: {
            insts: [
              Pop,
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
              Call(-17), // fib
              Ret,
            ],
            consts: [],
            exports: ["main" => { pc: 19, num_args: 1, num_rets: 1 }],
          },
        },
        main: main,
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

  #[test]
  fn doubly_linked_list() {
    fn sum_repeat(n: u64, repeat: u64) -> u64 {
      vm! {
        modules: {
          main: {
            insts: [
              Pop,
              Ret,

            // main:
              StG(1),
              StG(0),
              PushU(0),
              StV(0),
              LdG(1),
            // loop_start:
              Dup,
              Bz(10), // loop_end
              // create a new list
              LdG(0),
              Call(11), // new_list
              // get sum
              Call(59), // sum
              LdV(0),
              Add,
              StV(0),
              PushU(1),
              Sub,
              Jmp(-10), // loop_start
            // loop_end:
              Pop,
              LdV(0),
              Ret,

            // new_list:
              StA(0),
              PushU(0),
              Dup,
              StV(2),
              StV(1),
              LdV(0),
            // loop_start:
              Dup,
              Bz(19), // loop_end
              // create a new node
              Dup,
              LdV(0),
              Swap,
              Sub,
              Call(17), // new_node
              // check tail
              LdV(2),
              Bz(6), // else
              Dup,
              LdV(2),
              Swap,
              Call(23), // append
              Jmp(3), // end if
            // else:
              Dup,
              StV(1),
            // end_if:
              StV(2),
              PushU(1),
              Sub,
              Jmp(-19), // loop_start
            // loop_end:
              Pop,
              LdV(1),
              Ret,

            // new_node:
              StA(0),
              NewOC(0),
              Dup,
              PushU(0),
              StDO(0),
              Dup,
              PushU(0),
              StDO(1),
              Dup,
              LdV(0),
              StDO(2),
              Ret,

            // append:
              StA(1),
              LdV(0),
              LdV(1),
              StDO(1),
              LdV(1),
              LdV(0),
              StDO(0),
              Ret,

            // sum:
              StA(0),
              PushU(0),
              StV(1),
              LdV(0),
            // loop_start:
              Dup,
              Bz(8), // loop_end
              Dup,
              LdDO(2),
              LdV(1),
              Add,
              StV(1),
              LdPO(1),
              Jmp(-8), // loop_start
            // loop_end:
              Pop,
              LdV(1),
              Ret,
            ],
            consts: [
              Object {
                size: 24,
                align: 8,
                destructor: 0,
                managed_ptr: ManagedPtr { len: 2, offsets: [0, 1] },
              },
            ],
            exports: ["main" => { pc: 2, num_args: 2, num_rets: 1 }],
          },
        },
        main: main,
        args: [u64: n, u64: repeat],
        results: (u64),
      }
    }

    assert_eq!(sum_repeat(5, 1000), 10000);
    assert_eq!(sum_repeat(10, 10000), 450000);
  }

  #[test]
  fn call_ext() {
    fn even_odd(n: u64) -> (u64, u64) {
      vm! {
        modules: {
          main: {
            insts: [
              StG(0),
              Ret,

            // add1:
              PushU(1),
              Add,
              Ret,

            // main:
              StA(1),
              // pass handle to module `counter`
              LdG(0),
              LdV(0),
              CallExtC(1), // counter.set_g1
              LdV(1),
            // loop_start:
              Dup,
              Bz(10), // loop_end
              // set v3
              LdV(0),
              CallExtC(0), // counter.counter
              StV(2),
              // set v4
              LdV(0),
              CallExtC(0), // counter.counter
              StV(3),
              PushU(1),
              Sub,
              Jmp(-10), // loop_start
            // loop_end:
              LdV(2),
              LdV(3),
              Ret,
            ],
            consts: [
              Str {
                len: b"counter".len() as u64,
                bytes: *b"counter",
              },
              Str {
                len: b"set_g1".len() as u64,
                bytes: *b"set_g1",
              },
            ],
            exports: [
              "main" => { pc: 5, num_args: 2, num_rets: 2 },
              "add1" => { pc: 2, num_args: 1, num_rets: 1, },
            ],
          },
          counter: {
            insts: [
              Pop,
              PushU(0),
              StG(0),
              Ret,

            // counter:
              LdG(0),
              Dup,
              LdG(1),
              CallExtC(0), // main.add1
              StG(0),
              Ret,

            // set_g1:
              StG(1),
              Ret,
            ],
            consts: [
              Str {
                len: b"add1".len() as u64,
                bytes: *b"add1",
              },
            ],
            exports: [
              "counter" => { pc: 4, num_args: 0, num_rets: 1 },
              "set_g1" => { pc: 10, num_args: 1, num_rets: 0 },
            ],
          },
        },
        main: main,
        args: [Ptr: counter, u64: n],
        results: (u64, u64),
      }
    }

    assert_eq!(even_odd(1), (0, 1));
    assert_eq!(even_odd(2), (2, 3));
    assert_eq!(even_odd(3), (4, 5));
    assert_eq!(even_odd(100000), (100000 * 2 - 2, 100000 * 2 - 1));
  }

  #[test]
  fn destructor() {
    fn obj_counter(n: u64) -> u64 {
      let (vm, main) = vm! {
        modules: {
          main: {
            insts: [
              Pop,
              PushU(0),
              StG(0),
              Ret,

            // main:
            // loop_start:
              Dup,
              Bz(6), // loop_end
              NewOC(0),
              Pop,
              PushU(1),
              Sub,
              Jmp(-6), // loop_start
            // loop_end:
              Pop,
              Ret,

            // destructor:
              Pop,
              LdG(0),
              PushU(1),
              Add,
              StG(0),
              Ret,
            ],
            consts: [
              Object {
                size: 64,
                align: 1,
                destructor: 13,
                managed_ptr: ManagedPtr { len: 0, offsets: [] },
              },
            ],
            exports: ["main" => { pc: 4, num_args: 1, num_rets: 0 }],
          },
        },
        main: main,
        args: [u64: n],
        results: vm_main,
      };
      Sap::get_int_ptr(vm.globals(main).unwrap().get(0).unwrap()).unwrap()
    }

    assert_eq!(obj_counter(10), 10);
    assert_eq!(obj_counter(100), 100);
    assert_eq!(obj_counter(100000), 100000);
  }

  #[test]
  #[should_panic(expected = "called `Result::unwrap()` on an `Err` value: Strict(ModuleNotFound)")]
  fn unload_self() {
    vm! {
      modules: {
        main: {
          insts: [
            Sys(7),
            Ret,

          // main:
            Ret,
          ],
          consts: [],
          exports: ["main" => { pc: 2, num_args: 0, num_rets: 0 }],
        },
      },
      main: main,
      args: [],
      results: (),
    }
  }

  #[test]
  fn call_ext_self() {
    fn fib(n: u64) -> u64 {
      vm! {
        modules: {
          main: {
            insts: [
              StG(0),
              Ret,

            // main:
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
              LdG(0),
              CallExtC(0), // fib
              LdV(0),
              PushU(2),
              Sub,
              LdG(0),
              CallExtC(0), // fib
              Add,
              Ret,
            ],
            consts: [
              Str {
                len: b"main".len() as u64,
                bytes: *b"main",
              },
            ],
            exports: ["main" => { pc: 2, num_args: 1, num_rets: 1 }],
          },
        },
        main: main,
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

  #[test]
  fn factorial_loop() {
    fn fact(n: u64) -> u64 {
      vm! {
        modules: {
          main: {
            insts: [
              Pop,
              Ret,

            // main:
              PushU(1),
              StV(0),
              BzNP(6), // end_loop
            // start_loop:
              Dup,
              LdV(0),
              Mul,
              StV(0),
              Loop(-4), // start_loop
            // end_loop:
              LdV(0),
              Ret,
            ],
            consts: [],
            exports: ["main" => { pc: 2, num_args: 1, num_rets: 1 }],
          },
        },
        main: main,
        args: [u64: n],
        results: (u64),
      }
    }

    assert_eq!(fact(0), 1);
    assert_eq!(fact(1), 1);
    assert_eq!(fact(2), 2);
    assert_eq!(fact(3), 6);
    assert_eq!(fact(4), 24);
    assert_eq!(fact(5), 120);
    assert_eq!(fact(6), 720);
    assert_eq!(fact(10), 3628800);
  }
}
