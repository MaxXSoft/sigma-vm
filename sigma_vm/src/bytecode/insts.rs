use crate::utils::impl_try_from_int;

/// Type of instruction operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperandType {
  /// Signed operand.
  Signed,
  /// Unsigned operand.
  Unsigned,
}

/// Operand of instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand {
  /// Signed operand.
  Signed(i64),
  /// Unsigned operand.
  Unsigned(u64),
}

impl Operand {
  fn unwrap_signed(self) -> i64 {
    match self {
      Self::Signed(opr) => opr,
      _ => panic!("signed operand expected"),
    }
  }

  fn unwrap_unsigned(self) -> u64 {
    match self {
      Self::Unsigned(opr) => opr,
      _ => panic!("unsigned operand expected"),
    }
  }
}

/// Defines opcode and instruction.
macro_rules! def_opc_inst {
  ($($(#[$a:meta])* $opc:ident $(($t:tt))?),+ $(,)?) => {
    /// Operation code of instruction.
    #[repr(u8)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Opcode {
      $($(#[$a])* $opc),+
    }

    impl Opcode {
      /// Returns the operand type of the current opcode.
      pub fn operand_type(&self) -> Option<OperandType> {
        match self {
          $(Self::$opc => def_opc_inst!(@opr_type $opc $(($t))?),)+
        }
      }
    }

    impl_try_from_int! {
      impl TryFrom<u8> for Opcode {
        $($opc),+
      }
    }

    /// VM instructions.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Inst {
      $($(#[$a])* $opc $(($t))?),+
    }

    impl Inst {
      /// Creates a new instruction.
      ///
      /// # Panics
      ///
      /// Panics if `opr` does not match the instruction operand.
      pub fn new(opcode: Opcode, opr: Option<Operand>) -> Self {
        match opcode {
          $(Opcode::$opc => def_opc_inst!(@new_inst opr $opc $(($t))?),)+
        }
      }

      /// Returns the corresponding [`Opcode`] of the current instruction.
      pub fn opcode(&self) -> Opcode {
        match self {
          $(def_opc_inst!(@inst_pat $opc $(($t))?) => Opcode::$opc,)+
        }
      }

      /// Returns the corresponding [`Operand`] of the current instruction,
      /// or [`None`] if the current instruction has no operand.
      pub fn operand(&self) -> Option<Operand> {
        match self {
          $(def_opc_inst!(@inst_pat_opr $opc $(($t))?, opr) => def_opc_inst!(@operand $($t,)? opr),)+
        }
      }
    }
  };
  (@opr_type $opc:ident) => { None };
  (@opr_type $opc:ident (i64)) => { Some(OperandType::Signed) };
  (@opr_type $opc:ident (u64)) => { Some(OperandType::Unsigned) };
  (@new_inst $opr:ident $opc:ident) => { Self::$opc };
  (@new_inst $opr:ident $opc:ident (i64)) => { Self::$opc($opr.unwrap().unwrap_signed()) };
  (@new_inst $opr:ident $opc:ident (u64)) => { Self::$opc($opr.unwrap().unwrap_unsigned()) };
  (@inst_pat $opc:ident) => { Self::$opc };
  (@inst_pat $opc:ident ($t:tt)) => { Self::$opc(..) };
  (@inst_pat_opr $opc:ident, $opr:ident) => { Self::$opc };
  (@inst_pat_opr $opc:ident ($ty:ty), $opr:ident) => { Self::$opc($opr) };
  (@operand $opr:ident) => { None };
  (@operand i64, $opr:ident) => { Some(Operand::Signed(*$opr)) };
  (@operand u64, $opr:ident) => { Some(Operand::Unsigned(*$opr)) };
}

def_opc_inst! {
  /// No operation.
  Nop,
  /// Push signed integer opr constant to stack.
  PushI(i64),
  /// Push unsigned integer opr constant to stack.
  PushU(u64),
  /// Push pc to stack.
  PushPc,
  /// Discard s0.
  Pop,
  /// Duplicate s0.
  Dup,
  /// Swap s0 and s1.
  Swap,
  /// Load address s0, and push the signed 8-bit result to stack.
  LdB,
  /// Load address s0, and push the unsigned 8-bit result to stack.
  LdBU,
  /// Load address s0, and push the signed 16-bit result to stack.
  LdH,
  /// Load address s0, and push the unsigned 16-bit result to stack.
  LdHU,
  /// Load address s0, and push the signed 32-bit result to stack.
  LdW,
  /// Load address s0, and push the unsigned 32-bit result to stack.
  LdWU,
  /// Load address s0, and push the 64-bit result to stack.
  LdD,
  /// Load address s0, and push the pointer result to stack.
  LdP,
  /// Load address s0 with offset opr,
  /// and push the signed 8-bit result to stack.
  LdBO(i64),
  /// Load address s0 with offset opr,
  /// and push the unsigned 8-bit result to stack.
  LdBUO(i64),
  /// Load address s0 with offset opr,
  /// and push the signed 16-bit result to stack.
  LdHO(i64),
  /// Load address s0 with offset opr,
  /// and push the unsigned 16-bit result to stack.
  LdHUO(i64),
  /// Load address s0 with offset opr,
  /// and push the signed 32-bit result to stack.
  LdWO(i64),
  /// Load address s0 with offset opr,
  /// and push the unsigned 32-bit result to stack.
  LdWUO(i64),
  /// Load address s0 with offset opr,
  /// and push the 64-bit result to stack.
  LdDO(i64),
  /// Load address s0 with offset opr,
  /// and push the pointer result to stack.
  LdPO(i64),
  /// Load variable opr, and push the result to stack.
  LdV(u64),
  /// Load global variable opr, and push the result to stack.
  LdG(u64),
  /// Load the constant opr by its kind.
  LdC(u64),
  /// Load the address of the constant opr.
  LaC(u64),
  /// Store 8-bit value s0 to address s1.
  StB,
  /// Store 16-bit value s0 to address s1.
  StH,
  /// Store 32-bit value s0 to address s1.
  StW,
  /// Store 64-bit value s0 to address s1.
  StD,
  /// Store 8-bit value s0 to address s1 with offset opr.
  StBO(i64),
  /// Store 16-bit value s0 to address s1 with offset opr.
  StHO(i64),
  /// Store 32-bit value s0 to address s1 with offset opr.
  StWO(i64),
  /// Store 64-bit value s0 to address s1 with offset opr.
  StDO(i64),
  /// Store value s0 to variable opr.
  StV(u64),
  /// Store value s0 to global variable opr.
  StG(u64),
  /// Store arguments s0, ..., s{opr} as var{opr}, ..., var0.
  StA(u64),
  /// Allocate heap memory with size s1 and align s0.
  New,
  /// Allocate heap memory, with object metadata's address s0.
  NewO,
  /// Allocate heap memory, with object metadata's constant pool index opr.
  NewOC(u64),
  /// Allocate array with length s0, and object metadata's address s1.
  NewA,
  /// Allocate array with length s0, and object metadata's constant pool index opr.
  NewAC(u64),
  /// Load an external module with a string pointer s0 as it's path.
  /// Returns an integer for module handle, or 0 if failed.
  Load,
  /// Load an external module with a string constant opr as it's path.
  /// Returns an integer for module handle, or 0 if failed.
  LoadC(u64),
  /// Load an module from s1 pointed heap memory which size is s0 bytes.
  /// Returns an integer for module handle, or 0 if failed.
  LoadM,
  /// Branch to pc + opr if s0 is zero.
  Bz(i64),
  /// Branch to pc + opr if s0 is zero, otherwise do not pop s0.
  BzNP(i64),
  /// Branch to pc + opr if s0 is not zero.
  Bnz(i64),
  /// Set s0 to s0 - 1 (wrapping), branch to pc + opr if s0 is not zero
  /// without popping, otherwise pop s0 and do not branch.
  Loop(i64),
  /// Jump to pc + opr.
  Jmp(i64),
  /// Jump to s0.
  JmpS,
  /// Call the function at pc + opr with arguments s{n - 1}, ..., s0.
  Call(i64),
  /// Call the function at s0 with arguments s{n}, ..., s1.
  CallS,
  /// Call an external function with module handle s1, function name pointer s0
  /// and arguments s{n + 1}, ..., s2.
  CallExt,
  /// Call an external function with module handle s1, function PC s0
  /// and arguments s{n + 1}, ..., s2.
  CallExtS,
  /// Call an external function with module handle s0, function name constant opr
  /// and arguments s{n}, ..., s1.
  CallExtC(u64),
  /// Return from the current function.
  Ret,
  /// System call.
  Sys(i64),
  /// Breakpoint.
  Break,
  /// Bitwise not.
  Not,
  /// Logical not.
  LNot,
  /// Bitwise and.
  And,
  /// Bitwise or.
  Or,
  /// Bitwise xor.
  Xor,
  /// Logical left shift.
  Shl,
  /// Logical right shift.
  Shr,
  /// Arithmetic right shift.
  Sar,
  /// Sign extend the opr-bit integer s0.
  Sext(u64),
  /// Zero extend the opr-bit integer s0.
  Zext(u64),
  /// Test equal.
  Eq,
  /// Test not equal.
  Ne,
  /// Test less than.
  Lt,
  /// Test less than or equal.
  Le,
  /// Test greater than.
  Gt,
  /// Test greater than or equal.
  Ge,
  /// Test less than (unsigned).
  LtU,
  /// Test less than or equal (unsigned).
  LeU,
  /// Test greater than (unsigned).
  GtU,
  /// Test greater than or equal (unsigned).
  GeU,
  /// Negation.
  Neg,
  /// Addition.
  Add,
  /// Subtraction.
  Sub,
  /// Multiplication.
  Mul,
  /// Division.
  Div,
  /// Division (unsigned).
  DivU,
  /// Modulo.
  Mod,
  /// Modulo (unsigned).
  ModU,
  /// Test less than (float).
  LtF,
  /// Test less than or equal (float).
  LeF,
  /// Test greater than (float).
  GtF,
  /// Test greater than or equal (float).
  GeF,
  /// Negation (float).
  NegF,
  /// Addition (float).
  AddF,
  /// Subtraction (float).
  SubF,
  /// Multiplication (float).
  MulF,
  /// Division (float).
  DivF,
  /// Modulo (float).
  ModF,
  /// Test less than (double).
  LtD,
  /// Test less than or equal (double).
  LeD,
  /// Test greater than (double).
  GtD,
  /// Test greater than or equal (double).
  GeD,
  /// Negation (double).
  NegD,
  /// Addition (double).
  AddD,
  /// Subtraction (double).
  SubD,
  /// Multiplication (double).
  MulD,
  /// Division (double).
  DivD,
  /// Modulo (double).
  ModD,
  /// Integer to float.
  I2F,
  /// Integer to double.
  I2D,
  /// Float to integer.
  F2I,
  /// Float to double.
  F2D,
  /// Double to integer.
  D2I,
  /// Double to float.
  D2F,
  /// Transmutes (reinterprets) integer to float.
  ITF,
  /// Transmutes (reinterprets) integer to double.
  ITD,
  /// Transmutes (reinterprets) integer to pointer.
  ITP,
}
