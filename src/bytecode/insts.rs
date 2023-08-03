/// Defines opcode and instruction.
macro_rules! def_opc_inst {
  ($($(#[$a:meta])* $opc:ident $(($t:tt))?),+ $(,)?) => {
    /// Operation code of instruction.
    #[repr(u8)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Opcode {
      $($(#[$a])* $opc),+
    }

    /// VM instructions.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Inst {
      $($(#[$a])* $opc $(($t))?),+
    }

    impl Inst {
      /// Returns the corresponding [`Opcode`] of the current instruction.
      pub fn opcode(&self) -> Opcode {
        match self {
          $(def_opc_inst!(@pat $opc $(($t))?) => Opcode::$opc,)+
        }
      }
    }
  };
  (@pat $opc:ident) => { Self::$opc };
  (@pat $opc:ident ($t:tt)) => { Self::$opc(..) };
}

def_opc_inst! {
  /// No operation.
  Nop,
  /// Push signed integer opr constant to stack.
  PushI(i64),
  /// Push unsigned integer opr constant to stack.
  PushU(u64),
  /// Discard the value at the top of the stack.
  Pop,
  /// Load address s0, and push the signed 8-bit result to stack.
  LoadB,
  /// Load address s0, and push the unsigned 8-bit result to stack.
  LoadBU,
  /// Load address s0, and push the signed 16-bit result to stack.
  LoadH,
  /// Load address s0, and push the unsigned 16-bit result to stack.
  LoadHU,
  /// Load address s0, and push the signed 32-bit result to stack.
  LoadW,
  /// Load address s0, and push the unsigned 32-bit result to stack.
  LoadWU,
  /// Load address s0, and push the signed 64-bit result to stack.
  LoadD,
  /// Load address s0 with offset opr,
  /// and push the signed 8-bit result to stack.
  LoadBO(i64),
  /// Load address s0 with offset opr,
  /// and push the unsigned 8-bit result to stack.
  LoadBUO(i64),
  /// Load address s0 with offset opr,
  /// and push the signed 16-bit result to stack.
  LoadHO(i64),
  /// Load address s0 with offset opr,
  /// and push the unsigned 16-bit result to stack.
  LoadHUO(i64),
  /// Load address s0 with offset opr,
  /// and push the signed 32-bit result to stack.
  LoadWO(i64),
  /// Load address s0 with offset opr,
  /// and push the unsigned 32-bit result to stack.
  LoadWUO(i64),
  /// Load address s0 with offset opr,
  /// and push the signed 64-bit result to stack.
  LoadDO(i64),
  /// Load variable opr, and push the result to stack.
  LoadV(u64),
  /// Store 8-bit value s0 to address s1.
  StoreB,
  /// Store 16-bit value s0 to address s1.
  StoreH,
  /// Store 32-bit value s0 to address s1.
  StoreW,
  /// Store 64-bit value s0 to address s1.
  StoreD,
  /// Store 8-bit value s0 to address s1 with offset opr.
  StoreBO(i64),
  /// Store 16-bit value s0 to address s1 with offset opr.
  StoreHO(i64),
  /// Store 32-bit value s0 to address s1 with offset opr.
  StoreWO(i64),
  /// Store 64-bit value s0 to address s1 with offset opr.
  StoreDO(i64),
  /// Store value s0 to variable opr.
  StoreV(u64),
  /// Store arguments s0, ..., s{opr}.
  StoreA(u64),
  /// Allocate heap memory, with size s0 and managed pointer number opr.
  Alloc(u64),
  /// Branch to pc + opr if s0 is not zero.
  Bnz(i64),
  /// Jump to pc + opr.
  Jmp(i64),
  /// Call the function at pc + opr with arguments s0, ..., s{n - 1}.
  Call(i64),
  /// Return from the current function.
  Ret,
  /// System call.
  Sys(u64),
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
  Sext,
  /// Zero extend the opr-bit integer s0.
  Zext,
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
  /// Modulo.
  Mod,
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
}
