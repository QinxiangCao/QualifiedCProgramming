namespace SimpleC.Common.CTypes

inductive Signedness where
  | Signed | Unsigned
  deriving DecidableEq, Repr

inductive IntSize where
  | I8 | I16 | I32 | I64
  deriving DecidableEq, Repr

inductive CBasicType where
  | CT_void
  | CT_bool
  | CT_int (signedness : Signedness) (size : IntSize)
  deriving DecidableEq, Repr

export Signedness (Signed Unsigned)
export IntSize (I8 I16 I32 I64)
export CBasicType (CT_void CT_bool CT_int)

end SimpleC.Common.CTypes
