import SimpleC.Common.CTypes

namespace SimpleC.CoreLang.CTypes

open SimpleC.Common.CTypes

inductive FieldName where
  | CFN_named (name : String)
  | CFN_unnamed (id : Int)
  deriving DecidableEq, Repr

inductive TypeName where
  | CTN_named (name : String)
  | CTN_unnamed (id : Int)
  deriving DecidableEq, Repr

inductive SimpleCtype where
  | CT_basic (type : CBasicType)
  | CT_pointer (type : SimpleCtype)
  | CT_array (type : SimpleCtype) (length : Option Int)
  | CT_function (result : SimpleCtype) (parameters : List SimpleCtype)
  | CT_struct (name : TypeName) (level : Nat)
  | CT_union (name : TypeName) (level : Nat)
  | CT_enum (name : TypeName) (level : Nat)
  | CT_alias (name : String) (level : Nat)
  deriving Repr

export FieldName (CFN_named CFN_unnamed)
export TypeName (CTN_named CTN_unnamed)
export SimpleCtype (CT_basic CT_pointer CT_array CT_function CT_struct CT_union CT_enum CT_alias)

end SimpleC.CoreLang.CTypes
