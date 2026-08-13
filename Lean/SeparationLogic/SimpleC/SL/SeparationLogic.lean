import SimpleC.SL.Assertion
import SimpleC.SL.ConAssertion
import SimpleC.SL.Array2Lib
import SimpleC.SL.MapLib
import SimpleC.SL.PtrArray2Lib
import SimpleC.SL.StringLib
import SimpleC.SL.CriticalSTS

namespace SimpleC.SL.CommonAssertion.SeparationLogicSig

export SimpleC.SL.CommonAssertion.DerivedPredSig (
  store_byte
  store_2byte
  store_4byte
  store_8byte
  store_byte_noninit
  store_2byte_noninit
  store_4byte_noninit
  store_8byte_noninit
  store_char
  undef_store_char
  store_uchar
  undef_store_uchar
  store_short
  undef_store_short
  store_ushort
  undef_store_ushort
  store_int
  undef_store_int
  store_uint
  undef_store_uint
  store_int64
  undef_store_int64
  store_uint64
  undef_store_uint64
  store_ptr
  undef_store_ptr
  Invalid_store
  Invalid_undef_store
  dup_data_at_error
  store_array_rec
  store_array_missing_i_rec
  store_array
  store_undef_array_rec
  store_undef_array_missing_i_rec
  store_undef_array
  store_align4_list
  store_align4_n
  store_align_list
  store_align_n
  poly_store
  poly_undef_store
  struct_padding
  union_padding
  coq_prop_andp_left
  coq_prop_andp_right
  coq_prop_imply
  coq_prop_False_left
  orp_sepcon_left
  orp_sepcon_right
  orp_sepcon_left'
  orp_sepcon_right'
  orp_sepcon_left_equiv
  orp_sepcon_right_equiv
  exp_right_exists
  derivable1_imp
  derivable1_andp_mono
  ex_logic_equiv_andp
  wand_equiv
  ex_logic_equiv_sepcon
  prop_add_left
  truep_andp_left_equiv
  truep_andp_right_equiv
  sepcon_emp_equiv
  sepcon_cancel_res_emp
  sepcon_cancel_end
  sepcon_prop_equiv
  exp_exp_right
  exp_allp_left
  exp_allp_swap
  allp_allp_swap
  derivable1_wand_sepcon_adjoint
  all_list
  sepcon_emp_logic_equiv'
  elim_wand_emp_emp
  dump_spatial_left
  split_pure_and_spatial_goals
  _derivable1_andp_intros
  add_pure_split
  sepcon_cancel_lhs_emp
)

export SimpleC.SL.StoreAux.StoreLibSig (
  store_n_bytes
  store_n_bytes_Z
  store_n_bytes_noninit
  store_byte_eqm
  store_byte_equiv_store_n_bytes_Z
  store_2byte_equiv_store_n_bytes_Z
  store_4byte_equiv_store_n_bytes_Z
  store_8byte_equiv_store_n_bytes_Z
  store_byte_store_byte_noinit
  store_2byte_store_2byte_noinit
  store_4byte_store_4byte_noinit
  store_8byte_store_8byte_noinit
  store_ptr_undef_store_ptr
  store_int_range
  store_int_undef_store_int
  store_char_range
  store_char_undef_store_char
  store_short_range
  store_short_undef_store_short
  store_int64_range
  store_int64_undef_store_int64
  store_uint_range
  store_uint_undef_store_uint
  store_uchar_range
  store_uchar_undef_store_uchar
  store_ushort_range
  store_ushort_undef_store_ushort
  store_uint64_range
  store_uint64_undef_store_uint64
  poly_store_poly_undef_store
  dup_mstore
  dup_store_byte_noninit
  dup_store_byte
  dup_store_2bytes_noninit
  dup_store_2bytes
  dup_store_4bytes_noninit
  dup_store_4bytes
  dup_store_8bytes_noninit
  dup_store_8bytes
  dup_undef_store_int
  dup_store_int
  dup_undef_store_ptr
  dup_store_ptr
  store_byte_cast
  store_byte_cast'
  store_char_cast
  store_uchar_cast
  store_short_cast
  store_ushort_cast
  store_int_cast
  store_uint_cast
  store_int64_cast
  store_uint64_cast
  store_int_store_char
  store_uint_store_char
  undef_store_uint_undef_store_char
  undef_store_int_undef_store_char
  valid_store_char
  valid_store_uchar
  valid_undef_store_char
  valid_undef_store_uchar
  valid_store_short
  valid_store_ushort
  valid_undef_store_short
  valid_undef_store_ushort
  valid_store_int
  valid_store_uint
  valid_undef_store_int
  valid_undef_store_uint
  valid_store_int64
  valid_store_uint64
  valid_undef_store_int64
  valid_undef_store_uint64
  valid_store_ptr
  valid_undef_store_ptr
  undef_store_char_align
  store_char_align
  store_byte_align1
  undef_store_uchar_align
  store_uchar_align
  undef_store_int_align4
  store_int_align4
  undef_store_uint_align4
  store_uint_align4
  undef_store_int64_align4
  store_int64_align4
  undef_store_uint64_align4
  store_uint64_align4
  undef_store_ptr_align4
  store_ptr_align4
  store_byte_valid
  store_4byte_valid
  store_align4_valid
  store_align4_merge
  store_align4_n_valid
  store_align_valid
  store_align_merge
  undef_store_short_align
  store_short_align
  undef_store_ushort_align
  store_ushort_align
  store_align_n_valid
  store_align4_to_store_align
  store_ptr_store_uint
)

export SimpleC.SL.MapLib.MapLibSig (
  store_map
  store_map_missing_i
  store_map_split
  store_map_merge
  store_map_missing_equiv_store_map
  store_map_equiv_store_map_missing
  store_map_equiv
  store_map_missing_i_equiv
  store_map_empty
)

open SimpleC.SL.Array2Lib
open SimpleC.SL.ArrayLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.PtrArray2Lib
open SimpleC.SL.StoreAux
open SimpleC.SL.StringLib

abbrev derivedPredSig (self : SeparationLogicSig) : DerivedPredSig self :=
  DerivedPredSig.canonical self

abbrev storeLibSig (self : SeparationLogicSig) :
    StoreLibSig self self.derivedPredSig :=
  StoreLibSig.canonical self self.derivedPredSig

abbrev arrayLibSig (self : SeparationLogicSig) :
    ArrayLibSig self self.derivedPredSig self.storeLibSig :=
  ArrayLibSig.canonical self self.derivedPredSig self.storeLibSig

abbrev array2LibSig (self : SeparationLogicSig) :
    Array2LibSig self self.derivedPredSig self.storeLibSig self.arrayLibSig :=
  Array2LibSig.canonical self self.derivedPredSig self.storeLibSig self.arrayLibSig

abbrev ptrArray2LibSig (self : SeparationLogicSig) :
    PtrArray2LibSig self self.derivedPredSig self.storeLibSig self.arrayLibSig :=
  PtrArray2LibSig.canonical self self.derivedPredSig self.storeLibSig self.arrayLibSig

abbrev mapLibSig (self : SeparationLogicSig) :
    SimpleC.SL.MapLib.MapLibSig self self.derivedPredSig self.storeLibSig :=
  SimpleC.SL.MapLib.MapLibSig.canonical self self.derivedPredSig self.storeLibSig

-- The source module includes several StoreAux members which do not depend on
-- its logic parameter. The ignored receiver restores their aggregate shape.
abbrev vector_cons (_self : SeparationLogicSig) {A : Type} {n : Nat}
    (x : A) (xs : Vector A n) : Vector A (n + 1) :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_cons x xs
abbrev vector_head (_self : SeparationLogicSig) {A : Type} {n : Nat}
    (xs : Vector A (n + 1)) : A :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_head xs
abbrev vector_tail (_self : SeparationLogicSig) {A : Type} {n : Nat}
    (xs : Vector A (n + 1)) : Vector A n :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_tail xs
abbrev vector_head_cons (_self : SeparationLogicSig) {A : Type} {n : Nat}
    (x : A) (xs : Vector A n) :
    vector_head _self (vector_cons _self x xs) = x :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_head_cons x xs
abbrev vector_tail_cons (_self : SeparationLogicSig) {A : Type} {n : Nat}
    (x : A) (xs : Vector A n) :
    vector_tail _self (vector_cons _self x xs) = xs :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_tail_cons x xs
abbrev vector_cons_eta (_self : SeparationLogicSig) {A : Type} {n : Nat}
    (xs : Vector A (n + 1)) :
    vector_cons _self (vector_head _self xs) (vector_tail _self xs) = xs :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_cons_eta xs
abbrev bytes_eqm (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.bytes_eqm
abbrev n_bytes_to_Z (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.n_bytes_to_Z
abbrev Z_to_n_bytes (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.Z_to_n_bytes
abbrev merge_n_bytes (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_n_bytes
abbrev eqm_iff_mod_eq (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.eqm_iff_mod_eq
abbrev n_bytes_to_Z_cons (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.n_bytes_to_Z_cons
abbrev eqm_bytes_to_Z_eq (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.eqm_bytes_to_Z_eq
abbrev Z_to_n_bytes_succ (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.Z_to_n_bytes_succ
abbrev Z_to_n_bytes_to_Z (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.Z_to_n_bytes_to_Z
abbrev merge_short_equiv_merge_n_bytes (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_short_equiv_merge_n_bytes
abbrev merge_int_equiv_merge_n_bytes (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_int_equiv_merge_n_bytes
abbrev merge_int64_equiv_merge_n_bytes (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_int64_equiv_merge_n_bytes

abbrev dup_data_at_error_prop (_self : SeparationLogicSig) : Prop :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.dup_data_at_error_prop

noncomputable abbrev StoreCharAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreCharAsElement self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUCharAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreUCharAsElement self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreShortAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreShortAsElement self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUShortAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreUShortAsElement self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreIntAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreIntAsElement self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUIntAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreUIntAsElement self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreInt64AsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreInt64AsElement self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUInt64AsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreUInt64AsElement self self.derivedPredSig self.storeLibSig
noncomputable abbrev StorePtrAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StorePtrAsElement self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.CharArray self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.UCharArray self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.ShortArray self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.UShortArray self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.IntArray self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.UIntArray self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64Array (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.Int64Array self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64Array (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.UInt64Array self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.PtrArray self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.CharArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UCharArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.ShortArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UShortArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.IntArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UIntArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64Array2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.Int64Array2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64Array2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UInt64Array2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.PtrArray2
    self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.CharPtrArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UCharPtrArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.ShortPtrArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UShortPtrArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.IntPtrArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UIntPtrArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64PtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.Int64PtrArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64PtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UInt64PtrArray2
    self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.PtrPtrArray2
    self self.derivedPredSig self.storeLibSig

-- Fixed StringLib declarations become methods of every aggregate logic. The
-- abstract predicates and laws remain separate for CRules and naive_C_Rules.
abbrev AsciiToZ (_self : SeparationLogicSig) := StringLibSig.AsciiToZ
abbrev ZToAscii (_self : SeparationLogicSig) := StringLibSig.ZToAscii
abbrev string_length (_self : SeparationLogicSig) := StringLibSig.string_length
abbrev c_string (_self : SeparationLogicSig) := StringLibSig.c_string
abbrev valid_char (_self : SeparationLogicSig) := StringLibSig.valid_char
abbrev valid_string (_self : SeparationLogicSig) := StringLibSig.valid_string
abbrev StringLength (_self : SeparationLogicSig) := StringLibSig.StringLength
abbrev StringToList_nat (_self : SeparationLogicSig) := StringLibSig.StringToList_nat
abbrev StringToList (_self : SeparationLogicSig) := StringLibSig.StringToList
abbrev ListToString (_self : SeparationLogicSig) := StringLibSig.ListToString
abbrev ZToAscii_AsciiToZ (_self : SeparationLogicSig) :=
  StringLibSig.ZToAscii_AsciiToZ
abbrev ListToString_StringToList_nat_full (_self : SeparationLogicSig) :=
  StringLibSig.ListToString_StringToList_nat_full
abbrev ListToString_StringToList (_self : SeparationLogicSig) :=
  StringLibSig.ListToString_StringToList
abbrev valid_stringLit (_self : SeparationLogicSig) := StringLibSig.valid_stringLit
abbrev store_string (self : SeparationLogicSig) :=
  StringLibSig.store_string self self.derivedPredSig self.storeLibSig
abbrev store_stringLit (self : SeparationLogicSig) :=
  StringLibSig.store_stringLit self self.derivedPredSig self.storeLibSig
abbrev c_string_Zlength (_self : SeparationLogicSig) := StringLibSig.c_string_Zlength
abbrev StringToList_nat_length (_self : SeparationLogicSig) :=
  StringLibSig.StringToList_nat_length
abbrev StringToList_length (_self : SeparationLogicSig) :=
  StringLibSig.StringToList_length
abbrev StringToList_c_length (_self : SeparationLogicSig) :=
  StringLibSig.StringToList_c_length
abbrev store_string_length (self : SeparationLogicSig) :=
  StringLibSig.store_string_length self self.derivedPredSig self.storeLibSig
abbrev store_stringLit_length (self : SeparationLogicSig) :=
  StringLibSig.store_stringLit_length self self.derivedPredSig self.storeLibSig
abbrev store_string_split_to_missing_i (self : SeparationLogicSig) :=
  StringLibSig.store_string_split_to_missing_i
    self self.derivedPredSig self.storeLibSig
abbrev store_stringLit_split_to_missing_i (self : SeparationLogicSig) :=
  StringLibSig.store_stringLit_split_to_missing_i
    self self.derivedPredSig self.storeLibSig
abbrev AsciiToZ_range (_self : SeparationLogicSig) := StringLibSig.AsciiToZ_range

end SimpleC.SL.CommonAssertion.SeparationLogicSig

namespace SimpleC.SL.SeparationLogic

open SimpleC.SL.CommonAssertion
open SimpleC.SL.ConAssertion
open SimpleC.SL.StringLib

abbrev CRules : SeparationLogicSig := SimpleC.SL.Assertion.SL

abbrev naive_CSL : CSL STS_naive := CSL.canonical STS_naive

abbrev naive_C_Rules : SeparationLogicSig := naive_CSL.toSeparationLogicSig

namespace CRules

axiom GlobalStrings : (CoqString -> SimpleC.SL.Mem.addr) -> CRules.expr
axiom GlobalStrings_missing :
  (CoqString -> SimpleC.SL.Mem.addr) -> List CoqString -> CRules.expr
axiom GlobalStrings_split : forall LitMap s,
  CRules.derivable1 (GlobalStrings LitMap)
    (CRules.sepcon (GlobalStrings_missing LitMap [s])
      (CRules.store_stringLit (LitMap s) s))
axiom GlobalStrings_merge : forall LitMap s,
  CRules.derivable1
    (CRules.sepcon (GlobalStrings_missing LitMap [s])
      (CRules.store_stringLit (LitMap s) s))
    (GlobalStrings LitMap)
axiom GlobalStrings_missing_split : forall LitMap l s,
  s ∉ l ->
  CRules.derivable1 (GlobalStrings_missing LitMap l)
    (CRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (CRules.store_stringLit (LitMap s) s))
axiom GlobalStrings_missing_merge : forall LitMap l s,
  CRules.derivable1
    (CRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (CRules.store_stringLit (LitMap s) s))
    (GlobalStrings_missing LitMap l)
axiom GlobalStrings_split_existing : forall LitMap s,
  CRules.derivable1
    (CRules.sepcon (CRules.store_stringLit (LitMap s) s) (GlobalStrings LitMap))
    (CRules.sepcon (CRules.store_stringLit (LitMap s) s)
      (GlobalStrings_missing LitMap [s]))

def stringLibSig :
    StringLibSig CRules CRules.derivedPredSig CRules.storeLibSig CRules.arrayLibSig where
  GlobalStrings := GlobalStrings
  GlobalStrings_missing := GlobalStrings_missing
  GlobalStrings_split := GlobalStrings_split
  GlobalStrings_merge := GlobalStrings_merge
  GlobalStrings_missing_split := GlobalStrings_missing_split
  GlobalStrings_missing_merge := GlobalStrings_missing_merge
  GlobalStrings_split_existing := GlobalStrings_split_existing

end CRules

namespace naive_C_Rules

abbrev sts := STS_naive.sts
abbrev at_states := naive_CSL.at_states
abbrev has_tokens := naive_CSL.has_tokens

axiom GlobalStrings :
  (CoqString -> SimpleC.SL.Mem.addr) -> naive_C_Rules.expr
axiom GlobalStrings_missing :
  (CoqString -> SimpleC.SL.Mem.addr) -> List CoqString -> naive_C_Rules.expr
axiom GlobalStrings_split : forall LitMap s,
  naive_C_Rules.derivable1 (GlobalStrings LitMap)
    (naive_C_Rules.sepcon (GlobalStrings_missing LitMap [s])
      (naive_C_Rules.store_stringLit (LitMap s) s))
axiom GlobalStrings_merge : forall LitMap s,
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (GlobalStrings_missing LitMap [s])
      (naive_C_Rules.store_stringLit (LitMap s) s))
    (GlobalStrings LitMap)
axiom GlobalStrings_missing_split : forall LitMap l s,
  s ∉ l ->
  naive_C_Rules.derivable1 (GlobalStrings_missing LitMap l)
    (naive_C_Rules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (naive_C_Rules.store_stringLit (LitMap s) s))
axiom GlobalStrings_missing_merge : forall LitMap l s,
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (naive_C_Rules.store_stringLit (LitMap s) s))
    (GlobalStrings_missing LitMap l)
axiom GlobalStrings_split_existing : forall LitMap s,
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon
      (naive_C_Rules.store_stringLit (LitMap s) s) (GlobalStrings LitMap))
    (naive_C_Rules.sepcon
      (naive_C_Rules.store_stringLit (LitMap s) s)
      (GlobalStrings_missing LitMap [s]))

def stringLibSig : StringLibSig naive_C_Rules
    naive_C_Rules.derivedPredSig naive_C_Rules.storeLibSig
    naive_C_Rules.arrayLibSig where
  GlobalStrings := GlobalStrings
  GlobalStrings_missing := GlobalStrings_missing
  GlobalStrings_split := GlobalStrings_split
  GlobalStrings_merge := GlobalStrings_merge
  GlobalStrings_missing_split := GlobalStrings_missing_split
  GlobalStrings_missing_merge := GlobalStrings_missing_merge
  GlobalStrings_split_existing := GlobalStrings_split_existing

end naive_C_Rules

axiom field_address : Int -> String -> String -> Int

def should_be_equal {A : Type} (_x _y : A) : Prop := True

export SimpleC.SL.ArrayLibCore.ArrayLibCoreSig (repeat_Z repeat_Z_tail)

namespace IntArray2
noncomputable abbrev full := naive_C_Rules.IntArray2.full
noncomputable abbrev missing_i := naive_C_Rules.IntArray2.missing_i
end IntArray2

namespace IntPtrArray2
noncomputable abbrev full := naive_C_Rules.IntPtrArray2.full
noncomputable abbrev missing_i := naive_C_Rules.IntPtrArray2.missing_i
end IntPtrArray2

namespace CharPtrArray2
noncomputable abbrev full := naive_C_Rules.CharPtrArray2.full
noncomputable abbrev missing_i := naive_C_Rules.CharPtrArray2.missing_i
end CharPtrArray2

end SimpleC.SL.SeparationLogic
