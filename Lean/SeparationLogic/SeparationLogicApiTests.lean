import SimpleC.SL.SeparationLogic
import Lean.Util.CollectAxioms

namespace SeparationLogicApiTests

open SimpleC.SL.CommonAssertion
open SimpleC.SL.SeparationLogic
open Lean Elab Command

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env <- getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "SeparationLogic API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkSeparationLogicContract)
  "#check_separation_logic_contract " "[" ident,* "]" " => " num : command

syntax (name := checkSeparationLogicSurface)
  "#check_separation_logic_surface " "[" term,* "]" : command

elab_rules : command
  | `(#check_separation_logic_surface [$terms:term,*]) => do
      let terms := terms.getElems
      for term in terms do
        withRef term <| withoutModifyingEnv <| runTermElabM fun _ =>
          Term.withDeclName `_separation_logic_surface_check do
            let value <- Term.elabTerm term none
            Term.synthesizeSyntheticMVarsNoPostponing
            Lean.Meta.check value
      logInfo m!"SeparationLogic aggregate surface verified for {terms.size} entries"
  | `(#check_separation_logic_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "SeparationLogic API type hash changed: expected {expected}, got {actual}"
      let allowedAxioms := #[
        ``propext,
        ``Classical.choice,
        ``Quot.sound,
        ``SimpleC.SL.CNotation.sizeof_char,
        ``SimpleC.SL.CNotation.sizeof_uchar,
        ``SimpleC.SL.CNotation.sizeof_short,
        ``SimpleC.SL.CNotation.sizeof_ushort,
        ``SimpleC.SL.CNotation.sizeof_int,
        ``SimpleC.SL.CNotation.sizeof_uint,
        ``SimpleC.SL.CNotation.sizeof_int64,
        ``SimpleC.SL.CNotation.sizeof_uint64,
        ``SimpleC.SL.CNotation.sizeof_ptr,
        ``SimpleC.SL.CNotation.sizeof_front_end_type,
        ``SimpleC.SL.SeparationLogic.CRules.GlobalStrings,
        ``SimpleC.SL.SeparationLogic.CRules.GlobalStrings_missing,
        ``SimpleC.SL.SeparationLogic.CRules.GlobalStrings_split,
        ``SimpleC.SL.SeparationLogic.CRules.GlobalStrings_merge,
        ``SimpleC.SL.SeparationLogic.CRules.GlobalStrings_missing_split,
        ``SimpleC.SL.SeparationLogic.CRules.GlobalStrings_missing_merge,
        ``SimpleC.SL.SeparationLogic.CRules.GlobalStrings_split_existing,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules.GlobalStrings,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules.GlobalStrings_missing,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules.GlobalStrings_split,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules.GlobalStrings_merge,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules.GlobalStrings_missing_split,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules.GlobalStrings_missing_merge,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules.GlobalStrings_split_existing,
        ``SimpleC.SL.SeparationLogic.field_address
      ]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "SeparationLogic declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"SeparationLogic API contract verified for {names.size} declarations"

#check CRules
#check naive_C_Rules
#check CRules.expr
#check CRules.mstore
#check CRules.store_ptr
#check CRules.undef_store_uint64
#check CRules.store_array
#check CRules.coq_prop_andp_left
#check CRules.store_n_bytes_Z
#check CRules.store_int_range
#check CRules.store_align4_valid
#check CRules.store_uint_store_char
#check CRules.vector_cons
#check CRules.Z_to_n_bytes
#check CRules.merge_int64_equiv_merge_n_bytes
#check CRules.store_map
#check CRules.store_map_split
#check CRules.StoreCharAsElement
#check CRules.CharArray
#check CRules.IntArray
#check CRules.CharArray2
#check CRules.PtrArray2
#check CRules.CharPtrArray2
#check CRules.PtrPtrArray2
#check CRules.AsciiToZ
#check CRules.StringToList
#check CRules.store_string
#check CRules.store_string_split_to_missing_i
#check CRules.GlobalStrings
#check CRules.GlobalStrings_missing
#check CRules.GlobalStrings_split
#check CRules.GlobalStrings_merge
#check CRules.GlobalStrings_missing_split
#check CRules.GlobalStrings_missing_merge
#check CRules.GlobalStrings_split_existing
#check CRules.stringLibSig

#check naive_C_Rules.sts
#check naive_C_Rules.at_states
#check naive_C_Rules.has_tokens
#check naive_C_Rules.store_ptr
#check naive_C_Rules.Z_to_n_bytes
#check naive_C_Rules.IntArray
#check naive_C_Rules.IntArray2
#check naive_C_Rules.IntPtrArray2
#check naive_C_Rules.store_map
#check naive_C_Rules.store_string
#check naive_C_Rules.GlobalStrings
#check naive_C_Rules.GlobalStrings_split_existing
#check naive_C_Rules.stringLibSig

#check field_address
#check should_be_equal

#check_separation_logic_surface [
  CRules,
  naive_CSL,
  naive_C_Rules,
  CRules.store_byte,
  CRules.store_2byte,
  CRules.store_4byte,
  CRules.store_8byte,
  CRules.store_byte_noninit,
  CRules.store_2byte_noninit,
  CRules.store_4byte_noninit,
  CRules.store_8byte_noninit,
  CRules.store_char,
  CRules.undef_store_char,
  CRules.store_uchar,
  CRules.undef_store_uchar,
  CRules.store_short,
  CRules.undef_store_short,
  CRules.store_ushort,
  CRules.undef_store_ushort,
  CRules.store_int,
  CRules.undef_store_int,
  CRules.store_uint,
  CRules.undef_store_uint,
  CRules.store_int64,
  CRules.undef_store_int64,
  CRules.store_uint64,
  CRules.undef_store_uint64,
  CRules.store_ptr,
  CRules.undef_store_ptr,
  CRules.Invalid_store,
  CRules.Invalid_undef_store,
  CRules.dup_data_at_error,
  CRules.store_array_rec,
  CRules.store_array_missing_i_rec,
  CRules.store_array,
  CRules.store_undef_array_rec,
  CRules.store_undef_array_missing_i_rec,
  CRules.store_undef_array,
  CRules.store_align4_list,
  CRules.store_align4_n,
  CRules.store_align_list,
  CRules.store_align_n,
  CRules.poly_store,
  CRules.poly_undef_store,
  CRules.struct_padding,
  CRules.union_padding,
  CRules.coq_prop_andp_left,
  CRules.coq_prop_andp_right,
  CRules.coq_prop_imply,
  CRules.coq_prop_False_left,
  CRules.orp_sepcon_left,
  CRules.orp_sepcon_right,
  CRules.orp_sepcon_left',
  CRules.orp_sepcon_right',
  CRules.orp_sepcon_left_equiv,
  CRules.orp_sepcon_right_equiv,
  CRules.exp_right_exists,
  CRules.derivable1_imp,
  CRules.derivable1_andp_mono,
  CRules.ex_logic_equiv_andp,
  CRules.wand_equiv,
  CRules.ex_logic_equiv_sepcon,
  CRules.prop_add_left,
  CRules.truep_andp_left_equiv,
  CRules.truep_andp_right_equiv,
  CRules.sepcon_emp_equiv,
  CRules.sepcon_cancel_res_emp,
  CRules.sepcon_cancel_end,
  CRules.sepcon_prop_equiv,
  CRules.exp_exp_right,
  CRules.exp_allp_left,
  CRules.exp_allp_swap,
  CRules.allp_allp_swap,
  CRules.derivable1_wand_sepcon_adjoint,
  CRules.all_list,
  CRules.sepcon_emp_logic_equiv',
  CRules.elim_wand_emp_emp,
  CRules.dump_spatial_left,
  CRules.split_pure_and_spatial_goals,
  CRules._derivable1_andp_intros,
  CRules.add_pure_split,
  CRules.sepcon_cancel_lhs_emp,
  CRules.store_n_bytes,
  CRules.store_n_bytes_Z,
  CRules.store_n_bytes_noninit,
  CRules.store_byte_eqm,
  CRules.store_byte_equiv_store_n_bytes_Z,
  CRules.store_2byte_equiv_store_n_bytes_Z,
  CRules.store_4byte_equiv_store_n_bytes_Z,
  CRules.store_8byte_equiv_store_n_bytes_Z,
  CRules.store_byte_store_byte_noinit,
  CRules.store_2byte_store_2byte_noinit,
  CRules.store_4byte_store_4byte_noinit,
  CRules.store_8byte_store_8byte_noinit,
  CRules.store_ptr_undef_store_ptr,
  CRules.store_int_range,
  CRules.store_int_undef_store_int,
  CRules.store_char_range,
  CRules.store_char_undef_store_char,
  CRules.store_short_range,
  CRules.store_short_undef_store_short,
  CRules.store_int64_range,
  CRules.store_int64_undef_store_int64,
  CRules.store_uint_range,
  CRules.store_uint_undef_store_uint,
  CRules.store_uchar_range,
  CRules.store_uchar_undef_store_uchar,
  CRules.store_ushort_range,
  CRules.store_ushort_undef_store_ushort,
  CRules.store_uint64_range,
  CRules.store_uint64_undef_store_uint64,
  CRules.poly_store_poly_undef_store,
  CRules.dup_mstore,
  CRules.dup_store_byte_noninit,
  CRules.dup_store_byte,
  CRules.dup_store_2bytes_noninit,
  CRules.dup_store_2bytes,
  CRules.dup_store_4bytes_noninit,
  CRules.dup_store_4bytes,
  CRules.dup_store_8bytes_noninit,
  CRules.dup_store_8bytes,
  CRules.dup_undef_store_int,
  CRules.dup_store_int,
  CRules.dup_undef_store_ptr,
  CRules.dup_store_ptr,
  CRules.store_byte_cast,
  CRules.store_byte_cast',
  CRules.store_char_cast,
  CRules.store_uchar_cast,
  CRules.store_short_cast,
  CRules.store_ushort_cast,
  CRules.store_int_cast,
  CRules.store_uint_cast,
  CRules.store_int64_cast,
  CRules.store_uint64_cast,
  CRules.store_int_store_char,
  CRules.store_uint_store_char,
  CRules.undef_store_uint_undef_store_char,
  CRules.undef_store_int_undef_store_char,
  CRules.valid_store_char,
  CRules.valid_store_uchar,
  CRules.valid_undef_store_char,
  CRules.valid_undef_store_uchar,
  CRules.valid_store_short,
  CRules.valid_store_ushort,
  CRules.valid_undef_store_short,
  CRules.valid_undef_store_ushort,
  CRules.valid_store_int,
  CRules.valid_store_uint,
  CRules.valid_undef_store_int,
  CRules.valid_undef_store_uint,
  CRules.valid_store_int64,
  CRules.valid_store_uint64,
  CRules.valid_undef_store_int64,
  CRules.valid_undef_store_uint64,
  CRules.valid_store_ptr,
  CRules.valid_undef_store_ptr,
  CRules.undef_store_char_align,
  CRules.store_char_align,
  CRules.store_byte_align1,
  CRules.undef_store_uchar_align,
  CRules.store_uchar_align,
  CRules.undef_store_int_align4,
  CRules.store_int_align4,
  CRules.undef_store_uint_align4,
  CRules.store_uint_align4,
  CRules.undef_store_int64_align4,
  CRules.store_int64_align4,
  CRules.undef_store_uint64_align4,
  CRules.store_uint64_align4,
  CRules.undef_store_ptr_align4,
  CRules.store_ptr_align4,
  CRules.store_byte_valid,
  CRules.store_4byte_valid,
  CRules.store_align4_valid,
  CRules.store_align4_merge,
  CRules.store_align4_n_valid,
  CRules.store_align_valid,
  CRules.store_align_merge,
  CRules.undef_store_short_align,
  CRules.store_short_align,
  CRules.undef_store_ushort_align,
  CRules.store_ushort_align,
  CRules.store_align_n_valid,
  CRules.store_align4_to_store_align,
  CRules.store_ptr_store_uint,
  CRules.store_map,
  CRules.store_map_missing_i,
  CRules.store_map_split,
  CRules.store_map_merge,
  CRules.store_map_missing_equiv_store_map,
  CRules.store_map_equiv_store_map_missing,
  CRules.store_map_equiv,
  CRules.store_map_missing_i_equiv,
  CRules.store_map_empty,
  CRules.derivedPredSig,
  CRules.storeLibSig,
  CRules.arrayLibSig,
  CRules.array2LibSig,
  CRules.ptrArray2LibSig,
  CRules.mapLibSig,
  CRules.vector_cons,
  CRules.vector_head,
  CRules.vector_tail,
  CRules.vector_head_cons,
  CRules.vector_tail_cons,
  CRules.vector_cons_eta,
  CRules.bytes_eqm,
  CRules.n_bytes_to_Z,
  CRules.Z_to_n_bytes,
  CRules.merge_n_bytes,
  CRules.eqm_iff_mod_eq,
  CRules.n_bytes_to_Z_cons,
  CRules.eqm_bytes_to_Z_eq,
  CRules.Z_to_n_bytes_succ,
  CRules.Z_to_n_bytes_to_Z,
  CRules.merge_short_equiv_merge_n_bytes,
  CRules.merge_int_equiv_merge_n_bytes,
  CRules.merge_int64_equiv_merge_n_bytes,
  CRules.dup_data_at_error_prop,
  CRules.StoreCharAsElement,
  CRules.StoreUCharAsElement,
  CRules.StoreShortAsElement,
  CRules.StoreUShortAsElement,
  CRules.StoreIntAsElement,
  CRules.StoreUIntAsElement,
  CRules.StoreInt64AsElement,
  CRules.StoreUInt64AsElement,
  CRules.StorePtrAsElement,
  CRules.CharArray,
  CRules.UCharArray,
  CRules.ShortArray,
  CRules.UShortArray,
  CRules.IntArray,
  CRules.UIntArray,
  CRules.Int64Array,
  CRules.UInt64Array,
  CRules.PtrArray,
  CRules.CharArray2,
  CRules.UCharArray2,
  CRules.ShortArray2,
  CRules.UShortArray2,
  CRules.IntArray2,
  CRules.UIntArray2,
  CRules.Int64Array2,
  CRules.UInt64Array2,
  CRules.PtrArray2,
  CRules.CharPtrArray2,
  CRules.UCharPtrArray2,
  CRules.ShortPtrArray2,
  CRules.UShortPtrArray2,
  CRules.IntPtrArray2,
  CRules.UIntPtrArray2,
  CRules.Int64PtrArray2,
  CRules.UInt64PtrArray2,
  CRules.PtrPtrArray2,
  CRules.AsciiToZ,
  CRules.ZToAscii,
  CRules.string_length,
  CRules.c_string,
  CRules.valid_char,
  CRules.valid_string,
  CRules.StringLength,
  CRules.StringToList_nat,
  CRules.StringToList,
  CRules.ListToString,
  CRules.ZToAscii_AsciiToZ,
  CRules.ListToString_StringToList_nat_full,
  CRules.ListToString_StringToList,
  CRules.valid_stringLit,
  CRules.store_string,
  CRules.store_stringLit,
  CRules.c_string_Zlength,
  CRules.StringToList_nat_length,
  CRules.StringToList_length,
  CRules.StringToList_c_length,
  CRules.store_string_length,
  CRules.store_stringLit_length,
  CRules.store_string_split_to_missing_i,
  CRules.store_stringLit_split_to_missing_i,
  CRules.AsciiToZ_range,
  CRules.GlobalStrings,
  CRules.GlobalStrings_missing,
  CRules.GlobalStrings_split,
  CRules.GlobalStrings_merge,
  CRules.GlobalStrings_missing_split,
  CRules.GlobalStrings_missing_merge,
  CRules.GlobalStrings_split_existing,
  CRules.stringLibSig,
  naive_C_Rules.GlobalStrings,
  naive_C_Rules.GlobalStrings_missing,
  naive_C_Rules.GlobalStrings_split,
  naive_C_Rules.GlobalStrings_merge,
  naive_C_Rules.GlobalStrings_missing_split,
  naive_C_Rules.GlobalStrings_missing_merge,
  naive_C_Rules.GlobalStrings_split_existing,
  naive_C_Rules.stringLibSig,
  field_address,
  should_be_equal
]

#check_separation_logic_contract [
  CRules,
  naive_CSL,
  naive_C_Rules,
  CRules.GlobalStrings,
  CRules.GlobalStrings_missing,
  CRules.GlobalStrings_split,
  CRules.GlobalStrings_merge,
  CRules.GlobalStrings_missing_split,
  CRules.GlobalStrings_missing_merge,
  CRules.GlobalStrings_split_existing,
  CRules.stringLibSig,
  naive_C_Rules.GlobalStrings,
  naive_C_Rules.GlobalStrings_missing,
  naive_C_Rules.GlobalStrings_split,
  naive_C_Rules.GlobalStrings_merge,
  naive_C_Rules.GlobalStrings_missing_split,
  naive_C_Rules.GlobalStrings_missing_merge,
  naive_C_Rules.GlobalStrings_split_existing,
  naive_C_Rules.stringLibSig,
  field_address,
  should_be_equal
] => 12552654018554894991

example : CRules = SimpleC.SL.Assertion.SL := rfl
example : naive_C_Rules = naive_CSL.toSeparationLogicSig := rfl

example (p v : Int) :
    CRules.store_ptr p v =
      SimpleC.SL.CommonAssertion.DerivedPredSig.store_ptr CRules p v := rfl

example (v : Int) (n : Nat) :
    CRules.Z_to_n_bytes v n =
      SimpleC.SL.StoreAux.StoreLibSig.Z_to_n_bytes v n := rfl

example : CRules.IntArray.elementStore =
    SimpleC.SL.ArrayLib.StoreIntAsElement
      CRules CRules.derivedPredSig CRules.storeLibSig := rfl

example : CRules.IntArray2.elementStore =
    SimpleC.SL.ArrayLib.StoreIntAsElement
      CRules CRules.derivedPredSig CRules.storeLibSig := rfl

example : CRules.IntPtrArray2.elementStore =
    SimpleC.SL.ArrayLib.StoreIntAsElement
      CRules CRules.derivedPredSig CRules.storeLibSig := rfl

example (p : Int) (s : List Int) :
    CRules.store_string p s =
      SimpleC.SL.StringLib.StringLibSig.store_string
        CRules CRules.derivedPredSig CRules.storeLibSig p s := rfl

example : CRules.stringLibSig.GlobalStrings = CRules.GlobalStrings := rfl
example : CRules.stringLibSig.GlobalStrings_missing =
    CRules.GlobalStrings_missing := rfl
example : naive_C_Rules.stringLibSig.GlobalStrings =
    naive_C_Rules.GlobalStrings := rfl

example {A : Type} (x y : A) : should_be_equal x y := by
  trivial

#print axioms SimpleC.SL.SeparationLogic.CRules.GlobalStrings_split
#print axioms SimpleC.SL.SeparationLogic.naive_C_Rules.GlobalStrings_split
#print axioms SimpleC.SL.SeparationLogic.field_address
#print axioms SimpleC.SL.SeparationLogic.should_be_equal

end SeparationLogicApiTests
