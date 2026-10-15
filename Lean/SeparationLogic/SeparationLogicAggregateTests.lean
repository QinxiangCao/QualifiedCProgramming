import SimpleC.SL.SeparationLogic
import Lean.Util.CollectAxioms
import Lean.Util.CollectMVars

namespace SeparationLogicAggregateTests

open SimpleC.SL
open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion
open SimpleC.SL.SeparationLogic
open Lean Elab Command

syntax (name := checkAggregateRulesSurface)
  "#check_aggregate_rules_surface " "[" term,* "]" " => " num : command

syntax (name := auditP08FoundationAxioms)
  "#audit_p0_8_foundation_axioms " "[" ident,* "]" : command

syntax (name := auditP08StringAxioms)
  "#audit_p0_8_string_axioms " ident " [" ident,* "]" : command

private def p08FoundationAxioms : Array Name := #[
  ``propext, ``Classical.choice, ``Quot.sound,
  ``SimpleC.SL.CNotation.sizeof_struct_type,
  ``SimpleC.SL.CNotation.sizeof_union_type,
  ``SimpleC.SL.CNotation.sizeof_enum_type,
  ``SimpleC.SL.CNotation.sizeof_alias_type
]

private def auditP08Axioms (names allowed : Array Name) : CommandElabM Unit := do
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "P0-8 declaration '{name}' depends on disallowed axiom '{axiomName}'"

elab_rules : command
  | `(#check_aggregate_rules_surface [$terms:term,*] => $expected:num) => do
      let terms := terms.getElems
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number aggregate surface hash"
      let mut actual := hash terms.size
      for term in terms do
        let (value, valueType) <-
          withRef term <| withoutModifyingEnv <| runTermElabM fun _ =>
            Term.withDeclName `_aggregate_rules_surface_check do
              let value <- Term.elabTerm term none
              Term.synthesizeSyntheticMVarsNoPostponing
              let value <- Lean.instantiateMVars value
              Lean.Meta.check value
              let valueType <- Lean.instantiateMVars (← Lean.Meta.inferType value)
              let mvarIds :=
                (valueType.collectMVars (value.collectMVars {})).result
              for mvarId in mvarIds do
                let mvarType <- Lean.instantiateMVars (← mvarId.getType)
                if mvarType.isConstOf ``CArchSig ||
                    mvarType.isConstOf ``CEndianSig then
                  throwErrorAt term
                    "aggregate facade left an architecture/endian parameter unresolved"
              pure (value, valueType)
        actual := mixHash actual (mixHash (hash value) (hash valueType))
      unless actual = expected.toUInt64 do
        throwError "P0-8 aggregate surface changed: expected {expected}, got {actual}"
      logInfo m!"P0-8 aggregate surface verified for {terms.size} entries"

elab_rules : command
  | `(#audit_p0_8_foundation_axioms [$ids:ident,*]) => do
      let names <- ids.getElems.mapM fun id =>
        liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      auditP08Axioms names p08FoundationAxioms
      logInfo m!"P0-8 foundation axiom boundary verified for {names.size} declarations"
  | `(#audit_p0_8_string_axioms $moduleId:ident [$ids:ident,*]) => do
      let moduleName <- liftCoreM <| realizeGlobalConstNoOverloadWithInfo moduleId
      let names <- ids.getElems.mapM fun id =>
        liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      let fields := #[
        "GlobalStrings", "GlobalStrings_missing", "GlobalStrings_split",
        "GlobalStrings_merge", "GlobalStrings_missing_split",
        "GlobalStrings_missing_merge", "GlobalStrings_split_existing"
      ]
      let mut allowed := p08FoundationAxioms
      for field in fields do
        allowed := allowed.push (.str moduleName field)
      auditP08Axioms names allowed
      logInfo m!"P0-8 String axiom boundary verified for {moduleName}"

#check_aggregate_rules_surface [
  (fun (R : AggregateRules) => R.sizeof_front_end_type),
  (fun (R : AggregateRules) => R.sizeof_int),
  (fun (R : AggregateRules) => R.sizeof_char),
  (fun (R : AggregateRules) => R.sizeof_int64),
  (fun (R : AggregateRules) => R.sizeof_short),
  (fun (R : AggregateRules) => R.sizeof_uint),
  (fun (R : AggregateRules) => R.sizeof_uchar),
  (fun (R : AggregateRules) => R.sizeof_uint64),
  (fun (R : AggregateRules) => R.sizeof_int128),
  (fun (R : AggregateRules) => R.sizeof_uint128),
  (fun (R : AggregateRules) => R.sizeof_ushort),
  (fun (R : AggregateRules) => R.sizeof_float),
  (fun (R : AggregateRules) => R.sizeof_double),
  (fun (R : AggregateRules) => R.sizeof_long_double),
  (fun (R : AggregateRules) => R.sizeof_ptr),
  (fun (R : AggregateRules) => R.eval_addr),
  (fun (R : AggregateRules) => R.addr_of_array_subst),
  (fun (R : AggregateRules) => R.addr_of_array_subst'),
  (fun (R : AggregateRules) => R.const_array_pi),
  (fun (R : AggregateRules) => R.const_array_pi'),
  (fun (R : AggregateRules) => R.addr_of_arrow_field),
  (fun (R : AggregateRules) => R.addr_max_unsigned),
  (fun (R : AggregateRules) => R.ptr_size),
  (fun (R : AggregateRules) => R.ptr_align),
  (fun (R : AggregateRules) => R.ptr_size_Z),
  (fun (R : AggregateRules) => R.ptr_width_Z),
  (fun (R : AggregateRules) => R.aligned),
  (fun (R : AggregateRules) => R.merge_short),
  (fun (R : AggregateRules) => R.merge_int),
  (fun (R : AggregateRules) => R.merge_int64),
  (fun (R : AggregateRules) => R.vec1),
  (fun (R : AggregateRules) => R.vec2),
  (fun (R : AggregateRules) => R.vec4),
  (fun (R : AggregateRules) => R.vec8),
  (fun (R : AggregateRules) => R.ptr_size_32_or_64),
  (fun (R : AggregateRules) => R.ptr_size_pos),
  (fun (R : AggregateRules) => R.ptr_align_pos),
  (fun (R : AggregateRules) => R.ptr_aligned_aligned_4),
  (fun (R : AggregateRules) => R.addr_max_unsigned_ge_7),
  (fun (R : AggregateRules) => R.ptr_size_fits_addr),
  (fun (R : AggregateRules) => R.int_max_fits_addr),
  (fun (R : AggregateRules) => R.merge_n_bytes_self),
  (fun (R : AggregateRules) => R.merge_byte_equiv_merge_n_bytes),
  (fun (R : AggregateRules) => R.merge_short_eqm),
  (fun (R : AggregateRules) => R.merge_int_eqm),
  (fun (R : AggregateRules) => R.merge_int64_eqm),
  (fun (R : AggregateRules) => R.merge_short_value_eqm),
  (fun (R : AggregateRules) => R.merge_int_value_eqm),
  (fun (R : AggregateRules) => R.merge_int64_value_eqm),
  (fun (R : AggregateRules) => R.valid_addr_range),
  (fun (R : AggregateRules) => R.valid_object),
  (fun (R : AggregateRules) => R.isvalidptr_char),
  (fun (R : AggregateRules) => R.isvalidptr_short),
  (fun (R : AggregateRules) => R.isvalidptr_int),
  (fun (R : AggregateRules) => R.isvalidptr_int64),
  (fun (R : AggregateRules) => R.isvalidptr_int128),
  (fun (R : AggregateRules) => R.isvalidptr_float),
  (fun (R : AggregateRules) => R.isvalidptr_double),
  (fun (R : AggregateRules) => R.isvalidptr_long_double),
  (fun (R : AggregateRules) => R.isvalidptr),
  (fun (R : AggregateRules) => R.valid_ptr_value),
  (fun (R : AggregateRules) => R.byte_eqm_unsigned_last_8),
  (fun (R : AggregateRules) => R.byte_eqm_signed_last_8),
  (fun (R : AggregateRules) => R.store_int64_store_char),
  (fun (R : AggregateRules) => R.store_uint64_store_uchar),
  (fun (R : AggregateRules) => R.store_int64_store_uchar),
  (fun (R : AggregateRules) => R.store_uint64_store_char),
  (fun (R : AggregateRules) => R.merge_int64_by_ints),
  (fun (R : AggregateRules) => R.signed_int_of_bytes),
  (fun (R : AggregateRules) => R.unsigned_int_of_bytes),
  (fun (R : AggregateRules) => R.merge_int_signed_of_bytes),
  (fun (R : AggregateRules) => R.merge_int_unsigned_of_bytes),
  (fun (R : AggregateRules) => R.signed_int_of_bytes_range),
  (fun (R : AggregateRules) => R.unsigned_int_of_bytes_range),
  (fun (R : AggregateRules) => R.store_int64_store_int),
  (fun (R : AggregateRules) => R.store_uint64_store_uint),
  (fun (R : AggregateRules) => R.store_int64_store_uint),
  (fun (R : AggregateRules) => R.store_uint64_store_int),
  (fun (R : AggregateRules) => R.store_bytes_noninit_align),
  (fun (R : AggregateRules) => R.undef_store_ptr_undef_store_uint64),
  (fun (R : AggregateRules) => R.undef_store_ptr_undef_store_int64),
  (fun (R : AggregateRules) => R.undef_store_ptr_align),
  (fun (R : AggregateRules) => R.store_ptr_align),
  (fun (R : AggregateRules) => R.store_ptr_store_uint64),
  (fun (R : AggregateRules) => R.ELEMENT_STORE),
  (fun (R : AggregateRules) => R.ArrayLib),
  (fun (R : AggregateRules) => R.store_array_rec_length),
  (fun (R : AggregateRules) => R.store_array_rec_Zlength),
  (fun (R : AggregateRules) => R.store_array_rec_nil),
  (fun (R : AggregateRules) => R.store_array_rec_valid),
  (fun (R : AggregateRules) => R.store_array_length),
  (fun (R : AggregateRules) => R.store_array_Zlength),
  (fun (R : AggregateRules) => R.store_array_valid),
  (fun (R : AggregateRules) => R.store_array_missing_i_rec_length),
  (fun (R : AggregateRules) => R.store_array_missing_i_rec_Zlength),
  (fun (R : AggregateRules) => R.store_array_missing_i_rec_valid),
  (fun (R : AggregateRules) => R.store_array_missing_i_valid),
  (fun (R : AggregateRules) => R.store_array_rec_split_to_missing_i),
  (fun (R : AggregateRules) => R.store_array_split_to_missing_i),
  (fun (R : AggregateRules) => R.store_array_missing_i_merge_to_rec),
  (fun (R : AggregateRules) => R.store_array_missing_i_merge_to_array),
  (fun (R : AggregateRules) => @R.repeat_Z),
  (fun (R : AggregateRules) => @R.repeat_Z_tail),
  (fun (R : AggregateRules) => @R.SingleSome),
  (fun (R : AggregateRules) => R.Array2Lib),
  (fun (R : AggregateRules) => R.store_array_rec_to_undef_array_rec),
  (fun (R : AggregateRules) => R.store_array_to_undef_array),
  (fun (R : AggregateRules) => R.store_undef_array_rec_split_to_missing_i),
  (fun (R : AggregateRules) => R.store_undef_array_split_to_missing_i),
  (fun (R : AggregateRules) => R.Array3Lib),
  (fun (R : AggregateRules) => R.PtrArray2Lib),
  (fun (R : AggregateRules) => R.AsciiToZ),
  (fun (R : AggregateRules) => R.AsciiToZ_range),
  (fun (R : AggregateRules) => R.CharArray),
  (fun (R : AggregateRules) => R.CharArray2),
  (fun (R : AggregateRules) => R.CharArray3),
  (fun (R : AggregateRules) => R.CharPtrArray2),
  (fun (R : AggregateRules) => R.DoubleArray),
  (fun (R : AggregateRules) => R.DoubleArray2),
  (fun (R : AggregateRules) => R.DoubleArray3),
  (fun (R : AggregateRules) => R.FiniteDoubleArray),
  (fun (R : AggregateRules) => R.FiniteDoubleArray2),
  (fun (R : AggregateRules) => R.FiniteDoubleArray3),
  (fun (R : AggregateRules) => R.FiniteFloatArray),
  (fun (R : AggregateRules) => R.FiniteFloatArray2),
  (fun (R : AggregateRules) => R.FiniteFloatArray3),
  (fun (R : AggregateRules) => R.FiniteLongDoubleArray),
  (fun (R : AggregateRules) => R.FiniteLongDoubleArray2),
  (fun (R : AggregateRules) => R.FiniteLongDoubleArray3),
  (fun (R : AggregateRules) => R.FloatArray),
  (fun (R : AggregateRules) => R.FloatArray2),
  (fun (R : AggregateRules) => R.FloatArray3),
  (fun (R : AggregateRules) => R.Int128Array),
  (fun (R : AggregateRules) => R.Int128Array2),
  (fun (R : AggregateRules) => R.Int128Array3),
  (fun (R : AggregateRules) => R.Int64Array),
  (fun (R : AggregateRules) => R.Int64Array2),
  (fun (R : AggregateRules) => R.Int64Array3),
  (fun (R : AggregateRules) => R.Int64PtrArray2),
  (fun (R : AggregateRules) => R.IntArray),
  (fun (R : AggregateRules) => R.IntArray2),
  (fun (R : AggregateRules) => R.IntArray3),
  (fun (R : AggregateRules) => R.IntPtrArray2),
  (fun (R : AggregateRules) => R.Invalid_store),
  (fun (R : AggregateRules) => R.Invalid_undef_store),
  (fun (R : AggregateRules) => R.ListToString),
  (fun (R : AggregateRules) => R.ListToString_StringToList),
  (fun (R : AggregateRules) => R.ListToString_StringToList_nat_full),
  (fun (R : AggregateRules) => R.LongDoubleArray),
  (fun (R : AggregateRules) => R.LongDoubleArray2),
  (fun (R : AggregateRules) => R.LongDoubleArray3),
  (fun (R : AggregateRules) => R.PtrArray),
  (fun (R : AggregateRules) => R.PtrArray2),
  (fun (R : AggregateRules) => R.PtrArray3),
  (fun (R : AggregateRules) => R.PtrPtrArray2),
  (fun (R : AggregateRules) => R.ShortArray),
  (fun (R : AggregateRules) => R.ShortArray2),
  (fun (R : AggregateRules) => R.ShortArray3),
  (fun (R : AggregateRules) => R.ShortPtrArray2),
  (fun (R : AggregateRules) => R.StoreCharAsElement),
  (fun (R : AggregateRules) => R.StoreDoubleAsElement),
  (fun (R : AggregateRules) => R.StoreFiniteDoubleAsElement),
  (fun (R : AggregateRules) => R.StoreFiniteFloatAsElement),
  (fun (R : AggregateRules) => R.StoreFiniteLongDoubleAsElement),
  (fun (R : AggregateRules) => R.StoreFloatAsElement),
  (fun (R : AggregateRules) => R.StoreInt128AsElement),
  (fun (R : AggregateRules) => R.StoreInt64AsElement),
  (fun (R : AggregateRules) => R.StoreIntAsElement),
  (fun (R : AggregateRules) => R.StoreLongDoubleAsElement),
  (fun (R : AggregateRules) => R.StorePtrAsElement),
  (fun (R : AggregateRules) => R.StoreShortAsElement),
  (fun (R : AggregateRules) => R.StoreUCharAsElement),
  (fun (R : AggregateRules) => R.StoreUInt128AsElement),
  (fun (R : AggregateRules) => R.StoreUInt64AsElement),
  (fun (R : AggregateRules) => R.StoreUIntAsElement),
  (fun (R : AggregateRules) => R.StoreUShortAsElement),
  (fun (R : AggregateRules) => R.StringLength),
  (fun (R : AggregateRules) => R.StringToList),
  (fun (R : AggregateRules) => R.StringToList_c_length),
  (fun (R : AggregateRules) => R.StringToList_length),
  (fun (R : AggregateRules) => R.StringToList_nat),
  (fun (R : AggregateRules) => R.StringToList_nat_length),
  (fun (R : AggregateRules) => R.UCharArray),
  (fun (R : AggregateRules) => R.UCharArray2),
  (fun (R : AggregateRules) => R.UCharArray3),
  (fun (R : AggregateRules) => R.UCharPtrArray2),
  (fun (R : AggregateRules) => R.UInt128Array),
  (fun (R : AggregateRules) => R.UInt128Array2),
  (fun (R : AggregateRules) => R.UInt128Array3),
  (fun (R : AggregateRules) => R.UInt64Array),
  (fun (R : AggregateRules) => R.UInt64Array2),
  (fun (R : AggregateRules) => R.UInt64Array3),
  (fun (R : AggregateRules) => R.UInt64PtrArray2),
  (fun (R : AggregateRules) => R.UIntArray),
  (fun (R : AggregateRules) => R.UIntArray2),
  (fun (R : AggregateRules) => R.UIntArray3),
  (fun (R : AggregateRules) => R.UIntPtrArray2),
  (fun (R : AggregateRules) => R.UShortArray),
  (fun (R : AggregateRules) => R.UShortArray2),
  (fun (R : AggregateRules) => R.UShortArray3),
  (fun (R : AggregateRules) => R.UShortPtrArray2),
  (fun (R : AggregateRules) => R.ZToAscii),
  (fun (R : AggregateRules) => R.ZToAscii_AsciiToZ),
  (fun (R : AggregateRules) => R.Z_to_n_bytes),
  (fun (R : AggregateRules) => R.Z_to_n_bytes_to_Z),
  (fun (R : AggregateRules) => R._derivable1_andp_intros),
  (fun (R : AggregateRules) => R.add_pure_split),
  (fun (R : AggregateRules) => R.aligned_8_aligned_4),
  (fun (R : AggregateRules) => R.all_list),
  (fun (R : AggregateRules) => R.allp_allp_swap),
  (fun (R : AggregateRules) => R.array2LibSig),
  (fun (R : AggregateRules) => R.array3LibSig),
  (fun (R : AggregateRules) => R.arrayLibSig),
  (fun (R : AggregateRules) => R.bytes_eqm),
  (fun (R : AggregateRules) => R.c_string),
  (fun (R : AggregateRules) => R.c_string_Zlength),
  (fun (R : AggregateRules) => R.coq_prop_False_left),
  (fun (R : AggregateRules) => R.coq_prop_andp_left),
  (fun (R : AggregateRules) => R.coq_prop_andp_right),
  (fun (R : AggregateRules) => R.coq_prop_imply),
  (fun (R : AggregateRules) => R.derivable1),
  (fun (R : AggregateRules) => R.derivable1_andp_mono),
  (fun (R : AggregateRules) => R.derivable1_imp),
  (fun (R : AggregateRules) => R.derivable1_wand_sepcon_adjoint),
  (fun (R : AggregateRules) => R.derivedPredSig),
  (fun (R : AggregateRules) => R.dump_spatial_left),
  (fun (R : AggregateRules) => R.dup_data_at_error),
  (fun (R : AggregateRules) => R.dup_data_at_error_prop),
  (fun (R : AggregateRules) => R.dup_mstore),
  (fun (R : AggregateRules) => R.dup_store_2bytes),
  (fun (R : AggregateRules) => R.dup_store_2bytes_noninit),
  (fun (R : AggregateRules) => R.dup_store_4bytes),
  (fun (R : AggregateRules) => R.dup_store_4bytes_noninit),
  (fun (R : AggregateRules) => R.dup_store_8bytes),
  (fun (R : AggregateRules) => R.dup_store_8bytes_noninit),
  (fun (R : AggregateRules) => R.dup_store_byte),
  (fun (R : AggregateRules) => R.dup_store_byte_noninit),
  (fun (R : AggregateRules) => R.dup_store_int),
  (fun (R : AggregateRules) => R.dup_store_ptr),
  (fun (R : AggregateRules) => R.dup_undef_store_int),
  (fun (R : AggregateRules) => R.dup_undef_store_ptr),
  (fun (R : AggregateRules) => R.elim_wand_emp_emp),
  (fun (R : AggregateRules) => R.eqm_bytes_to_Z_eq),
  (fun (R : AggregateRules) => R.eqm_iff_mod_eq),
  (fun (R : AggregateRules) => R.ex_logic_equiv_andp),
  (fun (R : AggregateRules) => R.ex_logic_equiv_sepcon),
  (fun (R : AggregateRules) => R.exp_allp_left),
  (fun (R : AggregateRules) => R.exp_allp_swap),
  (fun (R : AggregateRules) => R.exp_exp_right),
  (fun (R : AggregateRules) => R.exp_right_exists),
  (fun (R : AggregateRules) => R.expr),
  (fun (R : AggregateRules) => R.front_end_type_value),
  (fun (R : AggregateRules) => R.mapLibSig),
  (fun (R : AggregateRules) => R.merge_int64_equiv_merge_n_bytes),
  (fun (R : AggregateRules) => R.merge_int_equiv_merge_n_bytes),
  (fun (R : AggregateRules) => R.merge_n_bytes),
  (fun (R : AggregateRules) => R.merge_short_equiv_merge_n_bytes),
  (fun (R : AggregateRules) => R.mstore),
  (fun (R : AggregateRules) => R.n_bytes_to_Z),
  (fun (R : AggregateRules) => R.orp_sepcon_left),
  (fun (R : AggregateRules) => R.orp_sepcon_left_equiv),
  (fun (R : AggregateRules) => R.orp_sepcon_right),
  (fun (R : AggregateRules) => R.orp_sepcon_right_equiv),
  (fun (R : AggregateRules) => R.poly_store),
  (fun (R : AggregateRules) => R.poly_store_poly_undef_store),
  (fun (R : AggregateRules) => R.poly_undef_store),
  (fun (R : AggregateRules) => R.prop_add_left),
  (fun (R : AggregateRules) => R.ptrArray2LibSig),
  (fun (R : AggregateRules) => R.sepcon_cancel_end),
  (fun (R : AggregateRules) => R.sepcon_cancel_lhs_emp),
  (fun (R : AggregateRules) => R.sepcon_cancel_res_emp),
  (fun (R : AggregateRules) => R.sepcon_emp_equiv),
  (fun (R : AggregateRules) => R.sepcon_emp_logic_equiv),
  (fun (R : AggregateRules) => R.sepcon_prop_equiv),
  (fun (R : AggregateRules) => R.split_pure_and_spatial_goals),
  (fun (R : AggregateRules) => R.storeLibSig),
  (fun (R : AggregateRules) => R.store_16byte),
  (fun (R : AggregateRules) => R.store_16byte_noninit),
  (fun (R : AggregateRules) => R.store_16byte_store_16byte_noinit),
  (fun (R : AggregateRules) => R.store_2byte),
  (fun (R : AggregateRules) => R.store_2byte_equiv_store_n_bytes_Z),
  (fun (R : AggregateRules) => R.store_2byte_noninit),
  (fun (R : AggregateRules) => R.store_2byte_store_2byte_noinit),
  (fun (R : AggregateRules) => R.store_4byte),
  (fun (R : AggregateRules) => R.store_4byte_equiv_store_n_bytes_Z),
  (fun (R : AggregateRules) => R.store_4byte_noninit),
  (fun (R : AggregateRules) => R.store_4byte_store_4byte_noinit),
  (fun (R : AggregateRules) => R.store_4byte_valid),
  (fun (R : AggregateRules) => R.store_8byte),
  (fun (R : AggregateRules) => R.store_8byte_equiv_store_n_bytes_Z),
  (fun (R : AggregateRules) => R.store_8byte_noninit),
  (fun (R : AggregateRules) => R.store_8byte_store_8byte_noinit),
  (fun (R : AggregateRules) => R.store_align4_list),
  (fun (R : AggregateRules) => R.store_align4_merge),
  (fun (R : AggregateRules) => R.store_align4_n),
  (fun (R : AggregateRules) => R.store_align4_n_valid),
  (fun (R : AggregateRules) => R.store_align4_to_store_align),
  (fun (R : AggregateRules) => R.store_align4_valid),
  (fun (R : AggregateRules) => R.store_align_list),
  (fun (R : AggregateRules) => R.store_align_merge),
  (fun (R : AggregateRules) => R.store_align_n),
  (fun (R : AggregateRules) => R.store_align_n_valid),
  (fun (R : AggregateRules) => R.store_align_valid),
  (fun (R : AggregateRules) => R.store_array),
  (fun (R : AggregateRules) => R.store_array_missing_i_rec),
  (fun (R : AggregateRules) => R.store_array_rec),
  (fun (R : AggregateRules) => R.store_byte),
  (fun (R : AggregateRules) => R.store_byte_align1),
  (fun (R : AggregateRules) => R.store_byte_cast),
  (fun (R : AggregateRules) => R.store_byte_eqm),
  (fun (R : AggregateRules) => R.store_byte_equiv_store_n_bytes_Z),
  (fun (R : AggregateRules) => R.store_byte_noninit),
  (fun (R : AggregateRules) => R.store_byte_store_byte_noinit),
  (fun (R : AggregateRules) => R.store_byte_valid),
  (fun (R : AggregateRules) => R.store_bytes),
  (fun (R : AggregateRules) => R.store_bytes_noninit),
  (fun (R : AggregateRules) => R.store_bytes_store_bytes_noninit),
  (fun (R : AggregateRules) => R.store_char),
  (fun (R : AggregateRules) => R.store_char_align),
  (fun (R : AggregateRules) => R.store_char_cast),
  (fun (R : AggregateRules) => R.store_char_range),
  (fun (R : AggregateRules) => R.store_char_undef_store_char),
  (fun (R : AggregateRules) => R.store_double),
  (fun (R : AggregateRules) => R.store_double_align),
  (fun (R : AggregateRules) => R.store_double_align4),
  (fun (R : AggregateRules) => R.store_double_aligned8),
  (fun (R : AggregateRules) => R.store_double_undef_store_double),
  (fun (R : AggregateRules) => R.store_finite_double),
  (fun (R : AggregateRules) => R.store_finite_double_align),
  (fun (R : AggregateRules) => R.store_finite_double_aligned8),
  (fun (R : AggregateRules) => R.store_finite_double_undef_store_finite_double),
  (fun (R : AggregateRules) => R.store_finite_float),
  (fun (R : AggregateRules) => R.store_finite_float_align),
  (fun (R : AggregateRules) => R.store_finite_float_aligned4),
  (fun (R : AggregateRules) => R.store_finite_float_undef_store_finite_float),
  (fun (R : AggregateRules) => R.store_finite_long_double),
  (fun (R : AggregateRules) => R.store_finite_long_double_align),
  (fun (R : AggregateRules) => R.store_finite_long_double_aligned8),
  (fun (R : AggregateRules) => R.store_finite_long_double_undef_store_finite_long_double),
  (fun (R : AggregateRules) => R.store_float),
  (fun (R : AggregateRules) => R.store_float_align),
  (fun (R : AggregateRules) => R.store_float_align4),
  (fun (R : AggregateRules) => R.store_float_aligned4),
  (fun (R : AggregateRules) => R.store_float_undef_store_float),
  (fun (R : AggregateRules) => R.store_int),
  (fun (R : AggregateRules) => R.store_int128),
  (fun (R : AggregateRules) => R.store_int128_align),
  (fun (R : AggregateRules) => R.store_int128_range),
  (fun (R : AggregateRules) => R.store_int128_undef_store_int128),
  (fun (R : AggregateRules) => R.store_int64),
  (fun (R : AggregateRules) => R.store_int64_align4),
  (fun (R : AggregateRules) => R.store_int64_cast),
  (fun (R : AggregateRules) => R.store_int64_range),
  (fun (R : AggregateRules) => R.store_int64_undef_store_int64),
  (fun (R : AggregateRules) => R.store_int_align4),
  (fun (R : AggregateRules) => R.store_int_cast),
  (fun (R : AggregateRules) => R.store_int_range),
  (fun (R : AggregateRules) => R.store_int_store_char),
  (fun (R : AggregateRules) => R.store_int_undef_store_int),
  (fun (R : AggregateRules) => R.store_long_double),
  (fun (R : AggregateRules) => R.store_long_double_align),
  (fun (R : AggregateRules) => R.store_long_double_aligned8),
  (fun (R : AggregateRules) => R.store_long_double_undef_store_long_double),
  (fun (R : AggregateRules) => R.store_map),
  (fun (R : AggregateRules) => R.store_map_empty),
  (fun (R : AggregateRules) => R.store_map_equiv),
  (fun (R : AggregateRules) => R.store_map_equiv_store_map_missing),
  (fun (R : AggregateRules) => R.store_map_merge),
  (fun (R : AggregateRules) => R.store_map_missing_equiv_store_map),
  (fun (R : AggregateRules) => R.store_map_missing_i),
  (fun (R : AggregateRules) => R.store_map_missing_i_equiv),
  (fun (R : AggregateRules) => R.store_map_split),
  (fun (R : AggregateRules) => R.store_n_bytes),
  (fun (R : AggregateRules) => R.store_n_bytes_Z),
  (fun (R : AggregateRules) => R.store_n_bytes_noninit),
  (fun (R : AggregateRules) => R.store_ptr),
  (fun (R : AggregateRules) => R.store_ptr_align4),
  (fun (R : AggregateRules) => R.store_ptr_store_uint),
  (fun (R : AggregateRules) => R.store_ptr_undef_store_ptr),
  (fun (R : AggregateRules) => R.store_short),
  (fun (R : AggregateRules) => R.store_short_align),
  (fun (R : AggregateRules) => R.store_short_cast),
  (fun (R : AggregateRules) => R.store_short_range),
  (fun (R : AggregateRules) => R.store_short_undef_store_short),
  (fun (R : AggregateRules) => R.store_string),
  (fun (R : AggregateRules) => R.store_stringLit),
  (fun (R : AggregateRules) => R.store_stringLit_length),
  (fun (R : AggregateRules) => R.store_stringLit_split_to_missing_i),
  (fun (R : AggregateRules) => R.store_string_length),
  (fun (R : AggregateRules) => R.store_string_split_to_missing_i),
  (fun (R : AggregateRules) => R.store_uchar),
  (fun (R : AggregateRules) => R.store_uchar_align),
  (fun (R : AggregateRules) => R.store_uchar_cast),
  (fun (R : AggregateRules) => R.store_uchar_range),
  (fun (R : AggregateRules) => R.store_uchar_undef_store_uchar),
  (fun (R : AggregateRules) => R.store_uint),
  (fun (R : AggregateRules) => R.store_uint128),
  (fun (R : AggregateRules) => R.store_uint128_align),
  (fun (R : AggregateRules) => R.store_uint128_range),
  (fun (R : AggregateRules) => R.store_uint128_undef_store_uint128),
  (fun (R : AggregateRules) => R.store_uint64),
  (fun (R : AggregateRules) => R.store_uint64_align4),
  (fun (R : AggregateRules) => R.store_uint64_cast),
  (fun (R : AggregateRules) => R.store_uint64_range),
  (fun (R : AggregateRules) => R.store_uint64_undef_store_uint64),
  (fun (R : AggregateRules) => R.store_uint_align4),
  (fun (R : AggregateRules) => R.store_uint_cast),
  (fun (R : AggregateRules) => R.store_uint_range),
  (fun (R : AggregateRules) => R.store_uint_store_char),
  (fun (R : AggregateRules) => R.store_uint_undef_store_uint),
  (fun (R : AggregateRules) => R.store_undef_array),
  (fun (R : AggregateRules) => R.store_undef_array_missing_i_rec),
  (fun (R : AggregateRules) => R.store_undef_array_rec),
  (fun (R : AggregateRules) => R.store_ushort),
  (fun (R : AggregateRules) => R.store_ushort_align),
  (fun (R : AggregateRules) => R.store_ushort_cast),
  (fun (R : AggregateRules) => R.store_ushort_range),
  (fun (R : AggregateRules) => R.store_ushort_undef_store_ushort),
  (fun (R : AggregateRules) => R.string_length),
  (fun (R : AggregateRules) => R.struct_padding),
  (fun (R : AggregateRules) => R.truep_andp_left_equiv),
  (fun (R : AggregateRules) => R.truep_andp_right_equiv),
  (fun (R : AggregateRules) => R.typed_poly_store),
  (fun (R : AggregateRules) => R.typed_poly_store_poly_undef_store),
  (fun (R : AggregateRules) => R.undef_store_char),
  (fun (R : AggregateRules) => R.undef_store_char_align),
  (fun (R : AggregateRules) => R.undef_store_double),
  (fun (R : AggregateRules) => R.undef_store_double_align4),
  (fun (R : AggregateRules) => R.undef_store_finite_double),
  (fun (R : AggregateRules) => R.undef_store_finite_float),
  (fun (R : AggregateRules) => R.undef_store_finite_long_double),
  (fun (R : AggregateRules) => R.undef_store_float),
  (fun (R : AggregateRules) => R.undef_store_float_align4),
  (fun (R : AggregateRules) => R.undef_store_int),
  (fun (R : AggregateRules) => R.undef_store_int128),
  (fun (R : AggregateRules) => R.undef_store_int128_align),
  (fun (R : AggregateRules) => R.undef_store_int64),
  (fun (R : AggregateRules) => R.undef_store_int64_align4),
  (fun (R : AggregateRules) => R.undef_store_int_align4),
  (fun (R : AggregateRules) => R.undef_store_int_undef_store_char),
  (fun (R : AggregateRules) => R.undef_store_long_double),
  (fun (R : AggregateRules) => R.undef_store_long_double_align),
  (fun (R : AggregateRules) => R.undef_store_ptr),
  (fun (R : AggregateRules) => R.undef_store_ptr_align4),
  (fun (R : AggregateRules) => R.undef_store_short),
  (fun (R : AggregateRules) => R.undef_store_short_align),
  (fun (R : AggregateRules) => R.undef_store_uchar),
  (fun (R : AggregateRules) => R.undef_store_uchar_align),
  (fun (R : AggregateRules) => R.undef_store_uint),
  (fun (R : AggregateRules) => R.undef_store_uint128),
  (fun (R : AggregateRules) => R.undef_store_uint128_align),
  (fun (R : AggregateRules) => R.undef_store_uint64),
  (fun (R : AggregateRules) => R.undef_store_uint64_align4),
  (fun (R : AggregateRules) => R.undef_store_uint_align4),
  (fun (R : AggregateRules) => R.undef_store_uint_undef_store_char),
  (fun (R : AggregateRules) => R.undef_store_ushort),
  (fun (R : AggregateRules) => R.undef_store_ushort_align),
  (fun (R : AggregateRules) => R.union_padding),
  (fun (R : AggregateRules) => R.valid_char),
  (fun (R : AggregateRules) => R.valid_store_char),
  (fun (R : AggregateRules) => R.valid_store_double),
  (fun (R : AggregateRules) => R.valid_store_finite_double),
  (fun (R : AggregateRules) => R.valid_store_finite_float),
  (fun (R : AggregateRules) => R.valid_store_finite_long_double),
  (fun (R : AggregateRules) => R.valid_store_float),
  (fun (R : AggregateRules) => R.valid_store_int),
  (fun (R : AggregateRules) => R.valid_store_int128),
  (fun (R : AggregateRules) => R.valid_store_int64),
  (fun (R : AggregateRules) => R.valid_store_long_double),
  (fun (R : AggregateRules) => R.valid_store_ptr),
  (fun (R : AggregateRules) => R.valid_store_short),
  (fun (R : AggregateRules) => R.valid_store_uchar),
  (fun (R : AggregateRules) => R.valid_store_uint),
  (fun (R : AggregateRules) => R.valid_store_uint128),
  (fun (R : AggregateRules) => R.valid_store_uint64),
  (fun (R : AggregateRules) => R.valid_store_ushort),
  (fun (R : AggregateRules) => R.valid_string),
  (fun (R : AggregateRules) => R.valid_stringLit),
  (fun (R : AggregateRules) => R.valid_undef_store_char),
  (fun (R : AggregateRules) => R.valid_undef_store_int),
  (fun (R : AggregateRules) => R.valid_undef_store_int128),
  (fun (R : AggregateRules) => R.valid_undef_store_int64),
  (fun (R : AggregateRules) => R.valid_undef_store_ptr),
  (fun (R : AggregateRules) => R.valid_undef_store_short),
  (fun (R : AggregateRules) => R.valid_undef_store_uchar),
  (fun (R : AggregateRules) => R.valid_undef_store_uint),
  (fun (R : AggregateRules) => R.valid_undef_store_uint128),
  (fun (R : AggregateRules) => R.valid_undef_store_uint64),
  (fun (R : AggregateRules) => R.valid_undef_store_ushort),
  (fun (R : AggregateRules) => R.vector_cons),
  (fun (R : AggregateRules) => R.vector_cons_eta),
  (fun (R : AggregateRules) => R.vector_head),
  (fun (R : AggregateRules) => R.vector_head_cons),
  (fun (R : AggregateRules) => R.vector_tail),
  (fun (R : AggregateRules) => R.vector_tail_cons),
  (fun (R : AggregateRules) => R.wand_equiv)
] => 987229656434153248

#check CRules32
#check CRules64
#check naive_C_Rules32
#check naive_C_Rules64
#check Snaive_C_Rules32
#check Snaive_C_Rules64
#check CRules
#check naive_C_Rules
#check Snaive_C_Rules

#check CRules32.ptr_size_eq_4
#check CRules32.ptr_size_Z_eq_4
#check CRules32.addr_max_unsigned_eq_int
#check CRules32.undef_store_ptr_align4_32
#check CRules32.store_ptr_align4_32
#check CRules32.store_ptr_store_uint_32
#check CRules64.ptr_size_eq_8
#check CRules64.ptr_size_Z_eq_8
#check CRules64.addr_max_unsigned_eq_int64
#check CRules64.undef_store_ptr_undef_store_uint64_64
#check CRules64.undef_store_ptr_align4_64
#check CRules64.store_ptr_align4_64
#check CRules64.store_ptr_store_uint64_64
#check naive_C_Rules32.ptr_size_eq_4
#check naive_C_Rules32.ptr_size_Z_eq_4
#check naive_C_Rules32.addr_max_unsigned_eq_int
#check naive_C_Rules32.undef_store_ptr_align4_32
#check naive_C_Rules32.store_ptr_align4_32
#check naive_C_Rules32.store_ptr_store_uint_32
#check naive_C_Rules64.ptr_size_eq_8
#check naive_C_Rules64.ptr_size_Z_eq_8
#check naive_C_Rules64.addr_max_unsigned_eq_int64
#check naive_C_Rules64.undef_store_ptr_undef_store_uint64_64
#check naive_C_Rules64.undef_store_ptr_align4_64
#check naive_C_Rules64.store_ptr_align4_64
#check naive_C_Rules64.store_ptr_store_uint64_64
#check Snaive_C_Rules32.ptr_size_eq_4
#check Snaive_C_Rules32.ptr_size_Z_eq_4
#check Snaive_C_Rules32.addr_max_unsigned_eq_int
#check Snaive_C_Rules32.undef_store_ptr_align4_32
#check Snaive_C_Rules32.store_ptr_align4_32
#check Snaive_C_Rules32.store_ptr_store_uint_32
#check Snaive_C_Rules64.ptr_size_eq_8
#check Snaive_C_Rules64.ptr_size_Z_eq_8
#check Snaive_C_Rules64.addr_max_unsigned_eq_int64
#check Snaive_C_Rules64.undef_store_ptr_undef_store_uint64_64
#check Snaive_C_Rules64.undef_store_ptr_align4_64
#check Snaive_C_Rules64.store_ptr_align4_64
#check Snaive_C_Rules64.store_ptr_store_uint64_64

#check_aggregate_rules_surface [
  CRules32.ptr_size_eq_4, CRules32.ptr_size_Z_eq_4,
  CRules32.addr_max_unsigned_eq_int, CRules32.undef_store_ptr_align4_32,
  CRules32.store_ptr_align4_32, CRules32.store_ptr_store_uint_32,
  CRules64.ptr_size_eq_8, CRules64.ptr_size_Z_eq_8,
  CRules64.addr_max_unsigned_eq_int64,
  CRules64.undef_store_ptr_undef_store_uint64_64,
  CRules64.undef_store_ptr_align4_64, CRules64.store_ptr_align4_64,
  CRules64.store_ptr_store_uint64_64,
  naive_C_Rules32.ptr_size_eq_4, naive_C_Rules32.ptr_size_Z_eq_4,
  naive_C_Rules32.addr_max_unsigned_eq_int,
  naive_C_Rules32.undef_store_ptr_align4_32,
  naive_C_Rules32.store_ptr_align4_32,
  naive_C_Rules32.store_ptr_store_uint_32,
  naive_C_Rules64.ptr_size_eq_8, naive_C_Rules64.ptr_size_Z_eq_8,
  naive_C_Rules64.addr_max_unsigned_eq_int64,
  naive_C_Rules64.undef_store_ptr_undef_store_uint64_64,
  naive_C_Rules64.undef_store_ptr_align4_64,
  naive_C_Rules64.store_ptr_align4_64,
  naive_C_Rules64.store_ptr_store_uint64_64,
  Snaive_C_Rules32.ptr_size_eq_4, Snaive_C_Rules32.ptr_size_Z_eq_4,
  Snaive_C_Rules32.addr_max_unsigned_eq_int,
  Snaive_C_Rules32.undef_store_ptr_align4_32,
  Snaive_C_Rules32.store_ptr_align4_32,
  Snaive_C_Rules32.store_ptr_store_uint_32,
  Snaive_C_Rules64.ptr_size_eq_8, Snaive_C_Rules64.ptr_size_Z_eq_8,
  Snaive_C_Rules64.addr_max_unsigned_eq_int64,
  Snaive_C_Rules64.undef_store_ptr_undef_store_uint64_64,
  Snaive_C_Rules64.undef_store_ptr_align4_64,
  Snaive_C_Rules64.store_ptr_align4_64,
  Snaive_C_Rules64.store_ptr_store_uint64_64
] => 9376167627434260063

example : CRules32.Arch = Arch32 := rfl
example : CRules64.Arch = Arch64 := rfl
example : naive_C_Rules32.Arch = Arch32 := rfl
example : naive_C_Rules64.Arch = Arch64 := rfl
example : Snaive_C_Rules32.Arch = Arch32 := rfl
example : Snaive_C_Rules64.Arch = Arch64 := rfl

example : CRules32.Endian = BigEndian := rfl
example : CRules64.Endian = BigEndian := rfl
example : naive_C_Rules32.Endian = BigEndian := rfl
example : naive_C_Rules64.Endian = BigEndian := rfl
example : Snaive_C_Rules32.Endian = LittleEndian := rfl
example : Snaive_C_Rules64.Endian = LittleEndian := rfl

example : CRules = CRules32 := rfl
example : naive_C_Rules = naive_C_Rules32 := rfl
example : Snaive_C_Rules = Snaive_C_Rules32 := rfl
example : CRules.Arch = Arch32 := rfl
example : naive_C_Rules.Arch = Arch32 := rfl
example : Snaive_C_Rules.Arch = Arch32 := rfl

example (p v : Int) :
    CRules64.store_ptr p v =
      DerivedPredSig.store_ptr Arch64 BigEndian CRules64 p v := rfl
example (p v : Int) :
    Snaive_C_Rules32.store_int p v =
      DerivedPredSig.store_int Arch32 LittleEndian Snaive_C_Rules32 p v := rfl
example (p v : Int) :
    Snaive_C_Rules64.store_int64 p v =
      DerivedPredSig.store_int64 Arch64 LittleEndian Snaive_C_Rules64 p v := rfl

example : CRules64.PtrArray.elementStore.sizeA = 8 := rfl
example : Snaive_C_Rules32.PtrArray.elementStore.sizeA = 4 := rfl
example : Snaive_C_Rules64.PtrArray3.elementStore.sizeA = 8 := rfl

example (p : Int) (s : List Int) :
    Snaive_C_Rules64.store_string p s =
      StringLib.StringLibSig.store_string Arch64 LittleEndian
        Snaive_C_Rules64 Snaive_C_Rules64.derivedPredSig
        Snaive_C_Rules64.storeLibSig p s := rfl

example : CRules32.stringLibSig.GlobalStrings = CRules32.GlobalStrings := rfl
example : CRules64.stringLibSig.GlobalStrings = CRules64.GlobalStrings := rfl
example : naive_C_Rules64.stringLibSig.GlobalStrings =
    naive_C_Rules64.GlobalStrings := rfl
example : Snaive_C_Rules32.stringLibSig.GlobalStrings_missing =
    Snaive_C_Rules32.GlobalStrings_missing := rfl

example :
    CRules64.Z_to_n_bytes 0x01020304 4 = #v[1, 2, 3, 4] := by decide
example :
    Snaive_C_Rules64.Z_to_n_bytes 0x01020304 4 = #v[4, 3, 2, 1] := by decide

#audit_p0_8_string_axioms CRules32 [
  CRules32.GlobalStrings, CRules32.GlobalStrings_missing,
  CRules32.GlobalStrings_split, CRules32.GlobalStrings_merge,
  CRules32.GlobalStrings_missing_split, CRules32.GlobalStrings_missing_merge,
  CRules32.GlobalStrings_split_existing
]
#audit_p0_8_string_axioms CRules64 [
  CRules64.GlobalStrings, CRules64.GlobalStrings_missing,
  CRules64.GlobalStrings_split, CRules64.GlobalStrings_merge,
  CRules64.GlobalStrings_missing_split, CRules64.GlobalStrings_missing_merge,
  CRules64.GlobalStrings_split_existing
]
#audit_p0_8_string_axioms naive_C_Rules32 [
  naive_C_Rules32.GlobalStrings, naive_C_Rules32.GlobalStrings_missing,
  naive_C_Rules32.GlobalStrings_split, naive_C_Rules32.GlobalStrings_merge,
  naive_C_Rules32.GlobalStrings_missing_split,
  naive_C_Rules32.GlobalStrings_missing_merge,
  naive_C_Rules32.GlobalStrings_split_existing
]
#audit_p0_8_string_axioms naive_C_Rules64 [
  naive_C_Rules64.GlobalStrings, naive_C_Rules64.GlobalStrings_missing,
  naive_C_Rules64.GlobalStrings_split, naive_C_Rules64.GlobalStrings_merge,
  naive_C_Rules64.GlobalStrings_missing_split,
  naive_C_Rules64.GlobalStrings_missing_merge,
  naive_C_Rules64.GlobalStrings_split_existing
]
#audit_p0_8_string_axioms Snaive_C_Rules32 [
  Snaive_C_Rules32.GlobalStrings, Snaive_C_Rules32.GlobalStrings_missing,
  Snaive_C_Rules32.GlobalStrings_split, Snaive_C_Rules32.GlobalStrings_merge,
  Snaive_C_Rules32.GlobalStrings_missing_split,
  Snaive_C_Rules32.GlobalStrings_missing_merge,
  Snaive_C_Rules32.GlobalStrings_split_existing
]
#audit_p0_8_string_axioms Snaive_C_Rules64 [
  Snaive_C_Rules64.GlobalStrings, Snaive_C_Rules64.GlobalStrings_missing,
  Snaive_C_Rules64.GlobalStrings_split, Snaive_C_Rules64.GlobalStrings_merge,
  Snaive_C_Rules64.GlobalStrings_missing_split,
  Snaive_C_Rules64.GlobalStrings_missing_merge,
  Snaive_C_Rules64.GlobalStrings_split_existing
]

#audit_p0_8_foundation_axioms [
  CRules32.ptr_size_eq_4, CRules32.ptr_size_Z_eq_4,
  CRules32.addr_max_unsigned_eq_int, CRules32.undef_store_ptr_align4_32,
  CRules32.store_ptr_align4_32, CRules32.store_ptr_store_uint_32,
  CRules64.ptr_size_eq_8, CRules64.ptr_size_Z_eq_8,
  CRules64.addr_max_unsigned_eq_int64,
  CRules64.undef_store_ptr_undef_store_uint64_64,
  CRules64.undef_store_ptr_align4_64, CRules64.store_ptr_align4_64,
  CRules64.store_ptr_store_uint64_64,
  naive_C_Rules32.ptr_size_eq_4, naive_C_Rules32.ptr_size_Z_eq_4,
  naive_C_Rules32.addr_max_unsigned_eq_int,
  naive_C_Rules32.undef_store_ptr_align4_32,
  naive_C_Rules32.store_ptr_align4_32,
  naive_C_Rules32.store_ptr_store_uint_32,
  naive_C_Rules64.ptr_size_eq_8, naive_C_Rules64.ptr_size_Z_eq_8,
  naive_C_Rules64.addr_max_unsigned_eq_int64,
  naive_C_Rules64.undef_store_ptr_undef_store_uint64_64,
  naive_C_Rules64.undef_store_ptr_align4_64,
  naive_C_Rules64.store_ptr_align4_64,
  naive_C_Rules64.store_ptr_store_uint64_64,
  Snaive_C_Rules32.ptr_size_eq_4, Snaive_C_Rules32.ptr_size_Z_eq_4,
  Snaive_C_Rules32.addr_max_unsigned_eq_int,
  Snaive_C_Rules32.undef_store_ptr_align4_32,
  Snaive_C_Rules32.store_ptr_align4_32,
  Snaive_C_Rules32.store_ptr_store_uint_32,
  Snaive_C_Rules64.ptr_size_eq_8, Snaive_C_Rules64.ptr_size_Z_eq_8,
  Snaive_C_Rules64.addr_max_unsigned_eq_int64,
  Snaive_C_Rules64.undef_store_ptr_undef_store_uint64_64,
  Snaive_C_Rules64.undef_store_ptr_align4_64,
  Snaive_C_Rules64.store_ptr_align4_64,
  Snaive_C_Rules64.store_ptr_store_uint64_64
]

def crossNamespaceStringProbe := CRules64.GlobalStrings

/--
error: P0-8 declaration 'SeparationLogicAggregateTests.crossNamespaceStringProbe' depends on disallowed axiom 'SimpleC.SL.SeparationLogic.CRules64.GlobalStrings'
-/
#guard_msgs in
#audit_p0_8_string_axioms CRules32 [crossNamespaceStringProbe]

#print axioms CRules32.store_ptr_store_uint_32
#print axioms CRules64.store_ptr_store_uint64_64
#print axioms Snaive_C_Rules64.store_ptr_align4_64
#print axioms CRules64.GlobalStrings_split
#print axioms Snaive_C_Rules64.GlobalStrings_split

end SeparationLogicAggregateTests
