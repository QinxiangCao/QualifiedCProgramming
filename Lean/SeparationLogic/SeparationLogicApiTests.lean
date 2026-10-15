import SimpleC.SL.SeparationLogic
import Lean.Util.CollectAxioms
import Lean.Util.CollectMVars

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
  "#check_separation_logic_surface " "[" term,* "]" " => " num : command

elab_rules : command
  | `(#check_separation_logic_surface [$terms:term,*] => $expected:num) => do
      let terms := terms.getElems
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number aggregate surface hash"
      let mut actual := hash terms.size
      for term in terms do
        let (value, valueType) <-
          withRef term <| withoutModifyingEnv <| runTermElabM fun _ =>
            Term.withDeclName `_separation_logic_surface_check do
              let value <- Term.elabTerm term none
              Term.synthesizeSyntheticMVarsNoPostponing
              let value <- Lean.instantiateMVars value
              Lean.Meta.check value
              let valueType <- Lean.instantiateMVars (← Lean.Meta.inferType value)
              let mvarIds :=
                (valueType.collectMVars (value.collectMVars {})).result
              for mvarId in mvarIds do
                let mvarType <- Lean.instantiateMVars (← mvarId.getType)
                if mvarType.isConstOf ``SimpleC.SL.CArch.CArchSig ||
                    mvarType.isConstOf ``SimpleC.SL.CArch.CEndianSig then
                  throwErrorAt term
                    "aggregate facade left an architecture/endian parameter unresolved"
              pure (value, valueType)
        actual := mixHash actual (mixHash (hash value) (hash valueType))
      unless actual = expected.toUInt64 do
        throwError "SeparationLogic aggregate surface changed: expected {expected}, got {actual}"
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
        ``SimpleC.SL.CNotation.sizeof_struct_type,
        ``SimpleC.SL.CNotation.sizeof_union_type,
        ``SimpleC.SL.CNotation.sizeof_enum_type,
        ``SimpleC.SL.CNotation.sizeof_alias_type,
        ``SimpleC.SL.CNotation.eval_addr_expr,
        ``SimpleC.SL.CNotation.rvalue_expr_equiv,
        ``SimpleC.SL.CNotation.CNotationSig.eval_addr,
        ``SimpleC.SL.CNotation.CNotationSig.addr_of_array_subst,
        ``SimpleC.SL.CNotation.CNotationSig.addr_of_array_subst',
        ``SimpleC.SL.CNotation.CNotationSig.const_array_pi,
        ``SimpleC.SL.CNotation.CNotationSig.const_array_pi',
        ``SimpleC.SL.CNotation.CNotationSig.addr_of_arrow_field,
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
        ``SimpleC.SL.SeparationLogic.CRules32.GlobalStrings,
        ``SimpleC.SL.SeparationLogic.CRules32.GlobalStrings_missing,
        ``SimpleC.SL.SeparationLogic.CRules32.GlobalStrings_split,
        ``SimpleC.SL.SeparationLogic.CRules32.GlobalStrings_merge,
        ``SimpleC.SL.SeparationLogic.CRules32.GlobalStrings_missing_split,
        ``SimpleC.SL.SeparationLogic.CRules32.GlobalStrings_missing_merge,
        ``SimpleC.SL.SeparationLogic.CRules32.GlobalStrings_split_existing,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules32.GlobalStrings,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules32.GlobalStrings_missing,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules32.GlobalStrings_split,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules32.GlobalStrings_merge,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules32.GlobalStrings_missing_split,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules32.GlobalStrings_missing_merge,
        ``SimpleC.SL.SeparationLogic.naive_C_Rules32.GlobalStrings_split_existing,
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
#check CRules.store_int128
#check CRules.undef_store_uint128
#check CRules.store_float
#check CRules.store_finite_long_double
#check CRules.front_end_type_value
#check CRules.typed_poly_store
#check CRules.store_array
#check CRules.coq_prop_andp_left
#check CRules.store_n_bytes_Z
#check CRules.store_int_range
#check CRules.store_align4_valid
#check CRules.store_uint_store_char
#check CRules.store_float_undef_store_float
#check CRules.typed_poly_store_poly_undef_store
#check CRules.valid_store_double
#check CRules.store_finite_long_double_align
#check CRules.vector_cons
#check CRules.Z_to_n_bytes
#check CRules.merge_int64_equiv_merge_n_bytes
#check CRules.store_map
#check CRules.store_map_split
#check CRules.StoreCharAsElement
#check CRules.StoreInt128AsElement
#check CRules.StoreFloatAsElement
#check CRules.StoreFiniteLongDoubleAsElement
#check CRules.CharArray
#check CRules.IntArray
#check CRules.Int128Array
#check CRules.FloatArray
#check CRules.FiniteLongDoubleArray
#check CRules.CharArray2
#check CRules.PtrArray2
#check CRules.Int128Array2
#check CRules.FloatArray2
#check CRules.FiniteLongDoubleArray2
#check CRules.CharArray3
#check CRules.Int128Array3
#check CRules.FloatArray3
#check CRules.FiniteLongDoubleArray3
#check CRules.PtrArray3
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
#check naive_C_Rules.store_int128
#check naive_C_Rules.undef_store_uint128
#check naive_C_Rules.store_float
#check naive_C_Rules.front_end_type_value
#check naive_C_Rules.typed_poly_store
#check naive_C_Rules.Z_to_n_bytes
#check naive_C_Rules.IntArray
#check naive_C_Rules.IntArray2
#check naive_C_Rules.IntArray3
#check naive_C_Rules.FloatArray3
#check naive_C_Rules.PtrArray3
#check naive_C_Rules.IntPtrArray2
#check naive_C_Rules.store_map
#check naive_C_Rules.store_string
#check naive_C_Rules.GlobalStrings
#check naive_C_Rules.GlobalStrings_split_existing
#check naive_C_Rules.stringLibSig

#check field_address
#check should_be_equal
#check fp32
#check fp64_add
#check fp128_isFinite
#check bits_of_fp32
#check fexp32
#check fexp64
#check fexp128
#check rounded32
#check rounded64
#check rounded128
#check in_float32_range
#check in_float64_range
#check in_float128_range
#check rounded32_generic
#check rounded64_generic
#check rounded128_generic
#check fp32_of_real
#check fp64_of_real
#check fp128_of_real
#check fp32_to_R
#check fp64_to_R
#check fp128_to_R
#check fp32_to_R_total
#check fp64_to_R_total
#check fp128_to_R_total
#check LDBL_MIN

-- This contract is deliberately independent of the fixed `CRules` facade
-- surface below.  It freezes the parameterized CommonAssertion API, including
-- the order and implicitness of its architecture, endian, and rules arguments.
#check_separation_logic_contract [
  BasePredSig,
  BasePredSig.mstore,
  BasePredSig.mstore_noninit,
  BasePredSig.mstore_mstore_noninit,
  BasePredSig.mstore_eqm,
  BasePredSig.dup_mstore_noninit,
  SeparationLogicSig,
  SeparationLogicSig.toContext,
  SeparationLogicSig.mstore,
  SeparationLogicSig.mstore_noninit,
  SeparationLogicSig.mstore_mstore_noninit,
  SeparationLogicSig.mstore_eqm,
  SeparationLogicSig.dup_mstore_noninit,
  SeparationLogicSig.toBasePredSig,
  SeparationLogicSig.model,
  SeparationLogicSig.expr,
  SeparationLogicSig.join,
  SeparationLogicSig.is_unit,
  SeparationLogicSig.sepcon,
  SeparationLogicSig.wand,
  SeparationLogicSig.orp,
  SeparationLogicSig.andp,
  SeparationLogicSig.impp,
  SeparationLogicSig.exp,
  SeparationLogicSig.allp,
  SeparationLogicSig.emp,
  SeparationLogicSig.coq_prop,
  SeparationLogicSig.truep,
  SeparationLogicSig.derivable1,
  SeparationLogicSig.logic_equiv,
  DerivedPredSig,
  DerivedPredSig.canonical,
  DerivedPredSig.sizeof_front_end_type,
  DerivedPredSig.sizeof_int,
  DerivedPredSig.sizeof_char,
  DerivedPredSig.sizeof_int64,
  DerivedPredSig.sizeof_short,
  DerivedPredSig.sizeof_uint,
  DerivedPredSig.sizeof_uchar,
  DerivedPredSig.sizeof_uint64,
  DerivedPredSig.sizeof_int128,
  DerivedPredSig.sizeof_uint128,
  DerivedPredSig.sizeof_ushort,
  DerivedPredSig.sizeof_float,
  DerivedPredSig.sizeof_double,
  DerivedPredSig.sizeof_long_double,
  DerivedPredSig.sizeof_ptr,
  DerivedPredSig.eval_addr,
  DerivedPredSig.addr_of_array_subst,
  DerivedPredSig.addr_of_array_subst',
  DerivedPredSig.const_array_pi,
  DerivedPredSig.const_array_pi',
  DerivedPredSig.addr_of_arrow_field,
  DerivedPredSig.addr_max_unsigned,
  DerivedPredSig.ptr_size,
  DerivedPredSig.ptr_align,
  DerivedPredSig.ptr_size_Z,
  DerivedPredSig.ptr_width_Z,
  DerivedPredSig.aligned,
  DerivedPredSig.bytes_eqm,
  DerivedPredSig.n_bytes_to_Z,
  DerivedPredSig.Z_to_n_bytes,
  DerivedPredSig.merge_n_bytes,
  DerivedPredSig.merge_short,
  DerivedPredSig.merge_int,
  DerivedPredSig.merge_int64,
  DerivedPredSig.vec1,
  DerivedPredSig.vec2,
  DerivedPredSig.vec4,
  DerivedPredSig.vec8,
  DerivedPredSig.ptr_size_32_or_64,
  DerivedPredSig.ptr_size_pos,
  DerivedPredSig.ptr_align_pos,
  DerivedPredSig.ptr_aligned_aligned_4,
  DerivedPredSig.addr_max_unsigned_ge_7,
  DerivedPredSig.ptr_size_fits_addr,
  DerivedPredSig.int_max_fits_addr,
  DerivedPredSig.eqm_bytes_to_Z_eq,
  DerivedPredSig.Z_to_n_bytes_to_Z,
  DerivedPredSig.merge_n_bytes_self,
  DerivedPredSig.merge_byte_equiv_merge_n_bytes,
  DerivedPredSig.merge_short_equiv_merge_n_bytes,
  DerivedPredSig.merge_int_equiv_merge_n_bytes,
  DerivedPredSig.merge_int64_equiv_merge_n_bytes,
  DerivedPredSig.merge_short_eqm,
  DerivedPredSig.merge_int_eqm,
  DerivedPredSig.merge_int64_eqm,
  DerivedPredSig.merge_short_value_eqm,
  DerivedPredSig.merge_int_value_eqm,
  DerivedPredSig.merge_int64_value_eqm,
  DerivedPredSig.valid_addr_range,
  DerivedPredSig.valid_object,
  DerivedPredSig.isvalidptr_char,
  DerivedPredSig.isvalidptr_short,
  DerivedPredSig.isvalidptr_int,
  DerivedPredSig.isvalidptr_int64,
  DerivedPredSig.isvalidptr_int128,
  DerivedPredSig.isvalidptr_float,
  DerivedPredSig.isvalidptr_double,
  DerivedPredSig.isvalidptr_long_double,
  DerivedPredSig.isvalidptr,
  DerivedPredSig.valid_ptr_value,
  DerivedPredSig.store_byte,
  DerivedPredSig.store_2byte,
  DerivedPredSig.store_4byte,
  DerivedPredSig.store_8byte,
  DerivedPredSig.store_bytes,
  DerivedPredSig.store_16byte,
  DerivedPredSig.store_byte_noninit,
  DerivedPredSig.store_2byte_noninit,
  DerivedPredSig.store_4byte_noninit,
  DerivedPredSig.store_8byte_noninit,
  DerivedPredSig.store_bytes_noninit,
  DerivedPredSig.store_16byte_noninit,
  DerivedPredSig.store_char,
  DerivedPredSig.undef_store_char,
  DerivedPredSig.store_uchar,
  DerivedPredSig.undef_store_uchar,
  DerivedPredSig.store_short,
  DerivedPredSig.undef_store_short,
  DerivedPredSig.store_ushort,
  DerivedPredSig.undef_store_ushort,
  DerivedPredSig.store_int,
  DerivedPredSig.undef_store_int,
  DerivedPredSig.store_uint,
  DerivedPredSig.undef_store_uint,
  DerivedPredSig.store_int64,
  DerivedPredSig.undef_store_int64,
  DerivedPredSig.store_uint64,
  DerivedPredSig.undef_store_uint64,
  DerivedPredSig.store_int128,
  DerivedPredSig.undef_store_int128,
  DerivedPredSig.store_uint128,
  DerivedPredSig.undef_store_uint128,
  DerivedPredSig.store_float,
  DerivedPredSig.store_double,
  DerivedPredSig.store_long_double,
  DerivedPredSig.store_finite_float,
  DerivedPredSig.store_finite_double,
  DerivedPredSig.store_finite_long_double,
  DerivedPredSig.undef_store_float,
  DerivedPredSig.undef_store_double,
  DerivedPredSig.undef_store_long_double,
  DerivedPredSig.undef_store_finite_float,
  DerivedPredSig.undef_store_finite_double,
  DerivedPredSig.undef_store_finite_long_double,
  DerivedPredSig.store_ptr,
  DerivedPredSig.undef_store_ptr,
  DerivedPredSig.Invalid_store,
  DerivedPredSig.Invalid_undef_store,
  DerivedPredSig.dup_data_at_error,
  DerivedPredSig.dup_data_at_error_prop,
  DerivedPredSig.store_array_rec,
  DerivedPredSig.store_array_missing_i_rec,
  DerivedPredSig.store_array,
  DerivedPredSig.store_undef_array_rec,
  DerivedPredSig.store_undef_array_missing_i_rec,
  DerivedPredSig.store_undef_array,
  DerivedPredSig.store_align4_list,
  DerivedPredSig.store_align4_n,
  DerivedPredSig.store_align_list,
  DerivedPredSig.store_align_n,
  DerivedPredSig.front_end_type_value,
  DerivedPredSig.typed_poly_store,
  DerivedPredSig.poly_store,
  DerivedPredSig.poly_undef_store,
  DerivedPredSig.struct_padding,
  DerivedPredSig.union_padding,
  DerivedPredSig.coq_prop_andp_left,
  DerivedPredSig.coq_prop_andp_right,
  DerivedPredSig.coq_prop_imply,
  DerivedPredSig.coq_prop_False_left,
  DerivedPredSig.orp_sepcon_left,
  DerivedPredSig.orp_sepcon_right,
  DerivedPredSig.orp_sepcon_left',
  DerivedPredSig.orp_sepcon_right',
  DerivedPredSig.orp_sepcon_left_equiv,
  DerivedPredSig.orp_sepcon_right_equiv,
  DerivedPredSig.exp_right_exists,
  DerivedPredSig.derivable1_imp,
  DerivedPredSig.derivable1_andp_mono,
  DerivedPredSig.ex_logic_equiv_andp,
  DerivedPredSig.wand_equiv,
  DerivedPredSig.ex_logic_equiv_sepcon,
  DerivedPredSig.prop_add_left,
  DerivedPredSig.truep_andp_left_equiv,
  DerivedPredSig.truep_andp_right_equiv,
  DerivedPredSig.sepcon_emp_equiv,
  DerivedPredSig.sepcon_cancel_res_emp,
  DerivedPredSig.sepcon_cancel_end,
  DerivedPredSig.sepcon_prop_equiv,
  DerivedPredSig.exp_exp_right,
  DerivedPredSig.exp_allp_left,
  DerivedPredSig.exp_allp_swap,
  DerivedPredSig.allp_allp_swap,
  DerivedPredSig.derivable1_wand_sepcon_adjoint,
  DerivedPredSig.all_list,
  DerivedPredSig.sepcon_emp_logic_equiv',
  DerivedPredSig.elim_wand_emp_emp,
  DerivedPredSig.dump_spatial_left,
  DerivedPredSig.split_pure_and_spatial_goals,
  DerivedPredSig.split_spatial_and_pure_goals,
  DerivedPredSig._derivable1_andp_intros,
  DerivedPredSig.add_pure_split,
  DerivedPredSig.sepcon_cancel_lhs_emp
] => 11114504180954724331

#check_separation_logic_surface [
  CRules,
  naive_CSL,
  naive_C_Rules,
  CRules.store_byte,
  CRules.store_2byte,
  CRules.store_4byte,
  CRules.store_8byte,
  CRules.store_bytes,
  CRules.store_16byte,
  CRules.store_byte_noninit,
  CRules.store_2byte_noninit,
  CRules.store_4byte_noninit,
  CRules.store_8byte_noninit,
  CRules.store_bytes_noninit,
  CRules.store_16byte_noninit,
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
  CRules.store_int128,
  CRules.undef_store_int128,
  CRules.store_uint128,
  CRules.undef_store_uint128,
  CRules.store_float,
  CRules.store_double,
  CRules.store_long_double,
  CRules.store_finite_float,
  CRules.store_finite_double,
  CRules.store_finite_long_double,
  CRules.undef_store_float,
  CRules.undef_store_double,
  CRules.undef_store_long_double,
  CRules.undef_store_finite_float,
  CRules.undef_store_finite_double,
  CRules.undef_store_finite_long_double,
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
  CRules.front_end_type_value,
  CRules.typed_poly_store,
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
  CRules.store_bytes_store_bytes_noninit,
  CRules.store_16byte_store_16byte_noinit,
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
  CRules.store_int128_range,
  CRules.store_int128_undef_store_int128,
  CRules.store_uint128_range,
  CRules.store_uint128_undef_store_uint128,
  CRules.store_float_undef_store_float,
  CRules.store_double_undef_store_double,
  CRules.store_long_double_undef_store_long_double,
  CRules.store_finite_float_undef_store_finite_float,
  CRules.store_finite_double_undef_store_finite_double,
  CRules.store_finite_long_double_undef_store_finite_long_double,
  CRules.poly_store_poly_undef_store,
  CRules.typed_poly_store_poly_undef_store,
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
  CRules.valid_store_int128,
  CRules.valid_store_uint128,
  CRules.valid_undef_store_int128,
  CRules.valid_undef_store_uint128,
  CRules.valid_store_float,
  CRules.valid_store_double,
  CRules.valid_store_long_double,
  CRules.valid_store_finite_float,
  CRules.valid_store_finite_double,
  CRules.valid_store_finite_long_double,
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
  CRules.aligned_8_aligned_4,
  CRules.store_float_aligned4,
  CRules.store_double_aligned8,
  CRules.store_finite_float_aligned4,
  CRules.store_finite_double_aligned8,
  CRules.store_long_double_aligned8,
  CRules.store_finite_long_double_aligned8,
  CRules.undef_store_float_align4,
  CRules.store_float_align4,
  CRules.undef_store_double_align4,
  CRules.store_double_align4,
  CRules.undef_store_int128_align,
  CRules.store_int128_align,
  CRules.undef_store_uint128_align,
  CRules.store_uint128_align,
  CRules.store_float_align,
  CRules.store_double_align,
  CRules.undef_store_long_double_align,
  CRules.store_long_double_align,
  CRules.store_finite_float_align,
  CRules.store_finite_double_align,
  CRules.store_finite_long_double_align,
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
  CRules.array3LibSig,
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
  CRules.StoreInt128AsElement,
  CRules.StoreUInt128AsElement,
  CRules.StoreFloatAsElement,
  CRules.StoreDoubleAsElement,
  CRules.StoreLongDoubleAsElement,
  CRules.StoreFiniteFloatAsElement,
  CRules.StoreFiniteDoubleAsElement,
  CRules.StoreFiniteLongDoubleAsElement,
  CRules.StorePtrAsElement,
  CRules.CharArray,
  CRules.UCharArray,
  CRules.ShortArray,
  CRules.UShortArray,
  CRules.IntArray,
  CRules.UIntArray,
  CRules.Int64Array,
  CRules.UInt64Array,
  CRules.Int128Array,
  CRules.UInt128Array,
  CRules.FloatArray,
  CRules.DoubleArray,
  CRules.LongDoubleArray,
  CRules.FiniteFloatArray,
  CRules.FiniteDoubleArray,
  CRules.FiniteLongDoubleArray,
  CRules.PtrArray,
  CRules.CharArray2,
  CRules.UCharArray2,
  CRules.ShortArray2,
  CRules.UShortArray2,
  CRules.IntArray2,
  CRules.UIntArray2,
  CRules.Int64Array2,
  CRules.UInt64Array2,
  CRules.Int128Array2,
  CRules.UInt128Array2,
  CRules.FloatArray2,
  CRules.DoubleArray2,
  CRules.LongDoubleArray2,
  CRules.FiniteFloatArray2,
  CRules.FiniteDoubleArray2,
  CRules.FiniteLongDoubleArray2,
  CRules.PtrArray2,
  CRules.CharArray3,
  CRules.UCharArray3,
  CRules.ShortArray3,
  CRules.UShortArray3,
  CRules.IntArray3,
  CRules.UIntArray3,
  CRules.Int64Array3,
  CRules.UInt64Array3,
  CRules.Int128Array3,
  CRules.UInt128Array3,
  CRules.FloatArray3,
  CRules.DoubleArray3,
  CRules.LongDoubleArray3,
  CRules.FiniteFloatArray3,
  CRules.FiniteDoubleArray3,
  CRules.FiniteLongDoubleArray3,
  CRules.PtrArray3,
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
  naive_C_Rules.front_end_type_value,
  naive_C_Rules.Int128Array,
  naive_C_Rules.FloatArray2,
  naive_C_Rules.PtrArray3,
  fp32,
  fp64,
  fp128,
  fp32_nan_payload,
  fp32_nan_payload_valid,
  fp64_nan_payload,
  fp64_nan_payload_valid,
  fp128_nan_payload,
  fp128_nan_payload_valid,
  fp32_nan,
  fp64_nan,
  fp128_nan,
  fp32_unary_nan,
  fp64_unary_nan,
  fp128_unary_nan,
  fp32_binary_nan,
  fp64_binary_nan,
  fp128_binary_nan,
  fp32_add,
  fp32_sub,
  fp32_mul,
  fp32_div,
  fp32_neg,
  fp64_add,
  fp64_sub,
  fp64_mul,
  fp64_div,
  fp64_neg,
  fp128_add,
  fp128_sub,
  fp128_mul,
  fp128_div,
  fp128_neg,
  fp32_isFinite,
  fp64_isFinite,
  fp128_isFinite,
  fp32_isNaN,
  fp64_isNaN,
  fp128_isNaN,
  fp32_isInf,
  fp64_isInf,
  fp128_isInf,
  fp32_compare,
  fp64_compare,
  fp128_compare,
  fp32_eq,
  fp32_ne,
  fp32_lt,
  fp32_le,
  fp32_gt,
  fp32_ge,
  fp64_eq,
  fp64_ne,
  fp64_lt,
  fp64_le,
  fp64_gt,
  fp64_ge,
  fp128_eq,
  fp128_ne,
  fp128_lt,
  fp128_le,
  fp128_gt,
  fp128_ge,
  fp32_of_bits,
  fp64_of_bits,
  fp128_of_bits,
  bits_of_fp32,
  bits_of_fp64,
  bits_of_fp128,
  bits_of_float_value,
  bits_of_double_value,
  bits_of_long_double_value,
  max_unsigned_128,
  bits_of_float_value_range,
  bits_of_double_value_range,
  bits_of_long_double_value_range,
  fexp32,
  fexp64,
  fexp128,
  rounded32,
  rounded64,
  rounded128,
  in_float32_range,
  in_float64_range,
  in_float128_range,
  rounded32_generic,
  rounded64_generic,
  rounded128_generic,
  fp32_of_real,
  fp64_of_real,
  fp128_of_real,
  fp32_of_Z,
  fp64_of_Z,
  fp128_of_Z,
  Z_to_fp32,
  Z_to_fp64,
  Z_to_fp128,
  fp32_to_R,
  fp64_to_R,
  fp128_to_R,
  fp32_to_R_total,
  fp64_to_R_total,
  fp128_to_R_total,
  fp32_zero,
  fp32_neg_zero,
  fp64_zero,
  fp64_neg_zero,
  fp128_zero,
  fp128_neg_zero,
  fp32_pos_infinity,
  fp32_neg_infinity,
  fp64_pos_infinity,
  fp64_neg_infinity,
  fp128_pos_infinity,
  fp128_neg_infinity,
  FLT_MAX,
  FLT_MIN,
  DBL_MAX,
  DBL_MIN,
  LDBL_MAX,
  LDBL_MIN,
  field_address,
  should_be_equal
] => 6354823823336268699

/--
error: aggregate facade left an architecture/endian parameter unresolved
-/
#guard_msgs in
#check_separation_logic_surface [
  SimpleC.SL.StoreAux.StoreLibSig.store_int_range CRules
] => 0

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
] => 7426618560417580207

example : CRules = CRules32 := rfl
example : naive_C_Rules = naive_C_Rules32 := rfl

example (p v : Int) :
    CRules.store_ptr p v =
      SimpleC.SL.CommonAssertion.DerivedPredSig.store_ptr
        CRules.Arch CRules.Endian CRules p v := rfl

example (x v : Int) :
    CRules.store_n_bytes_Z x 8 v =
      SimpleC.SL.StoreAux.StoreLibSig.store_n_bytes_Z
        SimpleC.SL.CArch.Arch32 SimpleC.SL.CArch.BigEndian CRules x 8 v := rfl

example (x v : Int) :
    CRules.derivable1 (CRules.store_ptr x v) (CRules.store_uint x v) :=
  CRules.store_ptr_store_uint_32 x v

example (v : Int) (n : Nat) :
    CRules.Z_to_n_bytes v n =
      SimpleC.SL.StoreAux.StoreLibSig.Z_to_n_bytes
        SimpleC.SL.CArch.BigEndian v n := rfl

example : CRules.IntArray.elementStore =
    SimpleC.SL.ArrayLib.StoreIntAsElement
      SimpleC.SL.CArch.Arch32 SimpleC.SL.CArch.BigEndian
        CRules CRules.derivedPredSig CRules.storeLibSig := rfl

example : CRules.IntArray2.elementStore =
    SimpleC.SL.ArrayLib.StoreIntAsElement
      SimpleC.SL.CArch.Arch32 SimpleC.SL.CArch.BigEndian
        CRules CRules.derivedPredSig CRules.storeLibSig := rfl

example : CRules.IntArray3.elementStore =
    SimpleC.SL.ArrayLib.StoreIntAsElement
      SimpleC.SL.CArch.Arch32 SimpleC.SL.CArch.BigEndian
        CRules CRules.derivedPredSig CRules.storeLibSig := rfl

example : CRules.IntPtrArray2.elementStore =
    SimpleC.SL.ArrayLib.StoreIntAsElement
      SimpleC.SL.CArch.Arch32 SimpleC.SL.CArch.BigEndian
        CRules CRules.derivedPredSig CRules.storeLibSig := rfl

example (p : Int) (s : List Int) :
    CRules.store_string p s =
      SimpleC.SL.StringLib.StringLibSig.store_string
        SimpleC.SL.CArch.Arch32 SimpleC.SL.CArch.BigEndian
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
