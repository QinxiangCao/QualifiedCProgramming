import SimpleC.SL.Assertion
import SimpleC.SL.ConAssertion
import SimpleC.SL.Array2Lib
import SimpleC.SL.Array3Lib
import SimpleC.SL.MapLib
import SimpleC.SL.PtrArray2Lib
import SimpleC.SL.StringLib

/-!
Lean-only compatibility implementation for the repeated `Include` composition in
Coq `SeparationLogic.v`. There is no Coq source file corresponding to this physical
file. Source-facing declarations deliberately remain in
`SimpleC.SL.SeparationLogic`; this module must not be counted as an independently
migrated Coq source unit.
-/

namespace SimpleC.SL.SeparationLogic

open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion
open SimpleC.SL.StoreAux

/-- A first-class counterpart of one concrete Coq `SeparationLogic` module.
It retains the inherited logic signature while recording the architecture and
endianness selected by the module. Abstract StringLib fields remain in each
concrete module namespace so unrelated proofs do not acquire their axioms. -/
structure AggregateRules extends SeparationLogicSig where
  Arch : CArchSig
  Endian : CEndianSig

instance : Coe AggregateRules SeparationLogicSig :=
  ⟨AggregateRules.toSeparationLogicSig⟩

namespace AggregateDerivedPredSigCompat

abbrev store_2byte (self : AggregateRules) := DerivedPredSig.store_2byte self.Endian self
abbrev store_4byte (self : AggregateRules) := DerivedPredSig.store_4byte self.Endian self
abbrev store_8byte (self : AggregateRules) := DerivedPredSig.store_8byte self.Endian self
abbrev store_16byte (self : AggregateRules) := DerivedPredSig.store_16byte self.Endian self
abbrev store_char (self : AggregateRules) := DerivedPredSig.store_char self.Arch self
abbrev undef_store_char (self : AggregateRules) := DerivedPredSig.undef_store_char self.Arch self
abbrev store_uchar (self : AggregateRules) := DerivedPredSig.store_uchar self.Arch self
abbrev undef_store_uchar (self : AggregateRules) := DerivedPredSig.undef_store_uchar self.Arch self
abbrev store_short (self : AggregateRules) := DerivedPredSig.store_short self.Arch self.Endian self
abbrev undef_store_short (self : AggregateRules) := DerivedPredSig.undef_store_short self.Arch self
abbrev store_ushort (self : AggregateRules) := DerivedPredSig.store_ushort self.Arch self.Endian self
abbrev undef_store_ushort (self : AggregateRules) := DerivedPredSig.undef_store_ushort self.Arch self
abbrev store_int (self : AggregateRules) := DerivedPredSig.store_int self.Arch self.Endian self
abbrev undef_store_int (self : AggregateRules) := DerivedPredSig.undef_store_int self.Arch self
abbrev store_uint (self : AggregateRules) := DerivedPredSig.store_uint self.Arch self.Endian self
abbrev undef_store_uint (self : AggregateRules) := DerivedPredSig.undef_store_uint self.Arch self
abbrev store_int64 (self : AggregateRules) := DerivedPredSig.store_int64 self.Arch self.Endian self
abbrev undef_store_int64 (self : AggregateRules) := DerivedPredSig.undef_store_int64 self.Arch self
abbrev store_uint64 (self : AggregateRules) := DerivedPredSig.store_uint64 self.Arch self.Endian self
abbrev undef_store_uint64 (self : AggregateRules) := DerivedPredSig.undef_store_uint64 self.Arch self
abbrev store_int128 (self : AggregateRules) := DerivedPredSig.store_int128 self.Arch self.Endian self
abbrev undef_store_int128 (self : AggregateRules) := DerivedPredSig.undef_store_int128 self.Arch self
abbrev store_uint128 (self : AggregateRules) := DerivedPredSig.store_uint128 self.Arch self.Endian self
abbrev undef_store_uint128 (self : AggregateRules) := DerivedPredSig.undef_store_uint128 self.Arch self
abbrev store_float (self : AggregateRules) := DerivedPredSig.store_float self.Arch self.Endian self
abbrev undef_store_float (self : AggregateRules) := DerivedPredSig.undef_store_float self.Arch self
abbrev store_double (self : AggregateRules) := DerivedPredSig.store_double self.Arch self.Endian self
abbrev undef_store_double (self : AggregateRules) := DerivedPredSig.undef_store_double self.Arch self
abbrev store_long_double (self : AggregateRules) :=
  DerivedPredSig.store_long_double self.Arch self.Endian self
abbrev undef_store_long_double (self : AggregateRules) :=
  DerivedPredSig.undef_store_long_double self.Arch self
abbrev store_finite_float (self : AggregateRules) :=
  DerivedPredSig.store_finite_float self.Arch self.Endian self
abbrev store_finite_double (self : AggregateRules) :=
  DerivedPredSig.store_finite_double self.Arch self.Endian self
abbrev store_finite_long_double (self : AggregateRules) :=
  DerivedPredSig.store_finite_long_double self.Arch self.Endian self
abbrev undef_store_finite_float (self : AggregateRules) :=
  DerivedPredSig.undef_store_finite_float self.Arch self
abbrev undef_store_finite_double (self : AggregateRules) :=
  DerivedPredSig.undef_store_finite_double self.Arch self
abbrev undef_store_finite_long_double (self : AggregateRules) :=
  DerivedPredSig.undef_store_finite_long_double self.Arch self
abbrev store_ptr (self : AggregateRules) := DerivedPredSig.store_ptr self.Arch self.Endian self
abbrev undef_store_ptr (self : AggregateRules) := DerivedPredSig.undef_store_ptr self.Arch self
abbrev store_align4_list (self : AggregateRules) := DerivedPredSig.store_align4_list self.Arch self
abbrev store_align4_n (self : AggregateRules) := DerivedPredSig.store_align4_n self.Arch self
abbrev store_align_list (self : AggregateRules) := DerivedPredSig.store_align_list self.Arch self
abbrev store_align_n (self : AggregateRules) := DerivedPredSig.store_align_n self.Arch self
abbrev typed_poly_store (self : AggregateRules) :=
  DerivedPredSig.typed_poly_store self.Arch self.Endian self
abbrev poly_store (self : AggregateRules) := DerivedPredSig.poly_store self.Arch self.Endian self
abbrev poly_undef_store (self : AggregateRules) := DerivedPredSig.poly_undef_store self.Arch self

end AggregateDerivedPredSigCompat

namespace AggregateRules

universe u

abbrev rules (self : AggregateRules) : SeparationLogicSig :=
  self.toSeparationLogicSig

abbrev front_end_type_value (_self : AggregateRules) :=
  DerivedPredSig.front_end_type_value

open SimpleC.SL.CArch
open SimpleC.SL.StoreAux

-- Coq's `Include CNotationSig self.Arch` exposes these declarations directly.
noncomputable abbrev sizeof_front_end_type (self : AggregateRules) :=
  CNotation.CNotationSig.sizeof_front_end_type self.Arch
abbrev sizeof_int (self : AggregateRules) := CNotation.CNotationSig.sizeof_int self.Arch
abbrev sizeof_char (self : AggregateRules) := CNotation.CNotationSig.sizeof_char self.Arch
abbrev sizeof_int64 (self : AggregateRules) := CNotation.CNotationSig.sizeof_int64 self.Arch
abbrev sizeof_short (self : AggregateRules) := CNotation.CNotationSig.sizeof_short self.Arch
abbrev sizeof_uint (self : AggregateRules) := CNotation.CNotationSig.sizeof_uint self.Arch
abbrev sizeof_uchar (self : AggregateRules) := CNotation.CNotationSig.sizeof_uchar self.Arch
abbrev sizeof_uint64 (self : AggregateRules) := CNotation.CNotationSig.sizeof_uint64 self.Arch
abbrev sizeof_int128 (self : AggregateRules) := CNotation.CNotationSig.sizeof_int128 self.Arch
abbrev sizeof_uint128 (self : AggregateRules) := CNotation.CNotationSig.sizeof_uint128 self.Arch
abbrev sizeof_ushort (self : AggregateRules) := CNotation.CNotationSig.sizeof_ushort self.Arch
abbrev sizeof_float (self : AggregateRules) := CNotation.CNotationSig.sizeof_float self.Arch
abbrev sizeof_double (self : AggregateRules) := CNotation.CNotationSig.sizeof_double self.Arch
abbrev sizeof_long_double (self : AggregateRules) :=
  CNotation.CNotationSig.sizeof_long_double self.Arch
abbrev sizeof_ptr (self : AggregateRules) := CNotation.CNotationSig.sizeof_ptr self.Arch
abbrev eval_addr (self : AggregateRules) := CNotation.CNotationSig.eval_addr self.Arch
abbrev addr_of_array_subst (self : AggregateRules) :=
  CNotation.CNotationSig.addr_of_array_subst self.Arch
abbrev addr_of_array_subst' (self : AggregateRules) :=
  CNotation.CNotationSig.addr_of_array_subst' self.Arch
abbrev const_array_pi (self : AggregateRules) :=
  CNotation.CNotationSig.const_array_pi self.Arch
abbrev const_array_pi' (self : AggregateRules) :=
  CNotation.CNotationSig.const_array_pi' self.Arch
abbrev addr_of_arrow_field (self : AggregateRules) :=
  CNotation.CNotationSig.addr_of_arrow_field self.Arch

-- Direct declarations from `DerivedPredSig` that are not covered by the
-- architecture-sensitive store compatibility aliases below.
abbrev addr_max_unsigned (self : AggregateRules) := DerivedPredSig.addr_max_unsigned self.Arch
abbrev ptr_size (self : AggregateRules) := DerivedPredSig.ptr_size self.Arch
abbrev ptr_align (self : AggregateRules) := DerivedPredSig.ptr_align self.Arch
abbrev ptr_size_Z (self : AggregateRules) := DerivedPredSig.ptr_size_Z self.Arch
abbrev ptr_width_Z (self : AggregateRules) := DerivedPredSig.ptr_width_Z self.Arch
abbrev aligned (self : AggregateRules) := DerivedPredSig.aligned self.Arch
abbrev merge_short (self : AggregateRules) := DerivedPredSig.merge_short self.Endian
abbrev merge_int (self : AggregateRules) := DerivedPredSig.merge_int self.Endian
abbrev merge_int64 (self : AggregateRules) := DerivedPredSig.merge_int64 self.Endian
abbrev vec1 (_self : AggregateRules) := DerivedPredSig.vec1
abbrev vec2 (_self : AggregateRules) := DerivedPredSig.vec2
abbrev vec4 (_self : AggregateRules) := DerivedPredSig.vec4
abbrev vec8 (_self : AggregateRules) := DerivedPredSig.vec8
abbrev ptr_size_32_or_64 (self : AggregateRules) := DerivedPredSig.ptr_size_32_or_64 self.Arch
abbrev ptr_size_pos (self : AggregateRules) := DerivedPredSig.ptr_size_pos self.Arch
abbrev ptr_align_pos (self : AggregateRules) := DerivedPredSig.ptr_align_pos self.Arch
abbrev ptr_aligned_aligned_4 (self : AggregateRules) :=
  DerivedPredSig.ptr_aligned_aligned_4 self.Arch
abbrev addr_max_unsigned_ge_7 (self : AggregateRules) :=
  DerivedPredSig.addr_max_unsigned_ge_7 self.Arch
abbrev ptr_size_fits_addr (self : AggregateRules) :=
  DerivedPredSig.ptr_size_fits_addr self.Arch
abbrev int_max_fits_addr (self : AggregateRules) :=
  DerivedPredSig.int_max_fits_addr self.Arch
abbrev merge_n_bytes_self (self : AggregateRules) :=
  DerivedPredSig.merge_n_bytes_self self.Endian
abbrev merge_byte_equiv_merge_n_bytes (self : AggregateRules) :=
  DerivedPredSig.merge_byte_equiv_merge_n_bytes self.Endian
abbrev merge_short_eqm (self : AggregateRules) := DerivedPredSig.merge_short_eqm self.Endian
abbrev merge_int_eqm (self : AggregateRules) := DerivedPredSig.merge_int_eqm self.Endian
abbrev merge_int64_eqm (self : AggregateRules) := DerivedPredSig.merge_int64_eqm self.Endian
abbrev merge_short_value_eqm (self : AggregateRules) :=
  DerivedPredSig.merge_short_value_eqm self.Endian
abbrev merge_int_value_eqm (self : AggregateRules) :=
  DerivedPredSig.merge_int_value_eqm self.Endian
abbrev merge_int64_value_eqm (self : AggregateRules) :=
  DerivedPredSig.merge_int64_value_eqm self.Endian
abbrev valid_addr_range (self : AggregateRules) := DerivedPredSig.valid_addr_range self.Arch
abbrev valid_object (self : AggregateRules) := DerivedPredSig.valid_object self.Arch
abbrev isvalidptr_char (self : AggregateRules) := DerivedPredSig.isvalidptr_char self.Arch
abbrev isvalidptr_short (self : AggregateRules) := DerivedPredSig.isvalidptr_short self.Arch
abbrev isvalidptr_int (self : AggregateRules) := DerivedPredSig.isvalidptr_int self.Arch
abbrev isvalidptr_int64 (self : AggregateRules) := DerivedPredSig.isvalidptr_int64 self.Arch
abbrev isvalidptr_int128 (self : AggregateRules) := DerivedPredSig.isvalidptr_int128 self.Arch
abbrev isvalidptr_float (self : AggregateRules) := DerivedPredSig.isvalidptr_float self.Arch
abbrev isvalidptr_double (self : AggregateRules) := DerivedPredSig.isvalidptr_double self.Arch
abbrev isvalidptr_long_double (self : AggregateRules) :=
  DerivedPredSig.isvalidptr_long_double self.Arch
abbrev isvalidptr (self : AggregateRules) := DerivedPredSig.isvalidptr self.Arch
abbrev valid_ptr_value (self : AggregateRules) := DerivedPredSig.valid_ptr_value self.Arch

export SimpleC.SL.CommonAssertion.DerivedPredSig (
  store_byte
  store_2byte
  store_4byte
  store_8byte
  store_bytes
  store_16byte
  store_byte_noninit
  store_2byte_noninit
  store_4byte_noninit
  store_8byte_noninit
  store_bytes_noninit
  store_16byte_noninit
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
  store_int128
  undef_store_int128
  store_uint128
  undef_store_uint128
  store_float
  store_double
  store_long_double
  store_finite_float
  store_finite_double
  store_finite_long_double
  undef_store_float
  undef_store_double
  undef_store_long_double
  undef_store_finite_float
  undef_store_finite_double
  undef_store_finite_long_double
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
  front_end_type_value
  typed_poly_store
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

-- The concrete facade mirrors Coq's `Include DerivedPredSig self.Arch self.Endian`.
-- Parameterized declarations remain available through `DerivedPredSig`.
abbrev store_2byte (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_2byte self
abbrev store_4byte (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_4byte self
abbrev store_8byte (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_8byte self
abbrev store_16byte (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_16byte self
abbrev store_char (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_char self
abbrev undef_store_char (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_char self
abbrev store_uchar (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_uchar self
abbrev undef_store_uchar (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_uchar self
abbrev store_short (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_short self
abbrev undef_store_short (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_short self
abbrev store_ushort (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_ushort self
abbrev undef_store_ushort (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_ushort self
abbrev store_int (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_int self
abbrev undef_store_int (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_int self
abbrev store_uint (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_uint self
abbrev undef_store_uint (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_uint self
abbrev store_int64 (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_int64 self
abbrev undef_store_int64 (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_int64 self
abbrev store_uint64 (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_uint64 self
abbrev undef_store_uint64 (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_uint64 self
abbrev store_int128 (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_int128 self
abbrev undef_store_int128 (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_int128 self
abbrev store_uint128 (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_uint128 self
abbrev undef_store_uint128 (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_uint128 self
abbrev store_float (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_float self
abbrev undef_store_float (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_float self
abbrev store_double (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_double self
abbrev undef_store_double (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_double self
abbrev store_long_double (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_long_double self
abbrev undef_store_long_double (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_long_double self
abbrev store_finite_float (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_finite_float self
abbrev undef_store_finite_float (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_finite_float self
abbrev store_finite_double (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_finite_double self
abbrev undef_store_finite_double (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_finite_double self
abbrev store_finite_long_double (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_finite_long_double self
abbrev undef_store_finite_long_double (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_finite_long_double self
abbrev store_ptr (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_ptr self
abbrev undef_store_ptr (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.undef_store_ptr self
abbrev store_align4_list (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_align4_list self
abbrev store_align4_n (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_align4_n self
abbrev store_align_list (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_align_list self
abbrev store_align_n (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.store_align_n self
abbrev typed_poly_store (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.typed_poly_store self
abbrev poly_store (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.poly_store self
abbrev poly_undef_store (self : AggregateRules) :=
  AggregateDerivedPredSigCompat.poly_undef_store self

export SimpleC.SL.StoreAux.StoreLibSig (
  store_byte_eqm
  store_byte_store_byte_noinit
  store_bytes_store_bytes_noninit
  dup_mstore
  dup_store_byte_noninit
  dup_store_byte
  dup_store_2bytes_noninit
  dup_store_4bytes_noninit
  dup_store_8bytes_noninit
  store_byte_cast
  store_byte_cast'
  store_byte_valid
  store_4byte_valid
)

abbrev byte_eqm_unsigned_last_8 (_self : AggregateRules) :=
  StoreLibSig.byte_eqm_unsigned_last_8
abbrev byte_eqm_signed_last_8 (_self : AggregateRules) :=
  StoreLibSig.byte_eqm_signed_last_8
abbrev store_int64_store_char (self : AggregateRules) :=
  StoreLibSig.store_int64_store_char
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint64_store_uchar (self : AggregateRules) :=
  StoreLibSig.store_uint64_store_uchar
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int64_store_uchar (self : AggregateRules) :=
  StoreLibSig.store_int64_store_uchar
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint64_store_char (self : AggregateRules) :=
  StoreLibSig.store_uint64_store_char
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev merge_int64_by_ints (self : AggregateRules) :=
  StoreLibSig.merge_int64_by_ints self.Endian
abbrev signed_int_of_bytes (self : AggregateRules) :=
  StoreLibSig.signed_int_of_bytes self.Endian
abbrev unsigned_int_of_bytes (self : AggregateRules) :=
  StoreLibSig.unsigned_int_of_bytes self.Endian
abbrev merge_int_signed_of_bytes (self : AggregateRules) :=
  StoreLibSig.merge_int_signed_of_bytes (Endian := self.Endian)
abbrev merge_int_unsigned_of_bytes (self : AggregateRules) :=
  StoreLibSig.merge_int_unsigned_of_bytes (Endian := self.Endian)
abbrev signed_int_of_bytes_range (self : AggregateRules) :=
  StoreLibSig.signed_int_of_bytes_range (Endian := self.Endian)
abbrev unsigned_int_of_bytes_range (self : AggregateRules) :=
  StoreLibSig.unsigned_int_of_bytes_range (Endian := self.Endian)
abbrev store_int64_store_int (self : AggregateRules) :=
  StoreLibSig.store_int64_store_int
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint64_store_uint (self : AggregateRules) :=
  StoreLibSig.store_uint64_store_uint
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int64_store_uint (self : AggregateRules) :=
  StoreLibSig.store_int64_store_uint
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint64_store_int (self : AggregateRules) :=
  StoreLibSig.store_uint64_store_int
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_bytes_noninit_align (self : AggregateRules) :=
  StoreLibSig.store_bytes_noninit_align (Arch := self.Arch) self
abbrev undef_store_ptr_undef_store_uint64 (self : AggregateRules) :=
  StoreLibSig.undef_store_ptr_undef_store_uint64 (Arch := self.Arch) self
abbrev undef_store_ptr_undef_store_int64 (self : AggregateRules) :=
  StoreLibSig.undef_store_ptr_undef_store_int64 (Arch := self.Arch) self
abbrev undef_store_ptr_align (self : AggregateRules) :=
  StoreLibSig.undef_store_ptr_align (Arch := self.Arch) self
abbrev store_ptr_align (self : AggregateRules) :=
  StoreLibSig.store_ptr_align
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_ptr_store_uint64 (self : AggregateRules) :=
  StoreLibSig.store_ptr_store_uint64
    (Arch := self.Arch) (Endian := self.Endian) self

-- The P0-8 aggregate fixes every architecture-sensitive StoreAux member from
-- the receiver, so no architecture or endian metavariable escapes the facade.
abbrev store_n_bytes (self : AggregateRules) :=
  StoreLibSig.store_n_bytes self.Arch self.Endian self
abbrev store_n_bytes_Z (self : AggregateRules) :=
  StoreLibSig.store_n_bytes_Z self.Arch self.Endian self
abbrev store_n_bytes_noninit (self : AggregateRules) :=
  StoreLibSig.store_n_bytes_noninit self.Arch self.Endian self
abbrev store_byte_equiv_store_n_bytes_Z (self : AggregateRules) :=
  StoreLibSig.store_byte_equiv_store_n_bytes_Z self.Arch self.Endian self
abbrev store_2byte_equiv_store_n_bytes_Z (self : AggregateRules) :=
  StoreLibSig.store_2byte_equiv_store_n_bytes_Z self.Arch self.Endian self
abbrev store_4byte_equiv_store_n_bytes_Z (self : AggregateRules) :=
  StoreLibSig.store_4byte_equiv_store_n_bytes_Z self.Arch self.Endian self
abbrev store_8byte_equiv_store_n_bytes_Z (self : AggregateRules) :=
  StoreLibSig.store_8byte_equiv_store_n_bytes_Z self.Arch self.Endian self
abbrev store_2byte_store_2byte_noinit (self : AggregateRules) :=
  StoreLibSig.store_2byte_store_2byte_noinit (Endian := self.Endian) self
abbrev store_4byte_store_4byte_noinit (self : AggregateRules) :=
  StoreLibSig.store_4byte_store_4byte_noinit (Endian := self.Endian) self
abbrev store_8byte_store_8byte_noinit (self : AggregateRules) :=
  StoreLibSig.store_8byte_store_8byte_noinit (Endian := self.Endian) self
abbrev store_16byte_store_16byte_noinit (self : AggregateRules) :=
  StoreLibSig.store_16byte_store_16byte_noinit (Endian := self.Endian) self
abbrev store_ptr_undef_store_ptr (self : AggregateRules) :=
  StoreLibSig.store_ptr_undef_store_ptr
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int_range (self : AggregateRules) :=
  StoreLibSig.store_int_range (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int_undef_store_int (self : AggregateRules) :=
  StoreLibSig.store_int_undef_store_int (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_char_range (self : AggregateRules) :=
  StoreLibSig.store_char_range (Arch := self.Arch) self
abbrev store_char_undef_store_char (self : AggregateRules) :=
  StoreLibSig.store_char_undef_store_char (Arch := self.Arch) self
abbrev store_short_range (self : AggregateRules) :=
  StoreLibSig.store_short_range (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_short_undef_store_short (self : AggregateRules) :=
  StoreLibSig.store_short_undef_store_short (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int64_range (self : AggregateRules) :=
  StoreLibSig.store_int64_range (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int64_undef_store_int64 (self : AggregateRules) :=
  StoreLibSig.store_int64_undef_store_int64 (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint_range (self : AggregateRules) :=
  StoreLibSig.store_uint_range (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint_undef_store_uint (self : AggregateRules) :=
  StoreLibSig.store_uint_undef_store_uint (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uchar_range (self : AggregateRules) :=
  StoreLibSig.store_uchar_range (Arch := self.Arch) self
abbrev store_uchar_undef_store_uchar (self : AggregateRules) :=
  StoreLibSig.store_uchar_undef_store_uchar (Arch := self.Arch) self
abbrev store_ushort_range (self : AggregateRules) :=
  StoreLibSig.store_ushort_range (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_ushort_undef_store_ushort (self : AggregateRules) :=
  StoreLibSig.store_ushort_undef_store_ushort (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint64_range (self : AggregateRules) :=
  StoreLibSig.store_uint64_range (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint64_undef_store_uint64 (self : AggregateRules) :=
  StoreLibSig.store_uint64_undef_store_uint64 (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int128_range (self : AggregateRules) :=
  StoreLibSig.store_int128_range (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int128_undef_store_int128 (self : AggregateRules) :=
  StoreLibSig.store_int128_undef_store_int128 (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint128_range (self : AggregateRules) :=
  StoreLibSig.store_uint128_range (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint128_undef_store_uint128 (self : AggregateRules) :=
  StoreLibSig.store_uint128_undef_store_uint128 (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_float_undef_store_float (self : AggregateRules) :=
  StoreLibSig.store_float_undef_store_float (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_double_undef_store_double (self : AggregateRules) :=
  StoreLibSig.store_double_undef_store_double (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_long_double_undef_store_long_double (self : AggregateRules) :=
  StoreLibSig.store_long_double_undef_store_long_double
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_finite_float_undef_store_finite_float (self : AggregateRules) :=
  StoreLibSig.store_finite_float_undef_store_finite_float
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_finite_double_undef_store_finite_double (self : AggregateRules) :=
  StoreLibSig.store_finite_double_undef_store_finite_double
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_finite_long_double_undef_store_finite_long_double
    (self : AggregateRules) :=
  StoreLibSig.store_finite_long_double_undef_store_finite_long_double
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev poly_store_poly_undef_store (self : AggregateRules) :=
  StoreLibSig.poly_store_poly_undef_store (Arch := self.Arch) (Endian := self.Endian) self
abbrev typed_poly_store_poly_undef_store (self : AggregateRules) :=
  StoreLibSig.typed_poly_store_poly_undef_store
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev dup_store_2bytes (self : AggregateRules) :=
  StoreLibSig.dup_store_2bytes (Endian := self.Endian) self
abbrev dup_store_4bytes (self : AggregateRules) :=
  StoreLibSig.dup_store_4bytes (Endian := self.Endian) self
abbrev dup_store_8bytes (self : AggregateRules) :=
  StoreLibSig.dup_store_8bytes (Endian := self.Endian) self
abbrev dup_undef_store_int (self : AggregateRules) :=
  StoreLibSig.dup_undef_store_int (Arch := self.Arch) self
abbrev dup_store_int (self : AggregateRules) :=
  StoreLibSig.dup_store_int (Arch := self.Arch) (Endian := self.Endian) self
abbrev dup_undef_store_ptr (self : AggregateRules) :=
  StoreLibSig.dup_undef_store_ptr (Arch := self.Arch) self
abbrev dup_store_ptr (self : AggregateRules) :=
  StoreLibSig.dup_store_ptr (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_char_cast (self : AggregateRules) :=
  StoreLibSig.store_char_cast (Arch := self.Arch) self
abbrev store_uchar_cast (self : AggregateRules) :=
  StoreLibSig.store_uchar_cast (Arch := self.Arch) self
abbrev store_short_cast (self : AggregateRules) :=
  StoreLibSig.store_short_cast (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_ushort_cast (self : AggregateRules) :=
  StoreLibSig.store_ushort_cast (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int_cast (self : AggregateRules) :=
  StoreLibSig.store_int_cast (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint_cast (self : AggregateRules) :=
  StoreLibSig.store_uint_cast (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int64_cast (self : AggregateRules) :=
  StoreLibSig.store_int64_cast (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint64_cast (self : AggregateRules) :=
  StoreLibSig.store_uint64_cast (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_int_store_char (self : AggregateRules) :=
  StoreLibSig.store_int_store_char (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_uint_store_char (self : AggregateRules) :=
  StoreLibSig.store_uint_store_char (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_uint_undef_store_char (self : AggregateRules) :=
  StoreLibSig.undef_store_uint_undef_store_char (Arch := self.Arch) self
abbrev undef_store_int_undef_store_char (self : AggregateRules) :=
  StoreLibSig.undef_store_int_undef_store_char (Arch := self.Arch) self
abbrev valid_store_char (self : AggregateRules) :=
  StoreLibSig.valid_store_char (Arch := self.Arch) self
abbrev valid_store_uchar (self : AggregateRules) :=
  StoreLibSig.valid_store_uchar (Arch := self.Arch) self
abbrev valid_undef_store_char (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_char (Arch := self.Arch) self
abbrev valid_undef_store_uchar (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_uchar (Arch := self.Arch) self
abbrev valid_store_short (self : AggregateRules) :=
  StoreLibSig.valid_store_short (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_store_ushort (self : AggregateRules) :=
  StoreLibSig.valid_store_ushort (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_undef_store_short (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_short (Arch := self.Arch) self
abbrev valid_undef_store_ushort (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_ushort (Arch := self.Arch) self
abbrev valid_store_int (self : AggregateRules) :=
  StoreLibSig.valid_store_int (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_store_uint (self : AggregateRules) :=
  StoreLibSig.valid_store_uint (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_undef_store_int (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_int (Arch := self.Arch) self
abbrev valid_undef_store_uint (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_uint (Arch := self.Arch) self
abbrev valid_store_int64 (self : AggregateRules) :=
  StoreLibSig.valid_store_int64 (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_store_uint64 (self : AggregateRules) :=
  StoreLibSig.valid_store_uint64 (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_undef_store_int64 (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_int64 (Arch := self.Arch) self
abbrev valid_undef_store_uint64 (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_uint64 (Arch := self.Arch) self
abbrev valid_store_int128 (self : AggregateRules) :=
  StoreLibSig.valid_store_int128 (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_store_uint128 (self : AggregateRules) :=
  StoreLibSig.valid_store_uint128 (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_undef_store_int128 (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_int128 (Arch := self.Arch) self
abbrev valid_undef_store_uint128 (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_uint128 (Arch := self.Arch) self
abbrev valid_store_float (self : AggregateRules) :=
  StoreLibSig.valid_store_float (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_store_double (self : AggregateRules) :=
  StoreLibSig.valid_store_double (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_store_long_double (self : AggregateRules) :=
  StoreLibSig.valid_store_long_double (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_store_finite_float (self : AggregateRules) :=
  StoreLibSig.valid_store_finite_float (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_store_finite_double (self : AggregateRules) :=
  StoreLibSig.valid_store_finite_double (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_store_finite_long_double (self : AggregateRules) :=
  StoreLibSig.valid_store_finite_long_double
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_store_ptr (self : AggregateRules) :=
  StoreLibSig.valid_store_ptr (Arch := self.Arch) (Endian := self.Endian) self
abbrev valid_undef_store_ptr (self : AggregateRules) :=
  StoreLibSig.valid_undef_store_ptr (Arch := self.Arch) self
abbrev undef_store_char_align (self : AggregateRules) :=
  StoreLibSig.undef_store_char_align (Arch := self.Arch) self
abbrev store_char_align (self : AggregateRules) :=
  StoreLibSig.store_char_align (Arch := self.Arch) self
abbrev store_byte_align1 (self : AggregateRules) :=
  StoreLibSig.store_byte_align1 (Arch := self.Arch) self
abbrev undef_store_uchar_align (self : AggregateRules) :=
  StoreLibSig.undef_store_uchar_align (Arch := self.Arch) self
abbrev store_uchar_align (self : AggregateRules) :=
  StoreLibSig.store_uchar_align (Arch := self.Arch) self
abbrev undef_store_int_align4 (self : AggregateRules) :=
  StoreLibSig.undef_store_int_align4 (Arch := self.Arch) self
abbrev store_int_align4 (self : AggregateRules) :=
  StoreLibSig.store_int_align4 (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_uint_align4 (self : AggregateRules) :=
  StoreLibSig.undef_store_uint_align4 (Arch := self.Arch) self
abbrev store_uint_align4 (self : AggregateRules) :=
  StoreLibSig.store_uint_align4 (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_int64_align4 (self : AggregateRules) :=
  StoreLibSig.undef_store_int64_align4 (Arch := self.Arch) self
abbrev store_int64_align4 (self : AggregateRules) :=
  StoreLibSig.store_int64_align4 (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_uint64_align4 (self : AggregateRules) :=
  StoreLibSig.undef_store_uint64_align4 (Arch := self.Arch) self
abbrev store_uint64_align4 (self : AggregateRules) :=
  StoreLibSig.store_uint64_align4 (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_float_aligned4 (self : AggregateRules) :=
  StoreLibSig.store_float_aligned4 (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_double_aligned8 (self : AggregateRules) :=
  StoreLibSig.store_double_aligned8 (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_finite_float_aligned4 (self : AggregateRules) :=
  StoreLibSig.store_finite_float_aligned4 (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_finite_double_aligned8 (self : AggregateRules) :=
  StoreLibSig.store_finite_double_aligned8 (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_long_double_aligned8 (self : AggregateRules) :=
  StoreLibSig.store_long_double_aligned8 (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_finite_long_double_aligned8 (self : AggregateRules) :=
  StoreLibSig.store_finite_long_double_aligned8
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_float_align4 (self : AggregateRules) :=
  StoreLibSig.undef_store_float_align4 (Arch := self.Arch) self
abbrev store_float_align4 (self : AggregateRules) :=
  StoreLibSig.store_float_align4 (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_double_align4 (self : AggregateRules) :=
  StoreLibSig.undef_store_double_align4 (Arch := self.Arch) self
abbrev store_double_align4 (self : AggregateRules) :=
  StoreLibSig.store_double_align4 (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_int128_align (self : AggregateRules) :=
  StoreLibSig.undef_store_int128_align (Arch := self.Arch) self
abbrev store_int128_align (self : AggregateRules) :=
  StoreLibSig.store_int128_align (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_uint128_align (self : AggregateRules) :=
  StoreLibSig.undef_store_uint128_align (Arch := self.Arch) self
abbrev store_uint128_align (self : AggregateRules) :=
  StoreLibSig.store_uint128_align (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_float_align (self : AggregateRules) :=
  StoreLibSig.store_float_align (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_double_align (self : AggregateRules) :=
  StoreLibSig.store_double_align (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_long_double_align (self : AggregateRules) :=
  StoreLibSig.undef_store_long_double_align (Arch := self.Arch) self
abbrev store_long_double_align (self : AggregateRules) :=
  StoreLibSig.store_long_double_align (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_finite_float_align (self : AggregateRules) :=
  StoreLibSig.store_finite_float_align (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_finite_double_align (self : AggregateRules) :=
  StoreLibSig.store_finite_double_align (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_finite_long_double_align (self : AggregateRules) :=
  StoreLibSig.store_finite_long_double_align
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_ptr_align4 (self : AggregateRules) :=
  StoreLibSig.undef_store_ptr_align4 (Arch := self.Arch) self
abbrev store_ptr_align4 (self : AggregateRules) :=
  StoreLibSig.store_ptr_align4
    (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_align4_valid (self : AggregateRules) :=
  StoreLibSig.store_align4_valid (Arch := self.Arch) self
abbrev store_align4_merge (self : AggregateRules) :=
  StoreLibSig.store_align4_merge (Arch := self.Arch) self
abbrev store_align4_n_valid (self : AggregateRules) :=
  StoreLibSig.store_align4_n_valid (Arch := self.Arch) self
abbrev store_align_valid (self : AggregateRules) :=
  StoreLibSig.store_align_valid (Arch := self.Arch) self
abbrev store_align_merge (self : AggregateRules) :=
  StoreLibSig.store_align_merge (Arch := self.Arch) self
abbrev undef_store_short_align (self : AggregateRules) :=
  StoreLibSig.undef_store_short_align (Arch := self.Arch) self
abbrev store_short_align (self : AggregateRules) :=
  StoreLibSig.store_short_align (Arch := self.Arch) (Endian := self.Endian) self
abbrev undef_store_ushort_align (self : AggregateRules) :=
  StoreLibSig.undef_store_ushort_align (Arch := self.Arch) self
abbrev store_ushort_align (self : AggregateRules) :=
  StoreLibSig.store_ushort_align (Arch := self.Arch) (Endian := self.Endian) self
abbrev store_align_n_valid (self : AggregateRules) :=
  StoreLibSig.store_align_n_valid (Arch := self.Arch) self
abbrev store_align4_to_store_align (self : AggregateRules) :=
  StoreLibSig.store_align4_to_store_align (Arch := self.Arch) self
abbrev store_ptr_store_uint (self : AggregateRules) :=
  StoreLibSig.store_ptr_store_uint
    (Arch := self.Arch) (Endian := self.Endian) self
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
open SimpleC.SL.Array3Lib
open SimpleC.SL.ArrayLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.PtrArray2Lib
open SimpleC.SL.StoreAux
open SimpleC.SL.StringLib

abbrev derivedPredSig (self : AggregateRules) :
    DerivedPredSig self.Arch self.Endian self :=
  DerivedPredSig.canonical self.Arch self.Endian self

abbrev storeLibSig (self : AggregateRules) :
    StoreLibSig self.Arch self.Endian self self.derivedPredSig :=
  StoreLibSig.canonical self.Arch self.Endian self self.derivedPredSig

abbrev arrayLibSig (self : AggregateRules) :
    ArrayLibSig self.Arch self.Endian self self.derivedPredSig self.storeLibSig :=
  ArrayLibSig.canonical self.Arch self.Endian self self.derivedPredSig self.storeLibSig

abbrev array2LibSig (self : AggregateRules) :
    Array2LibSig self.Arch self.Endian self self.derivedPredSig self.storeLibSig
      self.arrayLibSig :=
  Array2LibSig.canonical self.Arch self.Endian self self.derivedPredSig
    self.storeLibSig self.arrayLibSig

abbrev array3LibSig (self : AggregateRules) :
    Array3LibSig self.Arch self.Endian self self.derivedPredSig self.storeLibSig
      self.arrayLibSig self.array2LibSig :=
  Array3LibSig.canonical self.Arch self.Endian self self.derivedPredSig
    self.storeLibSig self.arrayLibSig self.array2LibSig

abbrev ptrArray2LibSig (self : AggregateRules) :
    PtrArray2LibSig self.Arch self.Endian self self.derivedPredSig self.storeLibSig
      self.arrayLibSig :=
  PtrArray2LibSig.canonical self.Arch self.Endian self self.derivedPredSig
    self.storeLibSig self.arrayLibSig

-- Module-type and functor-result entry points flattened by the source Includes.
abbrev ELEMENT_STORE (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ELEMENT_STORE
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
abbrev ArrayLib (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.ArrayLibSig.ArrayFacade
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
abbrev Array2Lib (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.Array2Facade
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
abbrev Array3Lib (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.Array3Facade
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
abbrev PtrArray2Lib (self : AggregateRules) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.PtrArray2Facade
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig

-- Direct `ArrayLibCoreSig` declarations surrounding the generic ArrayLib
-- functor in Coq's flattened module surface.
abbrev store_array_rec_length (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_rec_length self
abbrev store_array_rec_Zlength (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_rec_Zlength self
abbrev store_array_rec_nil (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_rec_nil self
abbrev store_array_rec_valid (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_rec_valid self
abbrev store_array_length (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_length self
abbrev store_array_Zlength (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_Zlength self
abbrev store_array_valid (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_valid self
abbrev store_array_missing_i_rec_length (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_missing_i_rec_length self
abbrev store_array_missing_i_rec_Zlength (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_missing_i_rec_Zlength self
abbrev store_array_missing_i_rec_valid (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_missing_i_rec_valid self
abbrev store_array_missing_i_valid (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_missing_i_valid self
abbrev store_array_rec_split_to_missing_i (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_rec_split_to_missing_i self
abbrev store_array_split_to_missing_i (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_split_to_missing_i self
abbrev store_array_missing_i_merge_to_rec (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_missing_i_merge_to_rec self
abbrev store_array_missing_i_merge_to_array (self : AggregateRules) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_missing_i_merge_to_array self
abbrev repeat_Z (_self : AggregateRules) {A : Type u} :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z (A := A)
abbrev repeat_Z_tail (_self : AggregateRules) {A : Type u} :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.repeat_Z_tail (A := A)
abbrev SingleSome (_self : AggregateRules) {A : Type u} :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.SingleSome (A := A)

-- Direct `Array2LibCoreSig` declarations preceding its generic functor.
abbrev store_array_rec_to_undef_array_rec (self : AggregateRules) :=
  SimpleC.SL.Array2LibCore.Array2LibCoreSig.store_array_rec_to_undef_array_rec self
abbrev store_array_to_undef_array (self : AggregateRules) :=
  SimpleC.SL.Array2LibCore.Array2LibCoreSig.store_array_to_undef_array self
abbrev store_undef_array_rec_split_to_missing_i (self : AggregateRules) :=
  SimpleC.SL.Array2LibCore.Array2LibCoreSig.store_undef_array_rec_split_to_missing_i self
abbrev store_undef_array_split_to_missing_i (self : AggregateRules) :=
  SimpleC.SL.Array2LibCore.Array2LibCoreSig.store_undef_array_split_to_missing_i self

abbrev mapLibSig (self : AggregateRules) :
    SimpleC.SL.MapLib.MapLibSig
      self.Arch self.Endian self self.derivedPredSig self.storeLibSig :=
  SimpleC.SL.MapLib.MapLibSig.canonical
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig

-- The source module includes several StoreAux members which do not depend on
-- its logic parameter. The ignored receiver restores their aggregate shape.
abbrev vector_cons (_self : AggregateRules) {A : Type} {n : Nat}
    (x : A) (xs : Vector A n) : Vector A (n + 1) :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_cons x xs
abbrev vector_head (_self : AggregateRules) {A : Type} {n : Nat}
    (xs : Vector A (n + 1)) : A :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_head xs
abbrev vector_tail (_self : AggregateRules) {A : Type} {n : Nat}
    (xs : Vector A (n + 1)) : Vector A n :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_tail xs
abbrev vector_head_cons (_self : AggregateRules) {A : Type} {n : Nat}
    (x : A) (xs : Vector A n) :
    vector_head _self (vector_cons _self x xs) = x :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_head_cons x xs
abbrev vector_tail_cons (_self : AggregateRules) {A : Type} {n : Nat}
    (x : A) (xs : Vector A n) :
    vector_tail _self (vector_cons _self x xs) = xs :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_tail_cons x xs
abbrev vector_cons_eta (_self : AggregateRules) {A : Type} {n : Nat}
    (xs : Vector A (n + 1)) :
    vector_cons _self (vector_head _self xs) (vector_tail _self xs) = xs :=
  SimpleC.SL.StoreAux.StoreLibSig.vector_cons_eta xs
abbrev bytes_eqm (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.bytes_eqm _self.Endian
abbrev n_bytes_to_Z (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.n_bytes_to_Z _self.Endian
abbrev Z_to_n_bytes (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.Z_to_n_bytes _self.Endian
abbrev merge_n_bytes (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_n_bytes _self.Endian
abbrev eqm_iff_mod_eq (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.eqm_iff_mod_eq
abbrev eqm_bytes_to_Z_eq (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.eqm_bytes_to_Z_eq _self.Endian
abbrev Z_to_n_bytes_to_Z (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.Z_to_n_bytes_to_Z _self.Endian
abbrev merge_short_equiv_merge_n_bytes (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_short_equiv_merge_n_bytes
    _self.Endian
abbrev merge_int_equiv_merge_n_bytes (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_int_equiv_merge_n_bytes
    _self.Endian
abbrev merge_int64_equiv_merge_n_bytes (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_int64_equiv_merge_n_bytes
    _self.Endian
abbrev aligned_8_aligned_4 (_self : AggregateRules) :=
  SimpleC.SL.StoreAux.StoreLibSig.aligned_8_aligned_4

abbrev dup_data_at_error_prop (_self : AggregateRules) : Prop :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.dup_data_at_error_prop

noncomputable abbrev StoreCharAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreCharAsElement self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUCharAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreUCharAsElement self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreShortAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreShortAsElement self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUShortAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreUShortAsElement self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreIntAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreIntAsElement self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUIntAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreUIntAsElement self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreInt64AsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreInt64AsElement self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUInt64AsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreUInt64AsElement self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreInt128AsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreInt128AsElement
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUInt128AsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreUInt128AsElement
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreFloatAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreFloatAsElement
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreDoubleAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreDoubleAsElement
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreLongDoubleAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreLongDoubleAsElement
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreFiniteFloatAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreFiniteFloatAsElement
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreFiniteDoubleAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreFiniteDoubleAsElement
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreFiniteLongDoubleAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StoreFiniteLongDoubleAsElement
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StorePtrAsElement (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.StorePtrAsElement self.Arch self.Endian self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.CharArray self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.UCharArray self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.ShortArray self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.UShortArray self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.IntArray self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.UIntArray self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64Array (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.Int64Array self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64Array (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.UInt64Array self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int128Array (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.Int128Array
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt128Array (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.UInt128Array
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FloatArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.FloatArray
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev DoubleArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.DoubleArray
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev LongDoubleArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.LongDoubleArray
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteFloatArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.FiniteFloatArray
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteDoubleArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.FiniteDoubleArray
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteLongDoubleArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.FiniteLongDoubleArray
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrArray (self : AggregateRules) :=
  SimpleC.SL.ArrayLib.PtrArray self.Arch self.Endian self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.CharArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UCharArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.ShortArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UShortArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.IntArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UIntArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64Array2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.Int64Array2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64Array2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UInt64Array2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int128Array2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.Int128Array2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt128Array2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UInt128Array2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FloatArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.FloatArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev DoubleArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.DoubleArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev LongDoubleArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.LongDoubleArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteFloatArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.FiniteFloatArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteDoubleArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.FiniteDoubleArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteLongDoubleArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.FiniteLongDoubleArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrArray2 (self : AggregateRules) :=
  SimpleC.SL.Array2Lib.Array2LibSig.PtrArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.CharArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.UCharArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.ShortArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.UShortArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.IntArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.UIntArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64Array3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.Int64Array3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64Array3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.UInt64Array3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int128Array3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.Int128Array3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt128Array3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.UInt128Array3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FloatArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.FloatArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev DoubleArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.DoubleArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev LongDoubleArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.LongDoubleArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteFloatArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.FiniteFloatArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteDoubleArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.FiniteDoubleArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteLongDoubleArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.FiniteLongDoubleArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrArray3 (self : AggregateRules) :=
  SimpleC.SL.Array3Lib.Array3LibSig.PtrArray3
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharPtrArray2 (self : AggregateRules) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.CharPtrArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharPtrArray2 (self : AggregateRules) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UCharPtrArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortPtrArray2 (self : AggregateRules) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.ShortPtrArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortPtrArray2 (self : AggregateRules) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UShortPtrArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntPtrArray2 (self : AggregateRules) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.IntPtrArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntPtrArray2 (self : AggregateRules) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UIntPtrArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64PtrArray2 (self : AggregateRules) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.Int64PtrArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64PtrArray2 (self : AggregateRules) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UInt64PtrArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrPtrArray2 (self : AggregateRules) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.PtrPtrArray2
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig

-- Fixed StringLib declarations become methods of every aggregate logic. The
-- abstract predicates and laws remain separate for CRules and naive_C_Rules.
abbrev AsciiToZ (_self : AggregateRules) := StringLibSig.AsciiToZ
abbrev ZToAscii (_self : AggregateRules) := StringLibSig.ZToAscii
abbrev string_length (_self : AggregateRules) := StringLibSig.string_length
abbrev c_string (_self : AggregateRules) := StringLibSig.c_string
abbrev valid_char (_self : AggregateRules) := StringLibSig.valid_char
abbrev valid_string (_self : AggregateRules) := StringLibSig.valid_string
abbrev StringLength (_self : AggregateRules) := StringLibSig.StringLength
abbrev StringToList_nat (_self : AggregateRules) := StringLibSig.StringToList_nat
abbrev StringToList (_self : AggregateRules) := StringLibSig.StringToList
abbrev ListToString (_self : AggregateRules) := StringLibSig.ListToString
abbrev ZToAscii_AsciiToZ (_self : AggregateRules) :=
  StringLibSig.ZToAscii_AsciiToZ
abbrev ListToString_StringToList_nat_full (_self : AggregateRules) :=
  StringLibSig.ListToString_StringToList_nat_full
abbrev ListToString_StringToList (_self : AggregateRules) :=
  StringLibSig.ListToString_StringToList
abbrev valid_stringLit (_self : AggregateRules) := StringLibSig.valid_stringLit
abbrev store_string (self : AggregateRules) :=
  StringLibSig.store_string self.Arch self.Endian self self.derivedPredSig self.storeLibSig
abbrev store_stringLit (self : AggregateRules) :=
  StringLibSig.store_stringLit self.Arch self.Endian self self.derivedPredSig self.storeLibSig
abbrev c_string_Zlength (_self : AggregateRules) := StringLibSig.c_string_Zlength
abbrev StringToList_nat_length (_self : AggregateRules) :=
  StringLibSig.StringToList_nat_length
abbrev StringToList_length (_self : AggregateRules) :=
  StringLibSig.StringToList_length
abbrev StringToList_c_length (_self : AggregateRules) :=
  StringLibSig.StringToList_c_length
abbrev store_string_length (self : AggregateRules) :=
  StringLibSig.store_string_length self.Arch self.Endian self self.derivedPredSig self.storeLibSig
abbrev store_stringLit_length (self : AggregateRules) :=
  StringLibSig.store_stringLit_length self.Arch self.Endian self self.derivedPredSig self.storeLibSig
abbrev store_string_split_to_missing_i (self : AggregateRules) :=
  StringLibSig.store_string_split_to_missing_i
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
abbrev store_stringLit_split_to_missing_i (self : AggregateRules) :=
  StringLibSig.store_stringLit_split_to_missing_i
    self.Arch self.Endian self self.derivedPredSig self.storeLibSig
abbrev AsciiToZ_range (_self : AggregateRules) := StringLibSig.AsciiToZ_range


-- Exports preserve unqualified source names; explicit receivers also support
-- the flattened module surface when the aggregate itself is a variable.
abbrev store_byte (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_byte self
abbrev store_bytes (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_bytes self
abbrev store_byte_noninit (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_byte_noninit self
abbrev store_2byte_noninit (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_2byte_noninit self
abbrev store_4byte_noninit (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_4byte_noninit self
abbrev store_8byte_noninit (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_8byte_noninit self
abbrev store_bytes_noninit (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_bytes_noninit self
abbrev store_16byte_noninit (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_16byte_noninit self
abbrev Invalid_store (self : AggregateRules) {A : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.Invalid_store (A := A) self
abbrev Invalid_undef_store (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.Invalid_undef_store self
abbrev dup_data_at_error (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.dup_data_at_error self
abbrev store_array_rec (self : AggregateRules) {A : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.store_array_rec (A := A) self
abbrev store_array_missing_i_rec (self : AggregateRules) {A : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.store_array_missing_i_rec (A := A) self
abbrev store_array (self : AggregateRules) {A : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.store_array (A := A) self
abbrev store_undef_array_rec (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_undef_array_rec self
abbrev store_undef_array_missing_i_rec (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_undef_array_missing_i_rec self
abbrev store_undef_array (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.store_undef_array self
abbrev struct_padding (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.struct_padding self
abbrev union_padding (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.union_padding self
abbrev coq_prop_andp_left (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.coq_prop_andp_left self
abbrev coq_prop_andp_right (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.coq_prop_andp_right self
abbrev coq_prop_imply (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.coq_prop_imply self
abbrev coq_prop_False_left (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.coq_prop_False_left self
abbrev orp_sepcon_left (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.orp_sepcon_left self
abbrev orp_sepcon_right (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.orp_sepcon_right self
abbrev orp_sepcon_left' (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.orp_sepcon_left' self
abbrev orp_sepcon_right' (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.orp_sepcon_right' self
abbrev orp_sepcon_left_equiv (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.orp_sepcon_left_equiv self
abbrev orp_sepcon_right_equiv (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.orp_sepcon_right_equiv self
abbrev exp_right_exists (self : AggregateRules) {A : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.exp_right_exists (A := A) self
abbrev derivable1_imp (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.derivable1_imp self
abbrev derivable1_andp_mono (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.derivable1_andp_mono self
abbrev ex_logic_equiv_andp (self : AggregateRules) {A : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.ex_logic_equiv_andp (A := A) self
abbrev wand_equiv (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.wand_equiv self
abbrev ex_logic_equiv_sepcon (self : AggregateRules) {A : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.ex_logic_equiv_sepcon (A := A) self
abbrev prop_add_left (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.prop_add_left self
abbrev truep_andp_left_equiv (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.truep_andp_left_equiv self
abbrev truep_andp_right_equiv (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.truep_andp_right_equiv self
abbrev sepcon_emp_equiv (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.sepcon_emp_equiv self
abbrev sepcon_cancel_res_emp (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.sepcon_cancel_res_emp self
abbrev sepcon_cancel_end (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.sepcon_cancel_end self
abbrev sepcon_prop_equiv (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.sepcon_prop_equiv self
abbrev exp_exp_right (self : AggregateRules) {A : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.exp_exp_right (A := A) self
abbrev exp_allp_left (self : AggregateRules) {A : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.exp_allp_left (A := A) self
abbrev exp_allp_swap (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.exp_allp_swap (A := A) (B := B) self
abbrev allp_allp_swap (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.allp_allp_swap (A := A) (B := B) self
abbrev derivable1_wand_sepcon_adjoint (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.derivable1_wand_sepcon_adjoint self
abbrev all_list (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.all_list self
abbrev sepcon_emp_logic_equiv' (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.sepcon_emp_logic_equiv' self
abbrev elim_wand_emp_emp (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.elim_wand_emp_emp self
abbrev dump_spatial_left (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.dump_spatial_left self
abbrev split_pure_and_spatial_goals (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.split_pure_and_spatial_goals self
abbrev _derivable1_andp_intros (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig._derivable1_andp_intros self
abbrev add_pure_split (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.add_pure_split self
abbrev sepcon_cancel_lhs_emp (self : AggregateRules) := SimpleC.SL.CommonAssertion.DerivedPredSig.sepcon_cancel_lhs_emp self
abbrev store_byte_eqm (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.store_byte_eqm self
abbrev store_byte_store_byte_noinit (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.store_byte_store_byte_noinit self
abbrev store_bytes_store_bytes_noninit (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.store_bytes_store_bytes_noninit self
abbrev dup_mstore (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.dup_mstore self
abbrev dup_store_byte_noninit (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.dup_store_byte_noninit self
abbrev dup_store_byte (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.dup_store_byte self
abbrev dup_store_2bytes_noninit (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.dup_store_2bytes_noninit self
abbrev dup_store_4bytes_noninit (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.dup_store_4bytes_noninit self
abbrev dup_store_8bytes_noninit (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.dup_store_8bytes_noninit self
abbrev store_byte_cast (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.store_byte_cast self
abbrev store_byte_cast' (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.store_byte_cast' self
abbrev store_byte_valid (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.store_byte_valid self
abbrev store_4byte_valid (self : AggregateRules) := SimpleC.SL.StoreAux.StoreLibSig.store_4byte_valid self
abbrev store_map (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.MapLib.MapLibSig.store_map (A := A) (B := B) self
abbrev store_map_missing_i (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.MapLib.MapLibSig.store_map_missing_i (A := A) (B := B) self
abbrev store_map_split (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.MapLib.MapLibSig.store_map_split (A := A) (B := B) self
abbrev store_map_merge (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.MapLib.MapLibSig.store_map_merge (A := A) (B := B) self
abbrev store_map_missing_equiv_store_map (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.MapLib.MapLibSig.store_map_missing_equiv_store_map
    (A := A) (B := B) self
abbrev store_map_equiv_store_map_missing (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.MapLib.MapLibSig.store_map_equiv_store_map_missing
    (A := A) (B := B) self
abbrev store_map_equiv (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.MapLib.MapLibSig.store_map_equiv (A := A) (B := B) self
abbrev store_map_missing_i_equiv (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.MapLib.MapLibSig.store_map_missing_i_equiv (A := A) (B := B) self
abbrev store_map_empty (self : AggregateRules) {A B : Type} :=
  SimpleC.SL.MapLib.MapLibSig.store_map_empty (A := A) (B := B) self

end AggregateRules

end SimpleC.SL.SeparationLogic
