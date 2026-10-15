import SimpleC.SL.Assertion
import SimpleC.SL.ConAssertion
import SimpleC.SL.Array2Lib
import SimpleC.SL.Array3Lib
import SimpleC.SL.MapLib
import SimpleC.SL.PtrArray2Lib
import SimpleC.SL.StringLib
import SimpleC.SL.CriticalSTS
import SimpleC.SL.Compatibility.SeparationLogicAggregate

namespace SimpleC.SL.CommonAssertion.SeparationLogicSig

open SimpleC.SL.CArch
open SimpleC.SL.StoreAux

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

-- The concrete facade mirrors Coq's `Include DerivedPredSig Arch32 BigEndian`.
-- Parameterized declarations remain available through `DerivedPredSig`.
abbrev store_2byte (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_2byte self
abbrev store_4byte (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_4byte self
abbrev store_8byte (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_8byte self
abbrev store_16byte (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_16byte self
abbrev store_char (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_char self
abbrev undef_store_char (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_char self
abbrev store_uchar (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_uchar self
abbrev undef_store_uchar (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_uchar self
abbrev store_short (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_short self
abbrev undef_store_short (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_short self
abbrev store_ushort (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_ushort self
abbrev undef_store_ushort (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_ushort self
abbrev store_int (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_int self
abbrev undef_store_int (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_int self
abbrev store_uint (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_uint self
abbrev undef_store_uint (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_uint self
abbrev store_int64 (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_int64 self
abbrev undef_store_int64 (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_int64 self
abbrev store_uint64 (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_uint64 self
abbrev undef_store_uint64 (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_uint64 self
abbrev store_int128 (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_int128 self
abbrev undef_store_int128 (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_int128 self
abbrev store_uint128 (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_uint128 self
abbrev undef_store_uint128 (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_uint128 self
abbrev store_float (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_float self
abbrev undef_store_float (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_float self
abbrev store_double (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_double self
abbrev undef_store_double (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_double self
abbrev store_long_double (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_long_double self
abbrev undef_store_long_double (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_long_double self
abbrev store_finite_float (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_finite_float self
abbrev undef_store_finite_float (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_finite_float self
abbrev store_finite_double (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_finite_double self
abbrev undef_store_finite_double (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_finite_double self
abbrev store_finite_long_double (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_finite_long_double self
abbrev undef_store_finite_long_double (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_finite_long_double self
abbrev store_ptr (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_ptr self
abbrev undef_store_ptr (self : SeparationLogicSig) :=
  DerivedPredSigCompat.undef_store_ptr self
abbrev store_align4_list (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_align4_list self
abbrev store_align4_n (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_align4_n self
abbrev store_align_list (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_align_list self
abbrev store_align_n (self : SeparationLogicSig) :=
  DerivedPredSigCompat.store_align_n self
abbrev typed_poly_store (self : SeparationLogicSig) :=
  DerivedPredSigCompat.typed_poly_store self
abbrev poly_store (self : SeparationLogicSig) :=
  DerivedPredSigCompat.poly_store self
abbrev poly_undef_store (self : SeparationLogicSig) :=
  DerivedPredSigCompat.poly_undef_store self

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

-- Legacy source-default receiver view. The six P0-8 aggregates use the explicit
-- architecture/endian receiver in the compatibility implementation; this view
-- stays fixed to Arch32/BigEndian for old unqualified callers.
abbrev store_n_bytes (self : SeparationLogicSig) :=
  StoreLibSig.store_n_bytes Arch32 BigEndian self
abbrev store_n_bytes_Z (self : SeparationLogicSig) :=
  StoreLibSig.store_n_bytes_Z Arch32 BigEndian self
abbrev store_n_bytes_noninit (self : SeparationLogicSig) :=
  StoreLibSig.store_n_bytes_noninit Arch32 BigEndian self
abbrev store_byte_equiv_store_n_bytes_Z (self : SeparationLogicSig) :=
  StoreLibSig.store_byte_equiv_store_n_bytes_Z Arch32 BigEndian self
abbrev store_2byte_equiv_store_n_bytes_Z (self : SeparationLogicSig) :=
  StoreLibSig.store_2byte_equiv_store_n_bytes_Z Arch32 BigEndian self
abbrev store_4byte_equiv_store_n_bytes_Z (self : SeparationLogicSig) :=
  StoreLibSig.store_4byte_equiv_store_n_bytes_Z Arch32 BigEndian self
abbrev store_8byte_equiv_store_n_bytes_Z (self : SeparationLogicSig) :=
  StoreLibSig.store_8byte_equiv_store_n_bytes_Z Arch32 BigEndian self
abbrev store_2byte_store_2byte_noinit (self : SeparationLogicSig) :=
  StoreLibSig.store_2byte_store_2byte_noinit (Endian := BigEndian) self
abbrev store_4byte_store_4byte_noinit (self : SeparationLogicSig) :=
  StoreLibSig.store_4byte_store_4byte_noinit (Endian := BigEndian) self
abbrev store_8byte_store_8byte_noinit (self : SeparationLogicSig) :=
  StoreLibSig.store_8byte_store_8byte_noinit (Endian := BigEndian) self
abbrev store_16byte_store_16byte_noinit (self : SeparationLogicSig) :=
  StoreLibSig.store_16byte_store_16byte_noinit (Endian := BigEndian) self
abbrev store_ptr_undef_store_ptr (self : SeparationLogicSig) :=
  StoreLibSig.store_ptr_undef_store_ptr
    (Arch := Arch32) (Endian := BigEndian) self
abbrev store_int_range (self : SeparationLogicSig) :=
  StoreLibSig.store_int_range (Arch := Arch32) (Endian := BigEndian) self
abbrev store_int_undef_store_int (self : SeparationLogicSig) :=
  StoreLibSig.store_int_undef_store_int (Arch := Arch32) (Endian := BigEndian) self
abbrev store_char_range (self : SeparationLogicSig) :=
  StoreLibSig.store_char_range (Arch := Arch32) self
abbrev store_char_undef_store_char (self : SeparationLogicSig) :=
  StoreLibSig.store_char_undef_store_char (Arch := Arch32) self
abbrev store_short_range (self : SeparationLogicSig) :=
  StoreLibSig.store_short_range (Arch := Arch32) (Endian := BigEndian) self
abbrev store_short_undef_store_short (self : SeparationLogicSig) :=
  StoreLibSig.store_short_undef_store_short (Arch := Arch32) (Endian := BigEndian) self
abbrev store_int64_range (self : SeparationLogicSig) :=
  StoreLibSig.store_int64_range (Arch := Arch32) (Endian := BigEndian) self
abbrev store_int64_undef_store_int64 (self : SeparationLogicSig) :=
  StoreLibSig.store_int64_undef_store_int64 (Arch := Arch32) (Endian := BigEndian) self
abbrev store_uint_range (self : SeparationLogicSig) :=
  StoreLibSig.store_uint_range (Arch := Arch32) (Endian := BigEndian) self
abbrev store_uint_undef_store_uint (self : SeparationLogicSig) :=
  StoreLibSig.store_uint_undef_store_uint (Arch := Arch32) (Endian := BigEndian) self
abbrev store_uchar_range (self : SeparationLogicSig) :=
  StoreLibSig.store_uchar_range (Arch := Arch32) self
abbrev store_uchar_undef_store_uchar (self : SeparationLogicSig) :=
  StoreLibSig.store_uchar_undef_store_uchar (Arch := Arch32) self
abbrev store_ushort_range (self : SeparationLogicSig) :=
  StoreLibSig.store_ushort_range (Arch := Arch32) (Endian := BigEndian) self
abbrev store_ushort_undef_store_ushort (self : SeparationLogicSig) :=
  StoreLibSig.store_ushort_undef_store_ushort (Arch := Arch32) (Endian := BigEndian) self
abbrev store_uint64_range (self : SeparationLogicSig) :=
  StoreLibSig.store_uint64_range (Arch := Arch32) (Endian := BigEndian) self
abbrev store_uint64_undef_store_uint64 (self : SeparationLogicSig) :=
  StoreLibSig.store_uint64_undef_store_uint64 (Arch := Arch32) (Endian := BigEndian) self
abbrev store_int128_range (self : SeparationLogicSig) :=
  StoreLibSig.store_int128_range (Arch := Arch32) (Endian := BigEndian) self
abbrev store_int128_undef_store_int128 (self : SeparationLogicSig) :=
  StoreLibSig.store_int128_undef_store_int128 (Arch := Arch32) (Endian := BigEndian) self
abbrev store_uint128_range (self : SeparationLogicSig) :=
  StoreLibSig.store_uint128_range (Arch := Arch32) (Endian := BigEndian) self
abbrev store_uint128_undef_store_uint128 (self : SeparationLogicSig) :=
  StoreLibSig.store_uint128_undef_store_uint128 (Arch := Arch32) (Endian := BigEndian) self
abbrev store_float_undef_store_float (self : SeparationLogicSig) :=
  StoreLibSig.store_float_undef_store_float (Arch := Arch32) (Endian := BigEndian) self
abbrev store_double_undef_store_double (self : SeparationLogicSig) :=
  StoreLibSig.store_double_undef_store_double (Arch := Arch32) (Endian := BigEndian) self
abbrev store_long_double_undef_store_long_double (self : SeparationLogicSig) :=
  StoreLibSig.store_long_double_undef_store_long_double
    (Arch := Arch32) (Endian := BigEndian) self
abbrev store_finite_float_undef_store_finite_float (self : SeparationLogicSig) :=
  StoreLibSig.store_finite_float_undef_store_finite_float
    (Arch := Arch32) (Endian := BigEndian) self
abbrev store_finite_double_undef_store_finite_double (self : SeparationLogicSig) :=
  StoreLibSig.store_finite_double_undef_store_finite_double
    (Arch := Arch32) (Endian := BigEndian) self
abbrev store_finite_long_double_undef_store_finite_long_double
    (self : SeparationLogicSig) :=
  StoreLibSig.store_finite_long_double_undef_store_finite_long_double
    (Arch := Arch32) (Endian := BigEndian) self
abbrev poly_store_poly_undef_store (self : SeparationLogicSig) :=
  StoreLibSig.poly_store_poly_undef_store (Arch := Arch32) (Endian := BigEndian) self
abbrev typed_poly_store_poly_undef_store (self : SeparationLogicSig) :=
  StoreLibSig.typed_poly_store_poly_undef_store
    (Arch := Arch32) (Endian := BigEndian) self
abbrev dup_store_2bytes (self : SeparationLogicSig) :=
  StoreLibSig.dup_store_2bytes (Endian := BigEndian) self
abbrev dup_store_4bytes (self : SeparationLogicSig) :=
  StoreLibSig.dup_store_4bytes (Endian := BigEndian) self
abbrev dup_store_8bytes (self : SeparationLogicSig) :=
  StoreLibSig.dup_store_8bytes (Endian := BigEndian) self
abbrev dup_undef_store_int (self : SeparationLogicSig) :=
  StoreLibSig.dup_undef_store_int (Arch := Arch32) self
abbrev dup_store_int (self : SeparationLogicSig) :=
  StoreLibSig.dup_store_int (Arch := Arch32) (Endian := BigEndian) self
abbrev dup_undef_store_ptr (self : SeparationLogicSig) :=
  StoreLibSig.dup_undef_store_ptr (Arch := Arch32) self
abbrev dup_store_ptr (self : SeparationLogicSig) :=
  StoreLibSig.dup_store_ptr (Arch := Arch32) (Endian := BigEndian) self
abbrev store_char_cast (self : SeparationLogicSig) :=
  StoreLibSig.store_char_cast (Arch := Arch32) self
abbrev store_uchar_cast (self : SeparationLogicSig) :=
  StoreLibSig.store_uchar_cast (Arch := Arch32) self
abbrev store_short_cast (self : SeparationLogicSig) :=
  StoreLibSig.store_short_cast (Arch := Arch32) (Endian := BigEndian) self
abbrev store_ushort_cast (self : SeparationLogicSig) :=
  StoreLibSig.store_ushort_cast (Arch := Arch32) (Endian := BigEndian) self
abbrev store_int_cast (self : SeparationLogicSig) :=
  StoreLibSig.store_int_cast (Arch := Arch32) (Endian := BigEndian) self
abbrev store_uint_cast (self : SeparationLogicSig) :=
  StoreLibSig.store_uint_cast (Arch := Arch32) (Endian := BigEndian) self
abbrev store_int64_cast (self : SeparationLogicSig) :=
  StoreLibSig.store_int64_cast (Arch := Arch32) (Endian := BigEndian) self
abbrev store_uint64_cast (self : SeparationLogicSig) :=
  StoreLibSig.store_uint64_cast (Arch := Arch32) (Endian := BigEndian) self
abbrev store_int_store_char (self : SeparationLogicSig) :=
  StoreLibSig.store_int_store_char (Arch := Arch32) (Endian := BigEndian) self
abbrev store_uint_store_char (self : SeparationLogicSig) :=
  StoreLibSig.store_uint_store_char (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_uint_undef_store_char (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_uint_undef_store_char (Arch := Arch32) self
abbrev undef_store_int_undef_store_char (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_int_undef_store_char (Arch := Arch32) self
abbrev valid_store_char (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_char (Arch := Arch32) self
abbrev valid_store_uchar (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_uchar (Arch := Arch32) self
abbrev valid_undef_store_char (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_char (Arch := Arch32) self
abbrev valid_undef_store_uchar (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_uchar (Arch := Arch32) self
abbrev valid_store_short (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_short (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_store_ushort (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_ushort (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_undef_store_short (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_short (Arch := Arch32) self
abbrev valid_undef_store_ushort (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_ushort (Arch := Arch32) self
abbrev valid_store_int (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_int (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_store_uint (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_uint (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_undef_store_int (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_int (Arch := Arch32) self
abbrev valid_undef_store_uint (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_uint (Arch := Arch32) self
abbrev valid_store_int64 (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_int64 (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_store_uint64 (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_uint64 (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_undef_store_int64 (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_int64 (Arch := Arch32) self
abbrev valid_undef_store_uint64 (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_uint64 (Arch := Arch32) self
abbrev valid_store_int128 (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_int128 (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_store_uint128 (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_uint128 (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_undef_store_int128 (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_int128 (Arch := Arch32) self
abbrev valid_undef_store_uint128 (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_uint128 (Arch := Arch32) self
abbrev valid_store_float (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_float (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_store_double (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_double (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_store_long_double (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_long_double (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_store_finite_float (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_finite_float (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_store_finite_double (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_finite_double (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_store_finite_long_double (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_finite_long_double
    (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_store_ptr (self : SeparationLogicSig) :=
  StoreLibSig.valid_store_ptr (Arch := Arch32) (Endian := BigEndian) self
abbrev valid_undef_store_ptr (self : SeparationLogicSig) :=
  StoreLibSig.valid_undef_store_ptr (Arch := Arch32) self
abbrev undef_store_char_align (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_char_align (Arch := Arch32) self
abbrev store_char_align (self : SeparationLogicSig) :=
  StoreLibSig.store_char_align (Arch := Arch32) self
abbrev store_byte_align1 (self : SeparationLogicSig) :=
  StoreLibSig.store_byte_align1 (Arch := Arch32) self
abbrev undef_store_uchar_align (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_uchar_align (Arch := Arch32) self
abbrev store_uchar_align (self : SeparationLogicSig) :=
  StoreLibSig.store_uchar_align (Arch := Arch32) self
abbrev undef_store_int_align4 (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_int_align4 (Arch := Arch32) self
abbrev store_int_align4 (self : SeparationLogicSig) :=
  StoreLibSig.store_int_align4 (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_uint_align4 (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_uint_align4 (Arch := Arch32) self
abbrev store_uint_align4 (self : SeparationLogicSig) :=
  StoreLibSig.store_uint_align4 (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_int64_align4 (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_int64_align4 (Arch := Arch32) self
abbrev store_int64_align4 (self : SeparationLogicSig) :=
  StoreLibSig.store_int64_align4 (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_uint64_align4 (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_uint64_align4 (Arch := Arch32) self
abbrev store_uint64_align4 (self : SeparationLogicSig) :=
  StoreLibSig.store_uint64_align4 (Arch := Arch32) (Endian := BigEndian) self
abbrev store_float_aligned4 (self : SeparationLogicSig) :=
  StoreLibSig.store_float_aligned4 (Arch := Arch32) (Endian := BigEndian) self
abbrev store_double_aligned8 (self : SeparationLogicSig) :=
  StoreLibSig.store_double_aligned8 (Arch := Arch32) (Endian := BigEndian) self
abbrev store_finite_float_aligned4 (self : SeparationLogicSig) :=
  StoreLibSig.store_finite_float_aligned4 (Arch := Arch32) (Endian := BigEndian) self
abbrev store_finite_double_aligned8 (self : SeparationLogicSig) :=
  StoreLibSig.store_finite_double_aligned8 (Arch := Arch32) (Endian := BigEndian) self
abbrev store_long_double_aligned8 (self : SeparationLogicSig) :=
  StoreLibSig.store_long_double_aligned8 (Arch := Arch32) (Endian := BigEndian) self
abbrev store_finite_long_double_aligned8 (self : SeparationLogicSig) :=
  StoreLibSig.store_finite_long_double_aligned8
    (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_float_align4 (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_float_align4 (Arch := Arch32) self
abbrev store_float_align4 (self : SeparationLogicSig) :=
  StoreLibSig.store_float_align4 (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_double_align4 (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_double_align4 (Arch := Arch32) self
abbrev store_double_align4 (self : SeparationLogicSig) :=
  StoreLibSig.store_double_align4 (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_int128_align (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_int128_align (Arch := Arch32) self
abbrev store_int128_align (self : SeparationLogicSig) :=
  StoreLibSig.store_int128_align (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_uint128_align (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_uint128_align (Arch := Arch32) self
abbrev store_uint128_align (self : SeparationLogicSig) :=
  StoreLibSig.store_uint128_align (Arch := Arch32) (Endian := BigEndian) self
abbrev store_float_align (self : SeparationLogicSig) :=
  StoreLibSig.store_float_align (Arch := Arch32) (Endian := BigEndian) self
abbrev store_double_align (self : SeparationLogicSig) :=
  StoreLibSig.store_double_align (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_long_double_align (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_long_double_align (Arch := Arch32) self
abbrev store_long_double_align (self : SeparationLogicSig) :=
  StoreLibSig.store_long_double_align (Arch := Arch32) (Endian := BigEndian) self
abbrev store_finite_float_align (self : SeparationLogicSig) :=
  StoreLibSig.store_finite_float_align (Arch := Arch32) (Endian := BigEndian) self
abbrev store_finite_double_align (self : SeparationLogicSig) :=
  StoreLibSig.store_finite_double_align (Arch := Arch32) (Endian := BigEndian) self
abbrev store_finite_long_double_align (self : SeparationLogicSig) :=
  StoreLibSig.store_finite_long_double_align
    (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_ptr_align4 (self : SeparationLogicSig) (x : Int) :=
  StoreLibSig.undef_store_ptr_align4 (Arch := Arch32) self x rfl
abbrev store_ptr_align4 (self : SeparationLogicSig) (x v : Int) :=
  StoreLibSig.store_ptr_align4
    (Arch := Arch32) (Endian := BigEndian) self x v rfl
abbrev store_align4_valid (self : SeparationLogicSig) :=
  StoreLibSig.store_align4_valid (Arch := Arch32) self
abbrev store_align4_merge (self : SeparationLogicSig) :=
  StoreLibSig.store_align4_merge (Arch := Arch32) self
abbrev store_align4_n_valid (self : SeparationLogicSig) :=
  StoreLibSig.store_align4_n_valid (Arch := Arch32) self
abbrev store_align_valid (self : SeparationLogicSig) :=
  StoreLibSig.store_align_valid (Arch := Arch32) self
abbrev store_align_merge (self : SeparationLogicSig) :=
  StoreLibSig.store_align_merge (Arch := Arch32) self
abbrev undef_store_short_align (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_short_align (Arch := Arch32) self
abbrev store_short_align (self : SeparationLogicSig) :=
  StoreLibSig.store_short_align (Arch := Arch32) (Endian := BigEndian) self
abbrev undef_store_ushort_align (self : SeparationLogicSig) :=
  StoreLibSig.undef_store_ushort_align (Arch := Arch32) self
abbrev store_ushort_align (self : SeparationLogicSig) :=
  StoreLibSig.store_ushort_align (Arch := Arch32) (Endian := BigEndian) self
abbrev store_align_n_valid (self : SeparationLogicSig) :=
  StoreLibSig.store_align_n_valid (Arch := Arch32) self
abbrev store_align4_to_store_align (self : SeparationLogicSig) :=
  StoreLibSig.store_align4_to_store_align (Arch := Arch32) self
abbrev store_ptr_store_uint (self : SeparationLogicSig) (x v : Int) :=
  StoreLibSig.store_ptr_store_uint
    (Arch := Arch32) (Endian := BigEndian) self x v rfl rfl

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

abbrev derivedPredSig (self : SeparationLogicSig) :
    DerivedPredSig Arch32 BigEndian self :=
  DerivedPredSig.canonical Arch32 BigEndian self

abbrev storeLibSig (self : SeparationLogicSig) :
    StoreLibSig Arch32 BigEndian self self.derivedPredSig :=
  StoreLibSig.canonical Arch32 BigEndian self self.derivedPredSig

abbrev arrayLibSig (self : SeparationLogicSig) :
    ArrayLibSig Arch32 BigEndian self self.derivedPredSig self.storeLibSig :=
  ArrayLibSig.canonical Arch32 BigEndian self self.derivedPredSig self.storeLibSig

abbrev array2LibSig (self : SeparationLogicSig) :
    Array2LibSig Arch32 BigEndian self self.derivedPredSig self.storeLibSig
      self.arrayLibSig :=
  Array2LibSig.canonical Arch32 BigEndian self self.derivedPredSig
    self.storeLibSig self.arrayLibSig

abbrev array3LibSig (self : SeparationLogicSig) :
    Array3LibSig Arch32 BigEndian self self.derivedPredSig self.storeLibSig
      self.arrayLibSig self.array2LibSig :=
  Array3LibSig.canonical Arch32 BigEndian self self.derivedPredSig
    self.storeLibSig self.arrayLibSig self.array2LibSig

abbrev ptrArray2LibSig (self : SeparationLogicSig) :
    PtrArray2LibSig Arch32 BigEndian self self.derivedPredSig self.storeLibSig
      self.arrayLibSig :=
  PtrArray2LibSig.canonical Arch32 BigEndian self self.derivedPredSig
    self.storeLibSig self.arrayLibSig

abbrev mapLibSig (self : SeparationLogicSig) :
    SimpleC.SL.MapLib.MapLibSig
      Arch32 BigEndian self self.derivedPredSig self.storeLibSig :=
  SimpleC.SL.MapLib.MapLibSig.canonical
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig

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
  SimpleC.SL.StoreAux.StoreLibSig.bytes_eqm SimpleC.SL.CArch.BigEndian
abbrev n_bytes_to_Z (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.n_bytes_to_Z SimpleC.SL.CArch.BigEndian
abbrev Z_to_n_bytes (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.Z_to_n_bytes SimpleC.SL.CArch.BigEndian
abbrev merge_n_bytes (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_n_bytes SimpleC.SL.CArch.BigEndian
abbrev eqm_iff_mod_eq (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.eqm_iff_mod_eq
abbrev n_bytes_to_Z_cons (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSigCompat.n_bytes_to_Z_cons
abbrev eqm_bytes_to_Z_eq (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.eqm_bytes_to_Z_eq SimpleC.SL.CArch.BigEndian
abbrev Z_to_n_bytes_succ (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSigCompat.Z_to_n_bytes_succ
abbrev Z_to_n_bytes_to_Z (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.Z_to_n_bytes_to_Z SimpleC.SL.CArch.BigEndian
abbrev merge_short_equiv_merge_n_bytes (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_short_equiv_merge_n_bytes
    SimpleC.SL.CArch.BigEndian
abbrev merge_int_equiv_merge_n_bytes (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_int_equiv_merge_n_bytes
    SimpleC.SL.CArch.BigEndian
abbrev merge_int64_equiv_merge_n_bytes (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.merge_int64_equiv_merge_n_bytes
    SimpleC.SL.CArch.BigEndian
abbrev aligned_8_aligned_4 (_self : SeparationLogicSig) :=
  SimpleC.SL.StoreAux.StoreLibSig.aligned_8_aligned_4

abbrev dup_data_at_error_prop (_self : SeparationLogicSig) : Prop :=
  SimpleC.SL.CommonAssertion.DerivedPredSig.dup_data_at_error_prop

noncomputable abbrev StoreCharAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreCharAsElement Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUCharAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreUCharAsElement Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreShortAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreShortAsElement Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUShortAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreUShortAsElement Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreIntAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreIntAsElement Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUIntAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreUIntAsElement Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreInt64AsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreInt64AsElement Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUInt64AsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreUInt64AsElement Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreInt128AsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreInt128AsElement
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreUInt128AsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreUInt128AsElement
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreFloatAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreFloatAsElement
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreDoubleAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreDoubleAsElement
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreLongDoubleAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreLongDoubleAsElement
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreFiniteFloatAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreFiniteFloatAsElement
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreFiniteDoubleAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreFiniteDoubleAsElement
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StoreFiniteLongDoubleAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StoreFiniteLongDoubleAsElement
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev StorePtrAsElement (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.StorePtrAsElement Arch32 BigEndian self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.CharArray Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.UCharArray Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.ShortArray Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.UShortArray Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.IntArray Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.UIntArray Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64Array (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.Int64Array Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64Array (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.UInt64Array Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int128Array (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.Int128Array
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt128Array (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.UInt128Array
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FloatArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.FloatArray
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev DoubleArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.DoubleArray
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev LongDoubleArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.LongDoubleArray
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteFloatArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.FiniteFloatArray
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteDoubleArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.FiniteDoubleArray
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteLongDoubleArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.FiniteLongDoubleArray
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrArray (self : SeparationLogicSig) :=
  SimpleC.SL.ArrayLib.PtrArray Arch32 BigEndian self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.CharArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UCharArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.ShortArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UShortArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.IntArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UIntArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64Array2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.Int64Array2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64Array2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UInt64Array2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int128Array2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.Int128Array2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt128Array2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.UInt128Array2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FloatArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.FloatArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev DoubleArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.DoubleArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev LongDoubleArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.LongDoubleArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteFloatArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.FiniteFloatArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteDoubleArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.FiniteDoubleArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteLongDoubleArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.FiniteLongDoubleArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.Array2Lib.Array2LibSig.PtrArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.CharArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.UCharArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.ShortArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.UShortArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.IntArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.UIntArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64Array3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.Int64Array3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64Array3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.UInt64Array3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int128Array3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.Int128Array3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt128Array3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.UInt128Array3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FloatArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.FloatArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev DoubleArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.DoubleArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev LongDoubleArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.LongDoubleArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteFloatArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.FiniteFloatArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteDoubleArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.FiniteDoubleArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev FiniteLongDoubleArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.FiniteLongDoubleArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrArray3 (self : SeparationLogicSig) :=
  SimpleC.SL.Array3Lib.Array3LibSig.PtrArray3
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig

noncomputable abbrev CharPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.CharPtrArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UCharPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UCharPtrArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev ShortPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.ShortPtrArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UShortPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UShortPtrArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev IntPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.IntPtrArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UIntPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UIntPtrArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev Int64PtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.Int64PtrArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev UInt64PtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.UInt64PtrArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
noncomputable abbrev PtrPtrArray2 (self : SeparationLogicSig) :=
  SimpleC.SL.PtrArray2Lib.PtrArray2LibSig.PtrPtrArray2
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig

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
  StringLibSig.store_string Arch32 BigEndian self self.derivedPredSig self.storeLibSig
abbrev store_stringLit (self : SeparationLogicSig) :=
  StringLibSig.store_stringLit Arch32 BigEndian self self.derivedPredSig self.storeLibSig
abbrev c_string_Zlength (_self : SeparationLogicSig) := StringLibSig.c_string_Zlength
abbrev StringToList_nat_length (_self : SeparationLogicSig) :=
  StringLibSig.StringToList_nat_length
abbrev StringToList_length (_self : SeparationLogicSig) :=
  StringLibSig.StringToList_length
abbrev StringToList_c_length (_self : SeparationLogicSig) :=
  StringLibSig.StringToList_c_length
abbrev store_string_length (self : SeparationLogicSig) :=
  StringLibSig.store_string_length Arch32 BigEndian self self.derivedPredSig self.storeLibSig
abbrev store_stringLit_length (self : SeparationLogicSig) :=
  StringLibSig.store_stringLit_length Arch32 BigEndian self self.derivedPredSig self.storeLibSig
abbrev store_string_split_to_missing_i (self : SeparationLogicSig) :=
  StringLibSig.store_string_split_to_missing_i
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
abbrev store_stringLit_split_to_missing_i (self : SeparationLogicSig) :=
  StringLibSig.store_stringLit_split_to_missing_i
    Arch32 BigEndian self self.derivedPredSig self.storeLibSig
abbrev AsciiToZ_range (_self : SeparationLogicSig) := StringLibSig.AsciiToZ_range

end SimpleC.SL.CommonAssertion.SeparationLogicSig

namespace SimpleC.SL.SeparationLogic

export SimpleC.SL.FloatLib (
  fp32 fp64 fp128
  fp32_nan_payload fp32_nan_payload_valid
  fp64_nan_payload fp64_nan_payload_valid
  fp128_nan_payload fp128_nan_payload_valid
  fp32_nan fp64_nan fp128_nan
  fp32_unary_nan fp64_unary_nan fp128_unary_nan
  fp32_binary_nan fp64_binary_nan fp128_binary_nan
  fp32_add fp32_sub fp32_mul fp32_div fp32_neg
  fp64_add fp64_sub fp64_mul fp64_div fp64_neg
  fp128_add fp128_sub fp128_mul fp128_div fp128_neg
  fp32_isFinite fp64_isFinite fp128_isFinite
  fp32_isNaN fp64_isNaN fp128_isNaN
  fp32_isInf fp64_isInf fp128_isInf
  fp32_compare fp64_compare fp128_compare
  fp32_eq fp32_ne fp32_lt fp32_le fp32_gt fp32_ge
  fp64_eq fp64_ne fp64_lt fp64_le fp64_gt fp64_ge
  fp128_eq fp128_ne fp128_lt fp128_le fp128_gt fp128_ge
  fp32_of_bits fp64_of_bits fp128_of_bits
  bits_of_fp32 bits_of_fp64 bits_of_fp128
  bits_of_float_value bits_of_double_value bits_of_long_double_value
  max_unsigned_128
  bits_of_float_value_range bits_of_double_value_range
  bits_of_long_double_value_range
  fexp32 fexp64 fexp128
  rounded32 rounded64 rounded128
  in_float32_range in_float64_range in_float128_range
  rounded32_generic rounded64_generic rounded128_generic
  fp32_of_real fp64_of_real fp128_of_real
  fp32_of_Z fp64_of_Z fp128_of_Z
  Z_to_fp32 Z_to_fp64 Z_to_fp128
  fp32_to_R fp64_to_R fp128_to_R
  fp32_to_R_total fp64_to_R_total fp128_to_R_total
  fp32_zero fp32_neg_zero fp64_zero fp64_neg_zero fp128_zero fp128_neg_zero
  fp32_pos_infinity fp32_neg_infinity
  fp64_pos_infinity fp64_neg_infinity
  fp128_pos_infinity fp128_neg_infinity
  FLT_MAX FLT_MIN DBL_MAX DBL_MIN LDBL_MAX LDBL_MIN
)

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CArch
open SimpleC.SL.ConAssertion
open SimpleC.SL.StringLib

abbrev naive_CSL : CSL STS_naive := CSL.canonical STS_naive

namespace CRules32

private abbrev baseRules : SeparationLogicSig := SimpleC.SL.Assertion.SL
private abbrev dePredSig := DerivedPredSig.canonical Arch32 BigEndian baseRules
private abbrev storeSig := StoreAux.StoreLibSig.canonical
  Arch32 BigEndian baseRules dePredSig
private abbrev arraySig := ArrayLib.ArrayLibSig.canonical
  Arch32 BigEndian baseRules dePredSig storeSig
private abbrev storeStringLit :=
  StringLibSig.store_stringLit Arch32 BigEndian baseRules dePredSig storeSig

abbrev front_end_type_value := DerivedPredSig.front_end_type_value

axiom GlobalStrings :
  (CoqString -> SimpleC.SL.Mem.addr) -> baseRules.expr
axiom GlobalStrings_missing :
  (CoqString -> SimpleC.SL.Mem.addr) -> List CoqString -> baseRules.expr
axiom GlobalStrings_split : forall LitMap s,
  baseRules.derivable1 (GlobalStrings LitMap)
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_merge : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
    (GlobalStrings LitMap)
axiom GlobalStrings_missing_split : forall LitMap l s,
  s ∉ l ->
  baseRules.derivable1 (GlobalStrings_missing LitMap l)
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_missing_merge : forall LitMap l s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
    (GlobalStrings_missing LitMap l)
axiom GlobalStrings_split_existing : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (storeStringLit (LitMap s) s) (GlobalStrings LitMap))
    (baseRules.sepcon (storeStringLit (LitMap s) s)
      (GlobalStrings_missing LitMap [s]))

def stringLibSig :
    StringLibSig Arch32 BigEndian baseRules dePredSig storeSig arraySig where
  GlobalStrings := GlobalStrings
  GlobalStrings_missing := GlobalStrings_missing
  GlobalStrings_split := GlobalStrings_split
  GlobalStrings_merge := GlobalStrings_merge
  GlobalStrings_missing_split := GlobalStrings_missing_split
  GlobalStrings_missing_merge := GlobalStrings_missing_merge
  GlobalStrings_split_existing := GlobalStrings_split_existing

end CRules32

namespace CRules64

private abbrev baseRules : SeparationLogicSig := SimpleC.SL.Assertion.SL
private abbrev dePredSig := DerivedPredSig.canonical Arch64 BigEndian baseRules
private abbrev storeSig := StoreAux.StoreLibSig.canonical
  Arch64 BigEndian baseRules dePredSig
private abbrev arraySig := ArrayLib.ArrayLibSig.canonical
  Arch64 BigEndian baseRules dePredSig storeSig
private abbrev storeStringLit :=
  StringLibSig.store_stringLit Arch64 BigEndian baseRules dePredSig storeSig

abbrev front_end_type_value := DerivedPredSig.front_end_type_value

axiom GlobalStrings :
  (CoqString -> SimpleC.SL.Mem.addr) -> baseRules.expr
axiom GlobalStrings_missing :
  (CoqString -> SimpleC.SL.Mem.addr) -> List CoqString -> baseRules.expr
axiom GlobalStrings_split : forall LitMap s,
  baseRules.derivable1 (GlobalStrings LitMap)
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_merge : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
    (GlobalStrings LitMap)
axiom GlobalStrings_missing_split : forall LitMap l s,
  s ∉ l ->
  baseRules.derivable1 (GlobalStrings_missing LitMap l)
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_missing_merge : forall LitMap l s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
    (GlobalStrings_missing LitMap l)
axiom GlobalStrings_split_existing : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (storeStringLit (LitMap s) s) (GlobalStrings LitMap))
    (baseRules.sepcon (storeStringLit (LitMap s) s)
      (GlobalStrings_missing LitMap [s]))

def stringLibSig :
    StringLibSig Arch64 BigEndian baseRules dePredSig storeSig arraySig where
  GlobalStrings := GlobalStrings
  GlobalStrings_missing := GlobalStrings_missing
  GlobalStrings_split := GlobalStrings_split
  GlobalStrings_merge := GlobalStrings_merge
  GlobalStrings_missing_split := GlobalStrings_missing_split
  GlobalStrings_missing_merge := GlobalStrings_missing_merge
  GlobalStrings_split_existing := GlobalStrings_split_existing

end CRules64

namespace naive_C_Rules32

private abbrev baseRules : SeparationLogicSig := naive_CSL.toSeparationLogicSig
private abbrev dePredSig := DerivedPredSig.canonical Arch32 BigEndian baseRules
private abbrev storeSig := StoreAux.StoreLibSig.canonical
  Arch32 BigEndian baseRules dePredSig
private abbrev arraySig := ArrayLib.ArrayLibSig.canonical
  Arch32 BigEndian baseRules dePredSig storeSig
private abbrev storeStringLit :=
  StringLibSig.store_stringLit Arch32 BigEndian baseRules dePredSig storeSig

abbrev front_end_type_value := DerivedPredSig.front_end_type_value

axiom GlobalStrings :
  (CoqString -> SimpleC.SL.Mem.addr) -> baseRules.expr
axiom GlobalStrings_missing :
  (CoqString -> SimpleC.SL.Mem.addr) -> List CoqString -> baseRules.expr
axiom GlobalStrings_split : forall LitMap s,
  baseRules.derivable1 (GlobalStrings LitMap)
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_merge : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
    (GlobalStrings LitMap)
axiom GlobalStrings_missing_split : forall LitMap l s,
  s ∉ l ->
  baseRules.derivable1 (GlobalStrings_missing LitMap l)
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_missing_merge : forall LitMap l s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
    (GlobalStrings_missing LitMap l)
axiom GlobalStrings_split_existing : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (storeStringLit (LitMap s) s) (GlobalStrings LitMap))
    (baseRules.sepcon (storeStringLit (LitMap s) s)
      (GlobalStrings_missing LitMap [s]))

def stringLibSig :
    StringLibSig Arch32 BigEndian baseRules dePredSig storeSig arraySig where
  GlobalStrings := GlobalStrings
  GlobalStrings_missing := GlobalStrings_missing
  GlobalStrings_split := GlobalStrings_split
  GlobalStrings_merge := GlobalStrings_merge
  GlobalStrings_missing_split := GlobalStrings_missing_split
  GlobalStrings_missing_merge := GlobalStrings_missing_merge
  GlobalStrings_split_existing := GlobalStrings_split_existing

end naive_C_Rules32

namespace naive_C_Rules64

private abbrev baseRules : SeparationLogicSig := naive_CSL.toSeparationLogicSig
private abbrev dePredSig := DerivedPredSig.canonical Arch64 BigEndian baseRules
private abbrev storeSig := StoreAux.StoreLibSig.canonical
  Arch64 BigEndian baseRules dePredSig
private abbrev arraySig := ArrayLib.ArrayLibSig.canonical
  Arch64 BigEndian baseRules dePredSig storeSig
private abbrev storeStringLit :=
  StringLibSig.store_stringLit Arch64 BigEndian baseRules dePredSig storeSig

abbrev front_end_type_value := DerivedPredSig.front_end_type_value

axiom GlobalStrings :
  (CoqString -> SimpleC.SL.Mem.addr) -> baseRules.expr
axiom GlobalStrings_missing :
  (CoqString -> SimpleC.SL.Mem.addr) -> List CoqString -> baseRules.expr
axiom GlobalStrings_split : forall LitMap s,
  baseRules.derivable1 (GlobalStrings LitMap)
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_merge : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
    (GlobalStrings LitMap)
axiom GlobalStrings_missing_split : forall LitMap l s,
  s ∉ l ->
  baseRules.derivable1 (GlobalStrings_missing LitMap l)
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_missing_merge : forall LitMap l s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
    (GlobalStrings_missing LitMap l)
axiom GlobalStrings_split_existing : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (storeStringLit (LitMap s) s) (GlobalStrings LitMap))
    (baseRules.sepcon (storeStringLit (LitMap s) s)
      (GlobalStrings_missing LitMap [s]))

def stringLibSig :
    StringLibSig Arch64 BigEndian baseRules dePredSig storeSig arraySig where
  GlobalStrings := GlobalStrings
  GlobalStrings_missing := GlobalStrings_missing
  GlobalStrings_split := GlobalStrings_split
  GlobalStrings_merge := GlobalStrings_merge
  GlobalStrings_missing_split := GlobalStrings_missing_split
  GlobalStrings_missing_merge := GlobalStrings_missing_merge
  GlobalStrings_split_existing := GlobalStrings_split_existing

end naive_C_Rules64

namespace Snaive_C_Rules32

private abbrev baseRules : SeparationLogicSig := naive_CSL.toSeparationLogicSig
private abbrev dePredSig := DerivedPredSig.canonical Arch32 LittleEndian baseRules
private abbrev storeSig := StoreAux.StoreLibSig.canonical
  Arch32 LittleEndian baseRules dePredSig
private abbrev arraySig := ArrayLib.ArrayLibSig.canonical
  Arch32 LittleEndian baseRules dePredSig storeSig
private abbrev storeStringLit :=
  StringLibSig.store_stringLit Arch32 LittleEndian baseRules dePredSig storeSig

abbrev front_end_type_value := DerivedPredSig.front_end_type_value

axiom GlobalStrings :
  (CoqString -> SimpleC.SL.Mem.addr) -> baseRules.expr
axiom GlobalStrings_missing :
  (CoqString -> SimpleC.SL.Mem.addr) -> List CoqString -> baseRules.expr
axiom GlobalStrings_split : forall LitMap s,
  baseRules.derivable1 (GlobalStrings LitMap)
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_merge : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
    (GlobalStrings LitMap)
axiom GlobalStrings_missing_split : forall LitMap l s,
  s ∉ l ->
  baseRules.derivable1 (GlobalStrings_missing LitMap l)
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_missing_merge : forall LitMap l s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
    (GlobalStrings_missing LitMap l)
axiom GlobalStrings_split_existing : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (storeStringLit (LitMap s) s) (GlobalStrings LitMap))
    (baseRules.sepcon (storeStringLit (LitMap s) s)
      (GlobalStrings_missing LitMap [s]))

def stringLibSig :
    StringLibSig Arch32 LittleEndian baseRules dePredSig storeSig arraySig where
  GlobalStrings := GlobalStrings
  GlobalStrings_missing := GlobalStrings_missing
  GlobalStrings_split := GlobalStrings_split
  GlobalStrings_merge := GlobalStrings_merge
  GlobalStrings_missing_split := GlobalStrings_missing_split
  GlobalStrings_missing_merge := GlobalStrings_missing_merge
  GlobalStrings_split_existing := GlobalStrings_split_existing

end Snaive_C_Rules32

namespace Snaive_C_Rules64

private abbrev baseRules : SeparationLogicSig := naive_CSL.toSeparationLogicSig
private abbrev dePredSig := DerivedPredSig.canonical Arch64 LittleEndian baseRules
private abbrev storeSig := StoreAux.StoreLibSig.canonical
  Arch64 LittleEndian baseRules dePredSig
private abbrev arraySig := ArrayLib.ArrayLibSig.canonical
  Arch64 LittleEndian baseRules dePredSig storeSig
private abbrev storeStringLit :=
  StringLibSig.store_stringLit Arch64 LittleEndian baseRules dePredSig storeSig

abbrev front_end_type_value := DerivedPredSig.front_end_type_value

axiom GlobalStrings :
  (CoqString -> SimpleC.SL.Mem.addr) -> baseRules.expr
axiom GlobalStrings_missing :
  (CoqString -> SimpleC.SL.Mem.addr) -> List CoqString -> baseRules.expr
axiom GlobalStrings_split : forall LitMap s,
  baseRules.derivable1 (GlobalStrings LitMap)
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_merge : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap [s])
      (storeStringLit (LitMap s) s))
    (GlobalStrings LitMap)
axiom GlobalStrings_missing_split : forall LitMap l s,
  s ∉ l ->
  baseRules.derivable1 (GlobalStrings_missing LitMap l)
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
axiom GlobalStrings_missing_merge : forall LitMap l s,
  baseRules.derivable1
    (baseRules.sepcon (GlobalStrings_missing LitMap (s :: l))
      (storeStringLit (LitMap s) s))
    (GlobalStrings_missing LitMap l)
axiom GlobalStrings_split_existing : forall LitMap s,
  baseRules.derivable1
    (baseRules.sepcon (storeStringLit (LitMap s) s) (GlobalStrings LitMap))
    (baseRules.sepcon (storeStringLit (LitMap s) s)
      (GlobalStrings_missing LitMap [s]))

def stringLibSig :
    StringLibSig Arch64 LittleEndian baseRules dePredSig storeSig arraySig where
  GlobalStrings := GlobalStrings
  GlobalStrings_missing := GlobalStrings_missing
  GlobalStrings_split := GlobalStrings_split
  GlobalStrings_merge := GlobalStrings_merge
  GlobalStrings_missing_split := GlobalStrings_missing_split
  GlobalStrings_missing_merge := GlobalStrings_missing_merge
  GlobalStrings_split_existing := GlobalStrings_split_existing

end Snaive_C_Rules64

def CRules32 : AggregateRules :=
  { SimpleC.SL.Assertion.SL with
    Arch := Arch32
    Endian := BigEndian }

def CRules64 : AggregateRules :=
  { SimpleC.SL.Assertion.SL with
    Arch := Arch64
    Endian := BigEndian }

def naive_C_Rules32 : AggregateRules :=
  { naive_CSL.toSeparationLogicSig with
    Arch := Arch32
    Endian := BigEndian }

def naive_C_Rules64 : AggregateRules :=
  { naive_CSL.toSeparationLogicSig with
    Arch := Arch64
    Endian := BigEndian }

def Snaive_C_Rules32 : AggregateRules :=
  { naive_CSL.toSeparationLogicSig with
    Arch := Arch32
    Endian := LittleEndian }

def Snaive_C_Rules64 : AggregateRules :=
  { naive_CSL.toSeparationLogicSig with
    Arch := Arch64
    Endian := LittleEndian }

namespace naive_C_Rules32
abbrev sts := STS_naive.sts
abbrev at_states := naive_CSL.at_states
abbrev has_tokens := naive_CSL.has_tokens
end naive_C_Rules32

namespace naive_C_Rules64
abbrev sts := STS_naive.sts
abbrev at_states := naive_CSL.at_states
abbrev has_tokens := naive_CSL.has_tokens
end naive_C_Rules64

namespace Snaive_C_Rules32
abbrev sts := STS_naive.sts
abbrev at_states := naive_CSL.at_states
abbrev has_tokens := naive_CSL.has_tokens
end Snaive_C_Rules32

namespace Snaive_C_Rules64
abbrev sts := STS_naive.sts
abbrev at_states := naive_CSL.at_states
abbrev has_tokens := naive_CSL.has_tokens
end Snaive_C_Rules64

namespace CRules32

theorem ptr_size_eq_4 : CRules32.Arch.ptr_size = 4 := rfl
theorem ptr_size_Z_eq_4 : CRules32.Arch.ptr_size_Z = 4 := rfl
theorem addr_max_unsigned_eq_int :
    CRules32.Arch.addr_max_unsigned = Int.max_unsigned := rfl

theorem undef_store_ptr_align4_32 (x : Int) :
    CRules32.derivable1 (CRules32.undef_store_ptr x)
      (CRules32.store_align4_n 1) :=
  StoreAux.StoreLibSig.undef_store_ptr_align4
    (Arch := Arch32) CRules32 x rfl

theorem store_ptr_align4_32 (x v : Int) :
    CRules32.derivable1 (CRules32.store_ptr x v)
      (CRules32.store_align4_n 1) :=
  StoreAux.StoreLibSig.store_ptr_align4
    (Arch := Arch32) (Endian := CRules32.Endian) CRules32 x v rfl

theorem store_ptr_store_uint_32 (x v : Int) :
    CRules32.derivable1 (CRules32.store_ptr x v)
      (CRules32.store_uint x v) :=
  StoreAux.StoreLibSig.store_ptr_store_uint
    (Arch := Arch32) (Endian := CRules32.Endian) CRules32 x v rfl rfl

end CRules32

namespace CRules64

theorem ptr_size_eq_8 : CRules64.Arch.ptr_size = 8 := rfl
theorem ptr_size_Z_eq_8 : CRules64.Arch.ptr_size_Z = 8 := rfl
theorem addr_max_unsigned_eq_int64 :
    CRules64.Arch.addr_max_unsigned = Int64.max_unsigned := rfl

theorem undef_store_ptr_undef_store_uint64_64 (x : Int) :
    CRules64.derivable1 (CRules64.undef_store_ptr x)
      (CRules64.undef_store_uint64 x) :=
  StoreAux.StoreLibSig.undef_store_ptr_undef_store_uint64
    (Arch := Arch64) CRules64 x rfl

theorem undef_store_ptr_align4_64 (x : Int) :
    CRules64.derivable1 (CRules64.undef_store_ptr x)
      (CRules64.store_align4_n 2) :=
  CRules64.toContext.derivable1_trans _ _ _
    (undef_store_ptr_undef_store_uint64_64 x)
    (StoreAux.StoreLibSig.undef_store_uint64_align4
      (Arch := Arch64) CRules64 x)

theorem store_ptr_align4_64 (x v : Int) :
    CRules64.derivable1 (CRules64.store_ptr x v)
      (CRules64.store_align4_n 2) :=
  CRules64.toContext.derivable1_trans _ _ _
    (StoreAux.StoreLibSig.store_ptr_undef_store_ptr
      (Arch := Arch64) (Endian := CRules64.Endian) CRules64 x v)
    (undef_store_ptr_align4_64 x)

theorem store_ptr_store_uint64_64 (x v : Int) :
    CRules64.derivable1 (CRules64.store_ptr x v)
      (CRules64.store_uint64 x v) :=
  StoreAux.StoreLibSig.store_ptr_store_uint64
    (Arch := Arch64) (Endian := CRules64.Endian) CRules64 x v rfl rfl

end CRules64

namespace naive_C_Rules32

theorem ptr_size_eq_4 : naive_C_Rules32.Arch.ptr_size = 4 := rfl
theorem ptr_size_Z_eq_4 : naive_C_Rules32.Arch.ptr_size_Z = 4 := rfl
theorem addr_max_unsigned_eq_int :
    naive_C_Rules32.Arch.addr_max_unsigned = Int.max_unsigned := rfl

theorem undef_store_ptr_align4_32 (x : Int) :
    naive_C_Rules32.derivable1 (naive_C_Rules32.undef_store_ptr x)
      (naive_C_Rules32.store_align4_n 1) :=
  StoreAux.StoreLibSig.undef_store_ptr_align4
    (Arch := Arch32) naive_C_Rules32 x rfl

theorem store_ptr_align4_32 (x v : Int) :
    naive_C_Rules32.derivable1 (naive_C_Rules32.store_ptr x v)
      (naive_C_Rules32.store_align4_n 1) :=
  StoreAux.StoreLibSig.store_ptr_align4
    (Arch := Arch32) (Endian := naive_C_Rules32.Endian) naive_C_Rules32 x v rfl

theorem store_ptr_store_uint_32 (x v : Int) :
    naive_C_Rules32.derivable1 (naive_C_Rules32.store_ptr x v)
      (naive_C_Rules32.store_uint x v) :=
  StoreAux.StoreLibSig.store_ptr_store_uint
    (Arch := Arch32) (Endian := naive_C_Rules32.Endian) naive_C_Rules32 x v rfl rfl

end naive_C_Rules32

namespace naive_C_Rules64

theorem ptr_size_eq_8 : naive_C_Rules64.Arch.ptr_size = 8 := rfl
theorem ptr_size_Z_eq_8 : naive_C_Rules64.Arch.ptr_size_Z = 8 := rfl
theorem addr_max_unsigned_eq_int64 :
    naive_C_Rules64.Arch.addr_max_unsigned = Int64.max_unsigned := rfl

theorem undef_store_ptr_undef_store_uint64_64 (x : Int) :
    naive_C_Rules64.derivable1 (naive_C_Rules64.undef_store_ptr x)
      (naive_C_Rules64.undef_store_uint64 x) :=
  StoreAux.StoreLibSig.undef_store_ptr_undef_store_uint64
    (Arch := Arch64) naive_C_Rules64 x rfl

theorem undef_store_ptr_align4_64 (x : Int) :
    naive_C_Rules64.derivable1 (naive_C_Rules64.undef_store_ptr x)
      (naive_C_Rules64.store_align4_n 2) :=
  naive_C_Rules64.toContext.derivable1_trans _ _ _
    (undef_store_ptr_undef_store_uint64_64 x)
    (StoreAux.StoreLibSig.undef_store_uint64_align4
      (Arch := Arch64) naive_C_Rules64 x)

theorem store_ptr_align4_64 (x v : Int) :
    naive_C_Rules64.derivable1 (naive_C_Rules64.store_ptr x v)
      (naive_C_Rules64.store_align4_n 2) :=
  naive_C_Rules64.toContext.derivable1_trans _ _ _
    (StoreAux.StoreLibSig.store_ptr_undef_store_ptr
      (Arch := Arch64) (Endian := naive_C_Rules64.Endian) naive_C_Rules64 x v)
    (undef_store_ptr_align4_64 x)

theorem store_ptr_store_uint64_64 (x v : Int) :
    naive_C_Rules64.derivable1 (naive_C_Rules64.store_ptr x v)
      (naive_C_Rules64.store_uint64 x v) :=
  StoreAux.StoreLibSig.store_ptr_store_uint64
    (Arch := Arch64) (Endian := naive_C_Rules64.Endian) naive_C_Rules64 x v rfl rfl

end naive_C_Rules64

namespace Snaive_C_Rules32

theorem ptr_size_eq_4 : Snaive_C_Rules32.Arch.ptr_size = 4 := rfl
theorem ptr_size_Z_eq_4 : Snaive_C_Rules32.Arch.ptr_size_Z = 4 := rfl
theorem addr_max_unsigned_eq_int :
    Snaive_C_Rules32.Arch.addr_max_unsigned = Int.max_unsigned := rfl

theorem undef_store_ptr_align4_32 (x : Int) :
    Snaive_C_Rules32.derivable1 (Snaive_C_Rules32.undef_store_ptr x)
      (Snaive_C_Rules32.store_align4_n 1) :=
  StoreAux.StoreLibSig.undef_store_ptr_align4
    (Arch := Arch32) Snaive_C_Rules32 x rfl

theorem store_ptr_align4_32 (x v : Int) :
    Snaive_C_Rules32.derivable1 (Snaive_C_Rules32.store_ptr x v)
      (Snaive_C_Rules32.store_align4_n 1) :=
  StoreAux.StoreLibSig.store_ptr_align4
    (Arch := Arch32) (Endian := Snaive_C_Rules32.Endian) Snaive_C_Rules32 x v rfl

theorem store_ptr_store_uint_32 (x v : Int) :
    Snaive_C_Rules32.derivable1 (Snaive_C_Rules32.store_ptr x v)
      (Snaive_C_Rules32.store_uint x v) :=
  StoreAux.StoreLibSig.store_ptr_store_uint
    (Arch := Arch32) (Endian := Snaive_C_Rules32.Endian) Snaive_C_Rules32 x v rfl rfl

end Snaive_C_Rules32

namespace Snaive_C_Rules64

theorem ptr_size_eq_8 : Snaive_C_Rules64.Arch.ptr_size = 8 := rfl
theorem ptr_size_Z_eq_8 : Snaive_C_Rules64.Arch.ptr_size_Z = 8 := rfl
theorem addr_max_unsigned_eq_int64 :
    Snaive_C_Rules64.Arch.addr_max_unsigned = Int64.max_unsigned := rfl

theorem undef_store_ptr_undef_store_uint64_64 (x : Int) :
    Snaive_C_Rules64.derivable1 (Snaive_C_Rules64.undef_store_ptr x)
      (Snaive_C_Rules64.undef_store_uint64 x) :=
  StoreAux.StoreLibSig.undef_store_ptr_undef_store_uint64
    (Arch := Arch64) Snaive_C_Rules64 x rfl

theorem undef_store_ptr_align4_64 (x : Int) :
    Snaive_C_Rules64.derivable1 (Snaive_C_Rules64.undef_store_ptr x)
      (Snaive_C_Rules64.store_align4_n 2) :=
  Snaive_C_Rules64.toContext.derivable1_trans _ _ _
    (undef_store_ptr_undef_store_uint64_64 x)
    (StoreAux.StoreLibSig.undef_store_uint64_align4
      (Arch := Arch64) Snaive_C_Rules64 x)

theorem store_ptr_align4_64 (x v : Int) :
    Snaive_C_Rules64.derivable1 (Snaive_C_Rules64.store_ptr x v)
      (Snaive_C_Rules64.store_align4_n 2) :=
  Snaive_C_Rules64.toContext.derivable1_trans _ _ _
    (StoreAux.StoreLibSig.store_ptr_undef_store_ptr
      (Arch := Arch64) (Endian := Snaive_C_Rules64.Endian) Snaive_C_Rules64 x v)
    (undef_store_ptr_align4_64 x)

theorem store_ptr_store_uint64_64 (x v : Int) :
    Snaive_C_Rules64.derivable1 (Snaive_C_Rules64.store_ptr x v)
      (Snaive_C_Rules64.store_uint64 x v) :=
  StoreAux.StoreLibSig.store_ptr_store_uint64
    (Arch := Arch64) (Endian := Snaive_C_Rules64.Endian) Snaive_C_Rules64 x v rfl rfl

end Snaive_C_Rules64

abbrev CRules : AggregateRules := CRules32
abbrev naive_C_Rules : AggregateRules := naive_C_Rules32
abbrev Snaive_C_Rules : AggregateRules := Snaive_C_Rules32

namespace CRules
abbrev front_end_type_value := CRules32.front_end_type_value
abbrev GlobalStrings := CRules32.GlobalStrings
abbrev GlobalStrings_missing := CRules32.GlobalStrings_missing
abbrev GlobalStrings_split := CRules32.GlobalStrings_split
abbrev GlobalStrings_merge := CRules32.GlobalStrings_merge
abbrev GlobalStrings_missing_split := CRules32.GlobalStrings_missing_split
abbrev GlobalStrings_missing_merge := CRules32.GlobalStrings_missing_merge
abbrev GlobalStrings_split_existing := CRules32.GlobalStrings_split_existing
abbrev stringLibSig := CRules32.stringLibSig
abbrev ptr_size_eq_4 := CRules32.ptr_size_eq_4
abbrev ptr_size_Z_eq_4 := CRules32.ptr_size_Z_eq_4
abbrev addr_max_unsigned_eq_int := CRules32.addr_max_unsigned_eq_int
abbrev undef_store_ptr_align4_32 := CRules32.undef_store_ptr_align4_32
abbrev store_ptr_align4_32 := CRules32.store_ptr_align4_32
abbrev store_ptr_store_uint_32 := CRules32.store_ptr_store_uint_32
end CRules

namespace naive_C_Rules
abbrev sts := STS_naive.sts
abbrev at_states := naive_CSL.at_states
abbrev has_tokens := naive_CSL.has_tokens
abbrev front_end_type_value := naive_C_Rules32.front_end_type_value
abbrev GlobalStrings := naive_C_Rules32.GlobalStrings
abbrev GlobalStrings_missing := naive_C_Rules32.GlobalStrings_missing
abbrev GlobalStrings_split := naive_C_Rules32.GlobalStrings_split
abbrev GlobalStrings_merge := naive_C_Rules32.GlobalStrings_merge
abbrev GlobalStrings_missing_split := naive_C_Rules32.GlobalStrings_missing_split
abbrev GlobalStrings_missing_merge := naive_C_Rules32.GlobalStrings_missing_merge
abbrev GlobalStrings_split_existing := naive_C_Rules32.GlobalStrings_split_existing
abbrev stringLibSig := naive_C_Rules32.stringLibSig
abbrev ptr_size_eq_4 := naive_C_Rules32.ptr_size_eq_4
abbrev ptr_size_Z_eq_4 := naive_C_Rules32.ptr_size_Z_eq_4
abbrev addr_max_unsigned_eq_int := naive_C_Rules32.addr_max_unsigned_eq_int
abbrev undef_store_ptr_align4_32 := naive_C_Rules32.undef_store_ptr_align4_32
abbrev store_ptr_align4_32 := naive_C_Rules32.store_ptr_align4_32
abbrev store_ptr_store_uint_32 := naive_C_Rules32.store_ptr_store_uint_32
end naive_C_Rules

namespace Snaive_C_Rules
abbrev sts := STS_naive.sts
abbrev at_states := naive_CSL.at_states
abbrev has_tokens := naive_CSL.has_tokens
abbrev front_end_type_value := Snaive_C_Rules32.front_end_type_value
abbrev GlobalStrings := Snaive_C_Rules32.GlobalStrings
abbrev GlobalStrings_missing := Snaive_C_Rules32.GlobalStrings_missing
abbrev GlobalStrings_split := Snaive_C_Rules32.GlobalStrings_split
abbrev GlobalStrings_merge := Snaive_C_Rules32.GlobalStrings_merge
abbrev GlobalStrings_missing_split := Snaive_C_Rules32.GlobalStrings_missing_split
abbrev GlobalStrings_missing_merge := Snaive_C_Rules32.GlobalStrings_missing_merge
abbrev GlobalStrings_split_existing := Snaive_C_Rules32.GlobalStrings_split_existing
abbrev stringLibSig := Snaive_C_Rules32.stringLibSig
abbrev ptr_size_eq_4 := Snaive_C_Rules32.ptr_size_eq_4
abbrev ptr_size_Z_eq_4 := Snaive_C_Rules32.ptr_size_Z_eq_4
abbrev addr_max_unsigned_eq_int := Snaive_C_Rules32.addr_max_unsigned_eq_int
abbrev undef_store_ptr_align4_32 := Snaive_C_Rules32.undef_store_ptr_align4_32
abbrev store_ptr_align4_32 := Snaive_C_Rules32.store_ptr_align4_32
abbrev store_ptr_store_uint_32 := Snaive_C_Rules32.store_ptr_store_uint_32
end Snaive_C_Rules

axiom field_address : Int -> String -> String -> Int

def should_be_equal {A : Type} (_x _y : A) : Prop := True

end SimpleC.SL.SeparationLogic
