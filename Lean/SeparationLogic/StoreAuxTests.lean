import SimpleC.SL.StoreAux
import SimpleC.SL.Assertion
import Lean.Util.CollectAxioms

namespace StoreAuxTests

open AUXLib
open CompCert
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.DerivedPredSigCompat
open SimpleC.SL.CArch
open SimpleC.SL.FloatLib
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open SimpleC.SL.Assertion
open scoped SimpleC.SL.SAC

local instance : SacContext := ⟨SL⟩

open Lean Elab Command

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env ← getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "API manifest declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkApiContract) "#check_api_contract " "[" ident,* "]"
  " => " num : command

elab_rules : command
  | `(#check_api_contract [$ids:ident,*] => $expected:num) => do
      let names ← resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual ← apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "StoreAux API type hash changed: expected {expected}, got {actual}"
      let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "StoreAux declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"StoreAux API contract verified for {names.size} declarations"

-- Module-type counterpart, vector compatibility layer, and seven source definitions.
#check StoreLibSig
#check StoreLibSig.canonical
#check StoreLibSig.vector_cons
#check StoreLibSig.vector_head
#check StoreLibSig.vector_tail
#check StoreLibSig.vector_head_cons
#check StoreLibSig.vector_tail_cons
#check StoreLibSig.vector_cons_eta
#check StoreLibSig.bytes_eqm
#check StoreLibSig.n_bytes_to_Z
#check StoreLibSig.Z_to_n_bytes
#check StoreLibSig.merge_n_bytes
#check store_n_bytes
#check store_n_bytes_Z
#check store_n_bytes_noninit

-- All 13 generic source theorems.
#check store_byte_eqm
#check eqm_iff_mod_eq
#check StoreLibSigCompat.n_bytes_to_Z_cons
#check StoreLibSig.eqm_bytes_to_Z_eq
#check StoreLibSigCompat.Z_to_n_bytes_succ
#check StoreLibSig.Z_to_n_bytes_to_Z
#check StoreLibSig.merge_short_equiv_merge_n_bytes
#check StoreLibSig.merge_int_equiv_merge_n_bytes
#check StoreLibSig.merge_int64_equiv_merge_n_bytes
#check store_byte_equiv_store_n_bytes_Z
#check store_2byte_equiv_store_n_bytes_Z
#check store_4byte_equiv_store_n_bytes_Z
#check store_8byte_equiv_store_n_bytes_Z

-- All 49 relation/range/duplication/cast/decomposition source theorems.
#check store_byte_store_byte_noinit
#check store_2byte_store_2byte_noinit
#check store_4byte_store_4byte_noinit
#check store_8byte_store_8byte_noinit
#check store_bytes_store_bytes_noninit
#check store_16byte_store_16byte_noinit
#check store_ptr_undef_store_ptr
#check store_int_range
#check store_int_undef_store_int
#check store_char_range
#check store_char_undef_store_char
#check store_short_range
#check store_short_undef_store_short
#check store_int64_range
#check store_int64_undef_store_int64
#check store_uint_range
#check store_uint_undef_store_uint
#check store_uchar_range
#check store_uchar_undef_store_uchar
#check store_ushort_range
#check store_ushort_undef_store_ushort
#check store_uint64_range
#check store_uint64_undef_store_uint64
#check store_int128_range
#check store_int128_undef_store_int128
#check store_uint128_range
#check store_uint128_undef_store_uint128
#check store_float_undef_store_float
#check store_double_undef_store_double
#check store_long_double_undef_store_long_double
#check store_finite_float_undef_store_finite_float
#check store_finite_double_undef_store_finite_double
#check store_finite_long_double_undef_store_finite_long_double
#check poly_store_poly_undef_store
#check typed_poly_store_poly_undef_store
#check dup_mstore
#check dup_store_byte_noninit
#check dup_store_byte
#check dup_store_2bytes_noninit
#check dup_store_2bytes
#check dup_store_4bytes_noninit
#check dup_store_4bytes
#check dup_store_8bytes_noninit
#check dup_store_8bytes
#check dup_undef_store_int
#check dup_store_int
#check dup_undef_store_ptr
#check dup_store_ptr
#check store_byte_cast
#check store_byte_cast'
#check store_char_cast
#check store_uchar_cast
#check store_short_cast
#check store_ushort_cast
#check store_int_cast
#check store_uint_cast
#check store_int64_cast
#check store_uint64_cast
#check store_int_store_char
#check store_uint_store_char
#check undef_store_uint_undef_store_char
#check undef_store_int_undef_store_char

-- All 47 validity and alignment source theorems.
#check valid_store_char
#check valid_store_uchar
#check valid_undef_store_char
#check valid_undef_store_uchar
#check valid_store_short
#check valid_store_ushort
#check valid_undef_store_short
#check valid_undef_store_ushort
#check valid_store_int
#check valid_store_uint
#check valid_undef_store_int
#check valid_undef_store_uint
#check valid_store_int64
#check valid_store_uint64
#check valid_undef_store_int64
#check valid_undef_store_uint64
#check valid_store_int128
#check valid_store_uint128
#check valid_undef_store_int128
#check valid_undef_store_uint128
#check valid_store_float
#check valid_store_double
#check valid_store_long_double
#check valid_store_finite_float
#check valid_store_finite_double
#check valid_store_finite_long_double
#check valid_store_ptr
#check valid_undef_store_ptr
#check undef_store_char_align
#check store_char_align
#check store_byte_align1
#check undef_store_uchar_align
#check store_uchar_align
#check undef_store_int_align4
#check store_int_align4
#check undef_store_uint_align4
#check store_uint_align4
#check undef_store_int64_align4
#check store_int64_align4
#check undef_store_uint64_align4
#check store_uint64_align4
#check aligned_8_aligned_4
#check store_float_aligned4
#check store_double_aligned8
#check store_finite_float_aligned4
#check store_finite_double_aligned8
#check store_long_double_aligned8
#check store_finite_long_double_aligned8
#check undef_store_float_align4
#check store_float_align4
#check undef_store_double_align4
#check store_double_align4
#check undef_store_int128_align
#check store_int128_align
#check undef_store_uint128_align
#check store_uint128_align
#check store_float_align
#check store_double_align
#check undef_store_long_double_align
#check store_long_double_align
#check store_finite_float_align
#check store_finite_double_align
#check store_finite_long_double_align
#check undef_store_ptr_align4
#check store_ptr_align4
#check store_byte_valid
#check store_4byte_valid
#check store_align4_valid
#check store_align4_merge
#check store_align4_n_valid
#check store_align_valid
#check store_align_merge
#check undef_store_short_align
#check store_short_align
#check undef_store_ushort_align
#check store_ushort_align
#check store_align_n_valid
#check store_align4_to_store_align
#check store_ptr_store_uint

-- Candidate P0-6 declarations which were absent from the previous contract.
#check byte_eqm_unsigned_last_8
#check byte_eqm_signed_last_8
#check store_int64_store_char
#check store_uint64_store_uchar
#check store_int64_store_uchar
#check store_uint64_store_char
#check merge_int64_by_ints
#check signed_int_of_bytes
#check unsigned_int_of_bytes
#check merge_int_signed_of_bytes
#check merge_int_unsigned_of_bytes
#check signed_int_of_bytes_range
#check unsigned_int_of_bytes_range
#check store_int64_store_int
#check store_uint64_store_uint
#check store_int64_store_uint
#check store_uint64_store_int
#check store_bytes_noninit_align
#check undef_store_ptr_undef_store_uint64
#check undef_store_ptr_undef_store_int64
#check undef_store_ptr_align
#check store_ptr_align
#check store_ptr_store_uint64

-- This list freezes names, complete types, binder order, and binder visibility.
-- It also rejects axioms outside the three expected Lean foundations.
#check_api_contract [
  StoreLibSig,
  StoreLibSig.canonical,
  StoreLibSig.vector_cons,
  StoreLibSig.vector_head,
  StoreLibSig.vector_tail,
  StoreLibSig.vector_head_cons,
  StoreLibSig.vector_tail_cons,
  StoreLibSig.vector_cons_eta,
  StoreLibSig.bytes_eqm,
  StoreLibSig.n_bytes_to_Z,
  StoreLibSig.Z_to_n_bytes,
  StoreLibSig.merge_n_bytes,
  store_n_bytes,
  store_n_bytes_Z,
  store_n_bytes_noninit,
  store_byte_eqm,
  eqm_iff_mod_eq,
  StoreLibSigCompat.n_bytes_to_Z_cons,
  StoreLibSig.eqm_bytes_to_Z_eq,
  StoreLibSigCompat.Z_to_n_bytes_succ,
  StoreLibSig.Z_to_n_bytes_to_Z,
  StoreLibSig.merge_short_equiv_merge_n_bytes,
  StoreLibSig.merge_int_equiv_merge_n_bytes,
  StoreLibSig.merge_int64_equiv_merge_n_bytes,
  store_byte_equiv_store_n_bytes_Z,
  store_2byte_equiv_store_n_bytes_Z,
  store_4byte_equiv_store_n_bytes_Z,
  store_8byte_equiv_store_n_bytes_Z,
  store_byte_store_byte_noinit,
  store_2byte_store_2byte_noinit,
  store_4byte_store_4byte_noinit,
  store_8byte_store_8byte_noinit,
  store_bytes_store_bytes_noninit,
  store_16byte_store_16byte_noinit,
  store_ptr_undef_store_ptr,
  store_int_range,
  store_int_undef_store_int,
  store_char_range,
  store_char_undef_store_char,
  store_short_range,
  store_short_undef_store_short,
  store_int64_range,
  store_int64_undef_store_int64,
  store_uint_range,
  store_uint_undef_store_uint,
  store_uchar_range,
  store_uchar_undef_store_uchar,
  store_ushort_range,
  store_ushort_undef_store_ushort,
  store_uint64_range,
  store_uint64_undef_store_uint64,
  store_int128_range,
  store_int128_undef_store_int128,
  store_uint128_range,
  store_uint128_undef_store_uint128,
  store_float_undef_store_float,
  store_double_undef_store_double,
  store_long_double_undef_store_long_double,
  store_finite_float_undef_store_finite_float,
  store_finite_double_undef_store_finite_double,
  store_finite_long_double_undef_store_finite_long_double,
  poly_store_poly_undef_store,
  typed_poly_store_poly_undef_store,
  dup_mstore,
  dup_store_byte_noninit,
  dup_store_byte,
  dup_store_2bytes_noninit,
  dup_store_2bytes,
  dup_store_4bytes_noninit,
  dup_store_4bytes,
  dup_store_8bytes_noninit,
  dup_store_8bytes,
  dup_undef_store_int,
  dup_store_int,
  dup_undef_store_ptr,
  dup_store_ptr,
  store_byte_cast,
  store_byte_cast',
  store_char_cast,
  store_uchar_cast,
  store_short_cast,
  store_ushort_cast,
  store_int_cast,
  store_uint_cast,
  store_int64_cast,
  store_uint64_cast,
  store_int_store_char,
  store_uint_store_char,
  undef_store_uint_undef_store_char,
  undef_store_int_undef_store_char,
  valid_store_char,
  valid_store_uchar,
  valid_undef_store_char,
  valid_undef_store_uchar,
  valid_store_short,
  valid_store_ushort,
  valid_undef_store_short,
  valid_undef_store_ushort,
  valid_store_int,
  valid_store_uint,
  valid_undef_store_int,
  valid_undef_store_uint,
  valid_store_int64,
  valid_store_uint64,
  valid_undef_store_int64,
  valid_undef_store_uint64,
  valid_store_int128,
  valid_store_uint128,
  valid_undef_store_int128,
  valid_undef_store_uint128,
  valid_store_float,
  valid_store_double,
  valid_store_long_double,
  valid_store_finite_float,
  valid_store_finite_double,
  valid_store_finite_long_double,
  valid_store_ptr,
  valid_undef_store_ptr,
  undef_store_char_align,
  store_char_align,
  store_byte_align1,
  undef_store_uchar_align,
  store_uchar_align,
  undef_store_int_align4,
  store_int_align4,
  undef_store_uint_align4,
  store_uint_align4,
  undef_store_int64_align4,
  store_int64_align4,
  undef_store_uint64_align4,
  store_uint64_align4,
  aligned_8_aligned_4,
  store_float_aligned4,
  store_double_aligned8,
  store_finite_float_aligned4,
  store_finite_double_aligned8,
  store_long_double_aligned8,
  store_finite_long_double_aligned8,
  undef_store_float_align4,
  store_float_align4,
  undef_store_double_align4,
  store_double_align4,
  undef_store_int128_align,
  store_int128_align,
  undef_store_uint128_align,
  store_uint128_align,
  store_float_align,
  store_double_align,
  undef_store_long_double_align,
  store_long_double_align,
  store_finite_float_align,
  store_finite_double_align,
  store_finite_long_double_align,
  undef_store_ptr_align4,
  store_ptr_align4,
  store_byte_valid,
  store_4byte_valid,
  store_align4_valid,
  store_align4_merge,
  store_align4_n_valid,
  store_align_valid,
  store_align_merge,
  undef_store_short_align,
  store_short_align,
  undef_store_ushort_align,
  store_ushort_align,
  store_align_n_valid,
  store_align4_to_store_align,
  store_ptr_store_uint,
  byte_eqm_unsigned_last_8,
  byte_eqm_signed_last_8,
  store_int64_store_char,
  store_uint64_store_uchar,
  store_int64_store_uchar,
  store_uint64_store_char,
  merge_int64_by_ints,
  signed_int_of_bytes,
  unsigned_int_of_bytes,
  merge_int_signed_of_bytes,
  merge_int_unsigned_of_bytes,
  signed_int_of_bytes_range,
  unsigned_int_of_bytes_range,
  store_int64_store_int,
  store_uint64_store_uint,
  store_int64_store_uint,
  store_uint64_store_int,
  store_bytes_noninit_align,
  undef_store_ptr_undef_store_uint64,
  undef_store_ptr_undef_store_int64,
  undef_store_ptr_align,
  store_ptr_align,
  store_ptr_store_uint64
] => 7317451647991912470

-- Big-endian byte order, modulo behavior, and vector recursion boundaries.
example : StoreLibSig.bytes_eqm BigEndian 0 #v[] #v[] := trivial
example : StoreLibSig.bytes_eqm BigEndian 2 #v[-1, 256] #v[255, 0] := by
  exact ⟨⟨-1, by decide⟩, ⟨⟨1, by decide⟩, trivial⟩⟩
example : StoreLibSig.n_bytes_to_Z BigEndian 0 #v[] = 0 := rfl
example : StoreLibSig.n_bytes_to_Z BigEndian 2 #v[1, 2] = 258 := by native_decide
example : StoreLibSig.n_bytes_to_Z LittleEndian 2 #v[1, 2] = 513 := by native_decide
example : StoreLibSig.n_bytes_to_Z BigEndian 2 #v[-1, -1] = 65535 := by native_decide
example : StoreLibSig.Z_to_n_bytes BigEndian 258 2 = #v[1, 2] := by native_decide
example : StoreLibSig.Z_to_n_bytes BigEndian (-1) 2 = #v[255, 255] := by native_decide
example :
    StoreLibSig.Z_to_n_bytes BigEndian 0x0102030405060708090A0B0C0D0E0F10 16 =
      #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := by
  native_decide
example : StoreLibSig.merge_n_bytes BigEndian 2 #v[1, 2] 258 := by
  change BigEndian.merge_n_bytes 2 #v[1, 2] 258
  unfold BigEndian.merge_n_bytes BigEndian.n_bytes_to_Z Z.modulo Z.pow
  decide
example : StoreLibSig.merge_n_bytes BigEndian 2 #v[255, 255] (-1) := by
  change BigEndian.merge_n_bytes 2 #v[255, 255] (-1)
  unfold BigEndian.merge_n_bytes BigEndian.n_bytes_to_Z Z.modulo Z.pow
  decide

-- The generic stores preserve the source zero/successor shapes.
example (x : Int) : store_n_bytes Arch32 BigEndian SL x 0 #v[] = SL.emp := rfl
example (x b1 b2 : Int) :
    store_n_bytes Arch64 LittleEndian SL x 2 #v[b1, b2] =
      SL.sepcon (SL.mstore x b1)
        (SL.sepcon (SL.mstore (x + 1) b2) SL.emp) := rfl
example (x : Int) :
    store_n_bytes_noninit Arch32 BigEndian SL x 2 #v[17, 34] =
      SL.sepcon (SL.mstore_noninit x)
        (SL.sepcon (SL.mstore_noninit (x + 1)) SL.emp) := rfl
example (x v : Int) :
    store_n_bytes_Z Arch32 BigEndian SL x 1 v =
      SL.exp (Vector Int 1) (fun bytes =>
        SL.andp (SL.coq_prop (StoreLibSig.merge_n_bytes BigEndian 1 bytes v))
          (store_n_bytes Arch32 BigEndian SL x 1 bytes)) := rfl
example (x v : Int) :
    store_n_bytes_Z Arch64 LittleEndian SL x 8 v =
      SL.exp (Vector Int 8) (fun bytes =>
        SL.andp (SL.coq_prop (StoreLibSig.merge_n_bytes LittleEndian 8 bytes v))
          (store_n_bytes Arch64 LittleEndian SL x 8 bytes)) := rfl

-- All four architecture/endian combinations elaborate through the canonical
-- generic byte-store equivalence.
example (x v : Int) :
    SL.logic_equiv (DerivedPredSig.store_8byte BigEndian SL x v)
      (store_n_bytes_Z Arch32 BigEndian SL x 8 v) :=
  store_8byte_equiv_store_n_bytes_Z Arch32 BigEndian SL x v

example (x v : Int) :
    SL.logic_equiv (DerivedPredSig.store_8byte LittleEndian SL x v)
      (store_n_bytes_Z Arch32 LittleEndian SL x 8 v) :=
  store_8byte_equiv_store_n_bytes_Z Arch32 LittleEndian SL x v

example (x v : Int) :
    SL.logic_equiv (DerivedPredSig.store_8byte BigEndian SL x v)
      (store_n_bytes_Z Arch64 BigEndian SL x 8 v) :=
  store_8byte_equiv_store_n_bytes_Z Arch64 BigEndian SL x v

example (x v : Int) :
    SL.logic_equiv (DerivedPredSig.store_8byte LittleEndian SL x v)
      (store_n_bytes_Z Arch64 LittleEndian SL x 8 v) :=
  store_8byte_equiv_store_n_bytes_Z Arch64 LittleEndian SL x v

example : BigEndian.merge_int64 1 2 3 4 5 6 7 8 72623859790382856 := by
  unfold BigEndian.merge_int64 Z.modulo Z.pow
  decide

example : LittleEndian.merge_int64 1 2 3 4 5 6 7 8 578437695752307201 := by
  unfold LittleEndian.merge_int64 Z.modulo Z.pow
  decide

-- Independent word-decomposition checks pin the byte order used by the new
-- P0-6 relation instead of proving it through the relation's own theorems.
example :
    merge_int64_by_ints BigEndian 16909060 84281096 72623859790382856 := by
  refine ⟨1, 2, 3, 4, 5, 6, 7, 8, ?_⟩
  change BigEndian.merge_int 1 2 3 4 16909060 ∧
    BigEndian.merge_int 5 6 7 8 84281096 ∧
      BigEndian.merge_int64 1 2 3 4 5 6 7 8 72623859790382856
  unfold BigEndian.merge_int BigEndian.merge_int64 Z.modulo Z.pow
  decide

example :
    merge_int64_by_ints LittleEndian 67305985 134678021 578437695752307201 := by
  refine ⟨1, 2, 3, 4, 5, 6, 7, 8, ?_⟩
  change LittleEndian.merge_int 1 2 3 4 67305985 ∧
    LittleEndian.merge_int 5 6 7 8 134678021 ∧
      LittleEndian.merge_int64 1 2 3 4 5 6 7 8 578437695752307201
  unfold LittleEndian.merge_int LittleEndian.merge_int64 Z.modulo Z.pow
  decide

-- Pointer weakening and alignment select the 4-byte or 8-byte source branch,
-- independently of byte order.
example (x v : Int) :
    SL.derivable1 (DerivedPredSig.store_ptr Arch32 BigEndian SL x v)
      (DerivedPredSig.store_uint Arch32 BigEndian SL x v) :=
  store_ptr_store_uint (Arch := Arch32) (Endian := BigEndian) SL x v rfl rfl

example (x v : Int) :
    SL.derivable1 (DerivedPredSig.store_ptr Arch32 LittleEndian SL x v)
      (DerivedPredSig.store_uint Arch32 LittleEndian SL x v) :=
  store_ptr_store_uint (Arch := Arch32) (Endian := LittleEndian) SL x v rfl rfl

example (x v : Int) :
    SL.derivable1 (DerivedPredSig.store_ptr Arch64 BigEndian SL x v)
      (DerivedPredSig.store_uint64 Arch64 BigEndian SL x v) :=
  store_ptr_store_uint64 (Arch := Arch64) (Endian := BigEndian) SL x v rfl rfl

example (x v : Int) :
    SL.derivable1 (DerivedPredSig.store_ptr Arch64 LittleEndian SL x v)
      (DerivedPredSig.store_uint64 Arch64 LittleEndian SL x v) :=
  store_ptr_store_uint64 (Arch := Arch64) (Endian := LittleEndian) SL x v rfl rfl

example (x : Int) :
    SL.derivable1 (DerivedPredSig.undef_store_ptr Arch32 SL x)
      (DerivedPredSig.store_align_n Arch32 SL Arch32.ptr_size_Z) :=
  undef_store_ptr_align (Arch := Arch32) SL x

example (x : Int) :
    SL.derivable1 (DerivedPredSig.undef_store_ptr Arch64 SL x)
      (DerivedPredSig.store_align_n Arch64 SL Arch64.ptr_size_Z) :=
  undef_store_ptr_align (Arch := Arch64) SL x

example (x v : Int) :=
  store_int64_store_char (Arch := Arch32) (Endian := BigEndian) SL x v

example (x v : Int) :=
  store_uint64_store_uchar (Arch := Arch32) (Endian := LittleEndian) SL x v

example (x v : Int) :=
  store_int64_store_uchar (Arch := Arch64) (Endian := BigEndian) SL x v

example (x v : Int) :=
  store_uint64_store_char (Arch := Arch64) (Endian := LittleEndian) SL x v

-- Concrete source theorem behavior over the migrated memory model.
example (x : Int) :
    store_byte_noninit SL x ** store_byte_noninit SL x |-- “ False ” :=
  dup_store_byte_noninit SL x

-- The recursive 16-byte store exposes the same first byte on both sides, so
-- the ordinary separation-algebra conflict pipeline must reject the overlap.
example (x : Int) :
    store_16byte_noninit SL x ** store_16byte_noninit SL x |-- “ False ” := by
  unfold store_16byte_noninit store_bytes_noninit
  normalize
  sep_apply dup_store_byte_noninit SL x
  entailer!

example (x v : Int) : store_ptr SL x v |-- store_uint SL x v :=
  store_ptr_store_uint (Arch := Arch32) (Endian := BigEndian) SL x v rfl rfl

example (x : Int) : undef_store_short SL x |-- store_align_n SL 2 :=
  undef_store_short_align SL x

example (n m : Int) :
    store_align_n SL n ** store_align_n SL m |-- store_align_n SL (n + m) :=
  store_align_merge SL n m

-- Every relative offset at which two four-byte stores overlap is rejected.
private theorem store_4byte_overlap_false (CRules : SeparationLogicSig)
    (x d : Int) (hlo : -3 <= d) (hhi : d <= 3) :
    CRules.derivable1
      (CRules.sepcon (store_4byte_noninit CRules x)
        (store_4byte_noninit CRules (x + d)))
      (CRules.coq_prop False) := by
  intro state hstore
  have hdisjoint := store_4byte_valid CRules x (x + d) state hstore
  change x + 3 < x + d ∨ x + d + 3 < x at hdisjoint
  omega

example (x : Int) :
    store_4byte_noninit SL x ** store_4byte_noninit SL (x + (-3)) |-- “ False ” :=
  store_4byte_overlap_false SL x (-3) (by omega) (by omega)

example (x : Int) :
    store_4byte_noninit SL x ** store_4byte_noninit SL (x + (-2)) |-- “ False ” :=
  store_4byte_overlap_false SL x (-2) (by omega) (by omega)

example (x : Int) :
    store_4byte_noninit SL x ** store_4byte_noninit SL (x + (-1)) |-- “ False ” :=
  store_4byte_overlap_false SL x (-1) (by omega) (by omega)

example (x : Int) :
    store_4byte_noninit SL x ** store_4byte_noninit SL (x + 0) |-- “ False ” :=
  store_4byte_overlap_false SL x 0 (by omega) (by omega)

example (x : Int) :
    store_4byte_noninit SL x ** store_4byte_noninit SL (x + 1) |-- “ False ” :=
  store_4byte_overlap_false SL x 1 (by omega) (by omega)

example (x : Int) :
    store_4byte_noninit SL x ** store_4byte_noninit SL (x + 2) |-- “ False ” :=
  store_4byte_overlap_false SL x 2 (by omega) (by omega)

example (x : Int) :
    store_4byte_noninit SL x ** store_4byte_noninit SL (x + 3) |-- “ False ” :=
  store_4byte_overlap_false SL x 3 (by omega) (by omega)

-- Signed/unsigned casts wrap at each supported storage width.
example (x : Int) : store_char SL x (-1) |-- store_uchar SL x 255 := by
  simpa [SimpleC.SL.IntLib.unsigned_last_nbits, Z.pow, Z.modulo] using
    store_char_cast SL x (-1)

example (x : Int) : store_uchar SL x 255 |-- store_char SL x (-1) := by
  simpa [SimpleC.SL.IntLib.signed_last_nbits,
    SimpleC.SL.IntLib.unsigned_last_nbits, Z.pow, Z.modulo] using
    store_uchar_cast SL x 255

example (x : Int) : store_short SL x (-1) |-- store_ushort SL x 65535 := by
  simpa [SimpleC.SL.IntLib.unsigned_last_nbits, Z.pow, Z.modulo] using
    store_short_cast SL x (-1)

example (x : Int) : store_ushort SL x 65535 |-- store_short SL x (-1) := by
  simpa [SimpleC.SL.IntLib.signed_last_nbits,
    SimpleC.SL.IntLib.unsigned_last_nbits, Z.pow, Z.modulo] using
    store_ushort_cast SL x 65535

example (x : Int) : store_int SL x (-1) |-- store_uint SL x 4294967295 := by
  simpa [SimpleC.SL.IntLib.unsigned_last_nbits, Z.pow, Z.modulo] using
    store_int_cast SL x (-1)

example (x : Int) : store_uint SL x 4294967295 |-- store_int SL x (-1) := by
  simpa [SimpleC.SL.IntLib.signed_last_nbits,
    SimpleC.SL.IntLib.unsigned_last_nbits, Z.pow, Z.modulo] using
    store_uint_cast SL x 4294967295

example (x : Int) :
    store_int64 SL x (-1) |-- store_uint64 SL x 18446744073709551615 := by
  simpa [SimpleC.SL.IntLib.unsigned_last_nbits, Z.pow, Z.modulo] using
    store_int64_cast SL x (-1)

example (x : Int) :
    store_uint64 SL x 18446744073709551615 |-- store_int64 SL x (-1) := by
  simpa [SimpleC.SL.IntLib.signed_last_nbits,
    SimpleC.SL.IntLib.unsigned_last_nbits, Z.pow, Z.modulo] using
    store_uint64_cast SL x 18446744073709551615

-- The Int128 branches exercise the real 16-byte weakening path.
example (x value : Int) :
    poly_store SL FET_int128 x value |-- poly_undef_store SL FET_int128 x :=
  poly_store_poly_undef_store SL x FET_int128 value

example (x value : Int) :
    poly_store SL FET_uint128 x value |-- poly_undef_store SL FET_uint128 x :=
  poly_store_poly_undef_store SL x FET_uint128 value

example (x value : Int) :
    poly_store SL FET_int128 x value |-- poly_undef_store SL FET_int128 x := by
  poly_store_unfold
  exact store_int128_undef_store_int128 SL x value

example (x value : Int) :
    store_int128 SL x value |--
      SL.coq_prop (SimpleC.SL.IntLib.Int128.min_signed <= value ∧
        value <= SimpleC.SL.IntLib.Int128.max_signed) :=
  store_int128_range SL x value

example (x value : Int) :
    store_uint128 SL x value |--
      SL.coq_prop (0 <= value ∧ value <= SimpleC.SL.IntLib.Int128.max_unsigned) :=
  store_uint128_range SL x value

example (x value : Int) :
    store_int128 SL x value |-- store_align_n SL 16 :=
  store_int128_align SL x value

example (x : Int) :
    undef_store_uint128 SL x |-- store_align_n SL 16 :=
  undef_store_uint128_align SL x

example (x value : Int) :
    poly_store SL FET_float x value |-- poly_undef_store SL FET_float x :=
  poly_store_poly_undef_store SL x FET_float value

example (x value : Int) :
    poly_store SL FET_double x value |-- poly_undef_store SL FET_double x :=
  poly_store_poly_undef_store SL x FET_double value

example (x value : Int) :
    poly_store SL FET_long_double x value |-- poly_undef_store SL FET_long_double x :=
  poly_store_poly_undef_store SL x FET_long_double value

-- The dependent family carries actual floating values, while the untyped
-- family above carries source bit patterns.
example (x : Int) (value : fp32) :
    typed_poly_store SL FET_float x value |-- poly_undef_store SL FET_float x :=
  typed_poly_store_poly_undef_store SL x FET_float value

example (x : Int) (value : fp64) :
    typed_poly_store SL FET_double x value |-- poly_undef_store SL FET_double x := by
  poly_store_unfold
  exact store_double_undef_store_double SL x value

example (x : Int) (value : fp128) :
    typed_poly_store SL FET_long_double x value |--
      poly_undef_store SL FET_long_double x :=
  typed_poly_store_poly_undef_store SL x FET_long_double value

example (x : Int) (value : fp32) :
    DerivedPredSigCompat.store_finite_float SL x value |--
      DerivedPredSigCompat.undef_store_finite_float SL x := by
  unfold DerivedPredSigCompat.store_finite_float
    DerivedPredSigCompat.undef_store_finite_float
  apply coq_prop_andp_left
  intro _
  exact store_float_undef_store_float SL x value

example (x : Int) (value : fp64) :
    store_finite_double SL x value |--
      SL.coq_prop (fp64_isFinite value ∧ isvalidptr_double x) :=
  valid_store_finite_double SL x value

example (x : Int) (value : fp32) :
    store_float SL x value |-- store_align4_n SL 1 :=
  store_float_align4 SL x value

example (x : Int) (value : fp64) :
    store_double SL x value |-- store_align_n SL 8 :=
  store_double_align SL x value

example (x : Int) (value : fp128) :
    store_finite_long_double SL x value |-- store_align_n SL 16 :=
  store_finite_long_double_align SL x value

-- Alignment resources append at the Int length and convert four-byte units.
example : store_align4_n SL 2 ** store_align4_n SL 3 |-- store_align4_n SL 5 := by
  simpa using store_align4_merge SL 2 3

example : store_align_n SL 2 ** store_align_n SL 3 |-- store_align_n SL 5 := by
  simpa using store_align_merge SL 2 3

example : store_align4_n SL 3 |-- store_align_n SL 12 := by
  simpa using store_align4_to_store_align SL 3

-- StoreAux source call shape: pure introduction, two spatial applications, merge.
example (x : Int) :
    DerivedPredSigCompat.undef_store_short SacContext.rules x |--
      store_align_n SacContext.rules 2 := by
  unfold DerivedPredSigCompat.undef_store_short DerivedPredSig.undef_store_short
    DerivedPredSig.store_2byte_noninit
  Intros
  have hbyte0 : store_byte_noninit SacContext.rules x |--
      store_align_n SacContext.rules 1 := store_byte_align1 SacContext.rules x (by
    have hshort : DerivedPredSig.isvalidptr_short
        SimpleC.SL.CArch.Arch32 x := by assumption
    unfold DerivedPredSig.isvalidptr_short at hshort
    have hbound : x + 1 <= Int.max_unsigned := by
      change x + 1 <= SimpleC.SL.CArch.Arch32.addr_max_unsigned
      exact hshort.2.1
    unfold DerivedPredSig.isvalidptr_char
    omega)
  sep_apply hbyte0
  have hbyte1 : store_byte_noninit SacContext.rules (x + 1) |--
      store_align_n SacContext.rules 1 := store_byte_align1 SacContext.rules (x + 1) (by
    have hshort : DerivedPredSig.isvalidptr_short
        SimpleC.SL.CArch.Arch32 x := by assumption
    unfold DerivedPredSig.isvalidptr_short at hshort
    have hbound : x + 1 <= Int.max_unsigned := by
      change x + 1 <= SimpleC.SL.CArch.Arch32.addr_max_unsigned
      exact hshort.2.1
    unfold DerivedPredSig.isvalidptr_char
    omega)
  sep_apply hbyte1
  have hmerge : store_align_n SacContext.rules 1 ** store_align_n SacContext.rules 1 |--
      store_align_n SacContext.rules 2 := by
    simpa using store_align_merge SacContext.rules 1 1
  sep_apply hmerge
  entailer!

-- StoreAux source call shape: derive pure disjointness facts without consuming space.
example (x a : Int) (l : List Int) :
    DerivedPredSigCompat.store_align4_list SacContext.rules (a :: l) **
      store_4byte_noninit SacContext.rules x |--
      “ Forall (fun x' => x + 3 < x' ∨ x' + 3 < x) (a :: l) ” := by
  simp only [DerivedPredSig.store_align4_list]
  Intros
  have hhead : store_4byte_noninit SacContext.rules a **
      store_4byte_noninit SacContext.rules x |--
      “ a + 3 < x ∨ x + 3 < a ” := store_4byte_valid SacContext.rules a x
  prop_apply hhead
  Intros
  have htail : DerivedPredSigCompat.store_align4_list SacContext.rules l **
      store_4byte_noninit SacContext.rules x |--
      “ Forall (fun x' => x + 3 < x' ∨ x' + 3 < x) l ” :=
    store_align4_valid SacContext.rules x l
  prop_apply htail
  Intros
  entailer! <;> constructor <;> simp_all <;> omega

#print axioms StoreLibSig.Z_to_n_bytes_to_Z
#print axioms store_4byte_equiv_store_n_bytes_Z
#print axioms store_16byte_store_16byte_noinit
#print axioms store_int128_undef_store_int128
#print axioms store_int128_align
#print axioms store_float_undef_store_float
#print axioms typed_poly_store_poly_undef_store
#print axioms store_finite_long_double_align
#print axioms store_int64_store_char
#print axioms store_int64_store_int
#print axioms undef_store_ptr_align
#print axioms store_ptr_store_uint64
#print axioms store_align_merge
#print axioms store_align4_to_store_align

end StoreAuxTests
