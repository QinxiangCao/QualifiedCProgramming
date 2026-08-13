import SimpleC.SL.StoreAux
import SimpleC.SL.Assertion
import Lean.Util.CollectAxioms

namespace StoreAuxTests

open AUXLib
open CompCert
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
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
#check vector_cons
#check vector_head
#check vector_tail
#check vector_head_cons
#check vector_tail_cons
#check vector_cons_eta
#check bytes_eqm
#check n_bytes_to_Z
#check Z_to_n_bytes
#check merge_n_bytes
#check store_n_bytes
#check store_n_bytes_Z
#check store_n_bytes_noninit

-- All 13 generic source theorems.
#check store_byte_eqm
#check eqm_iff_mod_eq
#check n_bytes_to_Z_cons
#check eqm_bytes_to_Z_eq
#check Z_to_n_bytes_succ
#check Z_to_n_bytes_to_Z
#check merge_short_equiv_merge_n_bytes
#check merge_int_equiv_merge_n_bytes
#check merge_int64_equiv_merge_n_bytes
#check store_byte_equiv_store_n_bytes_Z
#check store_2byte_equiv_store_n_bytes_Z
#check store_4byte_equiv_store_n_bytes_Z
#check store_8byte_equiv_store_n_bytes_Z

-- All 49 relation/range/duplication/cast/decomposition source theorems.
#check store_byte_store_byte_noinit
#check store_2byte_store_2byte_noinit
#check store_4byte_store_4byte_noinit
#check store_8byte_store_8byte_noinit
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
#check poly_store_poly_undef_store
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

-- This list freezes names, complete types, binder order, and binder visibility.
-- It also rejects axioms outside the three expected Lean foundations.
#check_api_contract [
  StoreLibSig,
  StoreLibSig.canonical,
  vector_cons,
  vector_head,
  vector_tail,
  vector_head_cons,
  vector_tail_cons,
  vector_cons_eta,
  bytes_eqm,
  n_bytes_to_Z,
  Z_to_n_bytes,
  merge_n_bytes,
  store_n_bytes,
  store_n_bytes_Z,
  store_n_bytes_noninit,
  store_byte_eqm,
  eqm_iff_mod_eq,
  n_bytes_to_Z_cons,
  eqm_bytes_to_Z_eq,
  Z_to_n_bytes_succ,
  Z_to_n_bytes_to_Z,
  merge_short_equiv_merge_n_bytes,
  merge_int_equiv_merge_n_bytes,
  merge_int64_equiv_merge_n_bytes,
  store_byte_equiv_store_n_bytes_Z,
  store_2byte_equiv_store_n_bytes_Z,
  store_4byte_equiv_store_n_bytes_Z,
  store_8byte_equiv_store_n_bytes_Z,
  store_byte_store_byte_noinit,
  store_2byte_store_2byte_noinit,
  store_4byte_store_4byte_noinit,
  store_8byte_store_8byte_noinit,
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
  poly_store_poly_undef_store,
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
  store_ptr_store_uint
] => 11384383046875235412

-- Big-endian byte order, modulo behavior, and vector recursion boundaries.
example : bytes_eqm 0 #v[] #v[] := trivial
example : bytes_eqm 2 #v[-1, 256] #v[255, 0] := by
  exact ⟨⟨-1, by decide⟩, ⟨⟨1, by decide⟩, trivial⟩⟩
example : n_bytes_to_Z 0 #v[] = 0 := rfl
example : n_bytes_to_Z 2 #v[1, 2] = 258 := by native_decide
example : n_bytes_to_Z 2 #v[-1, -1] = 65535 := by native_decide
example : Z_to_n_bytes 258 2 = #v[1, 2] := by native_decide
example : Z_to_n_bytes (-1) 2 = #v[255, 255] := by native_decide
example : merge_n_bytes 2 #v[1, 2] 258 := by
  unfold merge_n_bytes n_bytes_to_Z Z.modulo Z.pow
  decide
example : merge_n_bytes 2 #v[255, 255] (-1) := by
  unfold merge_n_bytes n_bytes_to_Z Z.modulo Z.pow
  decide

-- The generic stores preserve the source zero/successor shapes.
example (x : Int) : store_n_bytes SL x 0 #v[] = SL.emp := rfl
example (x v : Int) :
    store_n_bytes_Z SL x 1 v =
      SL.exp (Vector Int 1) (fun bytes =>
        SL.andp (SL.coq_prop (merge_n_bytes 1 bytes v))
          (store_n_bytes SL x 1 bytes)) := rfl

-- Concrete source theorem behavior over the migrated memory model.
example (x : Int) :
    store_byte_noninit SL x ** store_byte_noninit SL x |-- “ False ” :=
  dup_store_byte_noninit SL x

example (x v : Int) : store_ptr SL x v |-- store_uint SL x v :=
  store_ptr_store_uint SL x v

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

-- Alignment resources append at the Int length and convert four-byte units.
example : store_align4_n SL 2 ** store_align4_n SL 3 |-- store_align4_n SL 5 := by
  simpa using store_align4_merge SL 2 3

example : store_align_n SL 2 ** store_align_n SL 3 |-- store_align_n SL 5 := by
  simpa using store_align_merge SL 2 3

example : store_align4_n SL 3 |-- store_align_n SL 12 := by
  simpa using store_align4_to_store_align SL 3

-- StoreAux source call shape: pure introduction, two spatial applications, merge.
example (x : Int) :
    undef_store_short SacContext.rules x |-- store_align_n SacContext.rules 2 := by
  unfold undef_store_short store_2byte_noninit
  Intros
  have hbyte0 : store_byte_noninit SacContext.rules x |--
      store_align_n SacContext.rules 1 := store_byte_align1 SacContext.rules x (by
    unfold isvalidptr_short at *
    unfold isvalidptr_char
    omega)
  sep_apply hbyte0
  have hbyte1 : store_byte_noninit SacContext.rules (x + 1) |--
      store_align_n SacContext.rules 1 := store_byte_align1 SacContext.rules (x + 1) (by
    unfold isvalidptr_short at *
    unfold isvalidptr_char
    omega)
  sep_apply hbyte1
  have hmerge : store_align_n SacContext.rules 1 ** store_align_n SacContext.rules 1 |--
      store_align_n SacContext.rules 2 := by
    simpa using store_align_merge SacContext.rules 1 1
  sep_apply hmerge
  entailer!

-- StoreAux source call shape: derive pure disjointness facts without consuming space.
set_option maxHeartbeats 1000000 in
example (x a : Int) (l : List Int) :
    store_align4_list SacContext.rules (a :: l) **
      store_4byte_noninit SacContext.rules x |--
      “ Forall (fun x' => x + 3 < x' ∨ x' + 3 < x) (a :: l) ” := by
  simp only [store_align4_list]
  Intros
  have hhead : store_4byte_noninit SacContext.rules a **
      store_4byte_noninit SacContext.rules x |--
      “ a + 3 < x ∨ x + 3 < a ” := store_4byte_valid SacContext.rules a x
  prop_apply hhead
  Intros
  have htail : store_align4_list SacContext.rules l **
      store_4byte_noninit SacContext.rules x |--
      “ Forall (fun x' => x + 3 < x' ∨ x' + 3 < x) l ” :=
    store_align4_valid SacContext.rules x l
  prop_apply htail
  Intros
  entailer! <;> constructor <;> simp_all <;> omega

#print axioms Z_to_n_bytes_to_Z
#print axioms store_4byte_equiv_store_n_bytes_Z
#print axioms store_align_merge
#print axioms store_align4_to_store_align

end StoreAuxTests
