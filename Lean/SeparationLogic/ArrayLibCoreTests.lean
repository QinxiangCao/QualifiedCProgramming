import SimpleC.SL.ArrayLibCore

namespace ArrayLibCoreTests

open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion
open SimpleC.SL.StoreAux
open SimpleC.SL.ArrayLibCore
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig

open Lean Elab Command

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env <- getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "ArrayLib core API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkArrayLibCoreContract)
  "#check_array_lib_core_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_array_lib_core_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "ArrayLib core API type hash changed: expected {expected}, got {actual}"
      logInfo m!"ArrayLib core API contract verified for {names.size} declarations"

-- This manifest freezes every public declaration checked below, including full
-- types, binder order and argument visibility.
#check_array_lib_core_contract [
  ArrayLibCoreSig,
  ArrayLibCoreSig.canonical,
  ELEMENT_STORE,
  ArrayLib.mixedstoreA,
  ArrayLib.seg,
  ArrayLib.missing_i,
  ArrayLib.full,
  ArrayLib.undef_seg,
  ArrayLib.undef_missing_i,
  ArrayLib.undef_full,
  ArrayLib.seg_shape,
  ArrayLib.missing_i_shape,
  ArrayLib.full_shape,
  ArrayLib.mixed_seg,
  ArrayLib.mixed_missing_i,
  ArrayLib.mixed_full,
  store_array_rec_length,
  store_array_rec_Zlength,
  store_array_rec_nil,
  store_array_rec_valid,
  store_array_length,
  store_array_Zlength,
  store_array_valid,
  store_array_missing_i_rec_length,
  store_array_missing_i_rec_Zlength,
  store_array_missing_i_rec_valid,
  store_array_missing_i_valid,
  store_array_rec_split_to_missing_i,
  store_array_split_to_missing_i,
  store_array_missing_i_merge_to_rec,
  store_array_missing_i_merge_to_array,
  ArrayLib.mixedstoreA_to_undefstoreA,
  ArrayLib.mixedstoreA_shift,
  ArrayLib.seg_length,
  ArrayLib.seg_Zlength,
  ArrayLib.seg_nil,
  ArrayLib.seg_single,
  ArrayLib.mixed_seg_single,
  ArrayLib.undef_seg_single,
  ArrayLib.seg_shape_single,
  ArrayLib.full_length,
  ArrayLib.full_Zlength,
  ArrayLib.mixed_seg_length,
  ArrayLib.mixed_seg_Zlength,
  ArrayLib.mixed_seg_nil,
  ArrayLib.mixed_full_length,
  ArrayLib.mixed_full_Zlength,
  ArrayLib.mixed_missing_i_length,
  ArrayLib.mixed_missing_i_Zlength,
  ArrayLib.missing_i_length,
  ArrayLib.missing_i_Zlength,
  ArrayLib.seg_valid,
  ArrayLib.mixed_seg_valid,
  ArrayLib.undef_seg_valid,
  ArrayLib.seg_shape_valid,
  ArrayLib.seg_empty,
  ArrayLib.mixed_seg_empty,
  ArrayLib.undef_seg_empty,
  ArrayLib.seg_shape_empty,
  ArrayLib.seg_unfold,
  ArrayLib.mixed_seg_unfold,
  ArrayLib.undef_seg_unfold,
  ArrayLib.seg_shape_unfold,
  ArrayLib.missing_i_empty,
  ArrayLib.mixed_missing_i_empty,
  ArrayLib.undef_missing_i_empty,
  ArrayLib.missing_i_shape_empty,
  ArrayLib.missing_i_unfold,
  ArrayLib.mixed_missing_i_unfold,
  ArrayLib.undef_missing_i_unfold,
  ArrayLib.missing_i_shape_unfold,
  ArrayLib.full_empty,
  ArrayLib.mixed_full_empty,
  ArrayLib.undef_full_empty,
  ArrayLib.full_shape_empty,
  ArrayLib.full_unfold,
  ArrayLib.mixed_full_unfold,
  ArrayLib.undef_full_unfold,
  ArrayLib.full_shape_unfold,
  ArrayLib.full_to_seg,
  ArrayLib.undef_full_to_undef_seg,
  ArrayLib.full_shape_to_seg_shape,
  ArrayLib.mixed_full_to_mixed_seg,
  ArrayLib.seg_to_mixed_seg,
  ArrayLib.full_to_mixed_seg,
  ArrayLib.mixed_seg_to_seg,
  ArrayLib.missing_i_to_mixed_missing_i,
  ArrayLib.mixed_missing_i_to_missing_i,
  ArrayLib.undef_seg_to_mixed_seg,
  ArrayLib.undef_full_to_mixed_seg,
  ArrayLib.seg_shift,
  ArrayLib.mixed_seg_shift,
  ArrayLib.seg_0_shift,
  ArrayLib.mixed_seg_0_shift,
  ArrayLib.undef_seg_shift,
  ArrayLib.undef_seg_0_shift,
  ArrayLib.seg_shape_shift,
  ArrayLib.seg_shape_0_shift,
  ArrayLib.seg_to_full,
  ArrayLib.mixed_seg_to_mixed_full,
  ArrayLib.mixed_full_to_full,
  ArrayLib.full_to_mixed_full,
  ArrayLib.undef_full_to_mixed_full,
  ArrayLib.seg_to_undef_seg,
  ArrayLib.mixed_seg_to_undef_seg,
  ArrayLib.seg_to_seg_shape,
  ArrayLib.undef_seg_to_undef_full,
  ArrayLib.seg_shape_to_full_shape,
  ArrayLib.missing_i_to_seg_head,
  ArrayLib.mixed_missing_i_to_mixed_seg_head,
  ArrayLib.undef_missing_i_to_undef_seg_head,
  ArrayLib.missing_i_shape_to_seg_shape_head,
  ArrayLib.missing_i_to_seg_tail,
  ArrayLib.mixed_missing_i_to_mixed_seg_tail,
  ArrayLib.undef_missing_i_to_undef_seg_tail,
  ArrayLib.missing_i_shape_to_seg_shape_tail,
  ArrayLib.missing_i_to_undef_missing_i,
  ArrayLib.mixed_missing_i_to_undef_missing_i,
  ArrayLib.undef_missing_i_to_mixed_missing_i,
  ArrayLib.missing_i_to_missing_i_shape,
  ArrayLib.full_to_undef_full,
  ArrayLib.mixed_seg_to_undef_full,
  ArrayLib.mixed_full_to_undef_seg,
  ArrayLib.mixed_full_to_undef_full,
  ArrayLib.full_to_full_shape,
  ArrayLibCoreSig.repeat_Z,
  ArrayLibCoreSig.repeat_Z_tail,
  ArrayLibCoreSig.SingleSome,
  ArrayLib.seg_shape_to_undef_seg,
  ArrayLib.full_shape_to_undef_full,
  ArrayLib.undef_seg_to_align,
  ArrayLib.seg_to_align,
  ArrayLib.mixed_seg_to_align,
  ArrayLib.seg_shape_to_align,
  ArrayLib.full_to_align,
  ArrayLib.mixed_full_to_align,
  ArrayLib.undef_full_to_align,
  ArrayLib.full_shape_to_align,
  ArrayLib.undef_full_valid,
  ArrayLib.full_shape_valid,
  ArrayLib.seg_length_range,
  ArrayLib.mixed_seg_length_range,
  ArrayLib.undef_seg_length_range,
  ArrayLib.seg_shape_length_range,
  ArrayLib.full_length_range,
  ArrayLib.mixed_full_length_range,
  ArrayLib.undef_full_length_range,
  ArrayLib.full_shape_length_range,
  ArrayLib.seg_split_to_missing_i,
  ArrayLib.full_split_to_missing_i,
  ArrayLib.mixed_seg_split_to_mixed_missing_i,
  ArrayLib.mixed_full_split_to_mixed_missing_i,
  ArrayLib.missing_i_merge_to_seg,
  ArrayLib.missing_i_merge_to_full,
  ArrayLib.mixed_missing_i_merge_to_mixed_seg,
  ArrayLib.mixed_missing_i_merge_to_mixed_full,
  ArrayLib.undef_seg_split_to_undef_missing_i,
  ArrayLib.undef_full_split_to_undef_missing_i,
  ArrayLib.undef_missing_i_merge_to_undef_seg,
  ArrayLib.undef_missing_i_merge_to_undef_full,
  ArrayLib.mixed_seg_split_to_undef_missing_i,
  ArrayLib.mixed_full_split_to_undef_missing_i,
  ArrayLib.mixed_missing_i_merge_to_undef_seg,
  ArrayLib.mixed_missing_i_merge_to_undef_full,
  ArrayLib.seg_shape_split_to_missing_i_shape,
  ArrayLib.full_shape_split_to_missing_i_shape,
  ArrayLib.missing_i_shape_merge_to_seg_shape,
  ArrayLib.missing_i_shape_merge_to_full_shape,
  ArrayLib.seg_split_to_seg,
  ArrayLib.mixed_seg_split_to_mixed_seg,
  ArrayLib.undef_seg_split_to_undef_seg,
  ArrayLib.seg_shape_split_to_seg_shape,
  ArrayLib.full_split_to_seg,
  ArrayLib.mixed_full_split_to_mixed_seg,
  ArrayLib.full_split_to_full,
  ArrayLib.mixed_full_split_to_mixed_full,
  ArrayLib.undef_full_split_to_undef_seg,
  ArrayLib.undef_full_split_to_undef_full,
  ArrayLib.full_shape_split_to_seg_shape,
  ArrayLib.full_shape_split_to_full_shape,
  ArrayLib.seg_merge_to_seg,
  ArrayLib.mixed_seg_merge_to_mixed_seg,
  ArrayLib.undef_seg_merge_to_undef_seg,
  ArrayLib.seg_shape_merge_to_seg_shape,
  ArrayLib.seg_merge_to_full,
  ArrayLib.mixed_seg_merge_to_mixed_full,
  ArrayLib.undef_seg_merge_to_undef_full,
  ArrayLib.seg_shape_merge_to_full_shape,
  ArrayLib.full_merge_to_full,
  ArrayLib.mixed_full_merge_to_mixed_full,
  ArrayLib.undef_full_merge_to_undef_full,
  ArrayLib.full_shape_merge_to_full_shape
] => 6423304207039358198

#check ArrayLibCoreSig
#check ArrayLibCoreSig.canonical
#check ELEMENT_STORE
#check ArrayLib.mixedstoreA
#check ArrayLib.seg
#check ArrayLib.missing_i
#check ArrayLib.full
#check ArrayLib.undef_seg
#check ArrayLib.undef_missing_i
#check ArrayLib.undef_full
#check ArrayLib.seg_shape
#check ArrayLib.missing_i_shape
#check ArrayLib.full_shape
#check ArrayLib.mixed_seg
#check ArrayLib.mixed_missing_i
#check ArrayLib.mixed_full
#check store_array_rec_length
#check store_array_rec_Zlength
#check store_array_rec_nil
#check store_array_rec_valid
#check store_array_length
#check store_array_Zlength
#check store_array_valid
#check store_array_missing_i_rec_length
#check store_array_missing_i_rec_Zlength
#check store_array_missing_i_rec_valid
#check store_array_missing_i_valid
#check store_array_rec_split_to_missing_i
#check store_array_split_to_missing_i
#check store_array_missing_i_merge_to_rec
#check store_array_missing_i_merge_to_array
#check ArrayLib.mixedstoreA_to_undefstoreA
#check ArrayLib.mixedstoreA_shift
#check ArrayLib.seg_length
#check ArrayLib.seg_Zlength
#check ArrayLib.seg_nil
#check ArrayLib.seg_single
#check ArrayLib.mixed_seg_single
#check ArrayLib.undef_seg_single
#check ArrayLib.seg_shape_single
#check ArrayLib.full_length
#check ArrayLib.full_Zlength
#check ArrayLib.mixed_seg_length
#check ArrayLib.mixed_seg_Zlength
#check ArrayLib.mixed_seg_nil
#check ArrayLib.mixed_full_length
#check ArrayLib.mixed_full_Zlength
#check ArrayLib.mixed_missing_i_length
#check ArrayLib.mixed_missing_i_Zlength
#check ArrayLib.missing_i_length
#check ArrayLib.missing_i_Zlength
#check ArrayLib.seg_valid
#check ArrayLib.mixed_seg_valid
#check ArrayLib.undef_seg_valid
#check ArrayLib.seg_shape_valid
#check ArrayLib.seg_empty
#check ArrayLib.mixed_seg_empty
#check ArrayLib.undef_seg_empty
#check ArrayLib.seg_shape_empty
#check ArrayLib.seg_unfold
#check ArrayLib.mixed_seg_unfold
#check ArrayLib.undef_seg_unfold
#check ArrayLib.seg_shape_unfold
#check ArrayLib.missing_i_empty
#check ArrayLib.mixed_missing_i_empty
#check ArrayLib.undef_missing_i_empty
#check ArrayLib.missing_i_shape_empty
#check ArrayLib.missing_i_unfold
#check ArrayLib.mixed_missing_i_unfold
#check ArrayLib.undef_missing_i_unfold
#check ArrayLib.missing_i_shape_unfold
#check ArrayLib.full_empty
#check ArrayLib.mixed_full_empty
#check ArrayLib.undef_full_empty
#check ArrayLib.full_shape_empty
#check ArrayLib.full_unfold
#check ArrayLib.mixed_full_unfold
#check ArrayLib.undef_full_unfold
#check ArrayLib.full_shape_unfold
#check ArrayLib.full_to_seg
#check ArrayLib.undef_full_to_undef_seg
#check ArrayLib.full_shape_to_seg_shape
#check ArrayLib.mixed_full_to_mixed_seg
#check ArrayLib.seg_to_mixed_seg
#check ArrayLib.full_to_mixed_seg
#check ArrayLib.mixed_seg_to_seg
#check ArrayLib.missing_i_to_mixed_missing_i
#check ArrayLib.mixed_missing_i_to_missing_i
#check ArrayLib.undef_seg_to_mixed_seg
#check ArrayLib.undef_full_to_mixed_seg
#check ArrayLib.seg_shift
#check ArrayLib.mixed_seg_shift
#check ArrayLib.seg_0_shift
#check ArrayLib.mixed_seg_0_shift
#check ArrayLib.undef_seg_shift
#check ArrayLib.undef_seg_0_shift
#check ArrayLib.seg_shape_shift
#check ArrayLib.seg_shape_0_shift
#check ArrayLib.seg_to_full
#check ArrayLib.mixed_seg_to_mixed_full
#check ArrayLib.mixed_full_to_full
#check ArrayLib.full_to_mixed_full
#check ArrayLib.undef_full_to_mixed_full
#check ArrayLib.seg_to_undef_seg
#check ArrayLib.mixed_seg_to_undef_seg
#check ArrayLib.seg_to_seg_shape
#check ArrayLib.undef_seg_to_undef_full
#check ArrayLib.seg_shape_to_full_shape
#check ArrayLib.missing_i_to_seg_head
#check ArrayLib.mixed_missing_i_to_mixed_seg_head
#check ArrayLib.undef_missing_i_to_undef_seg_head
#check ArrayLib.missing_i_shape_to_seg_shape_head
#check ArrayLib.missing_i_to_seg_tail
#check ArrayLib.mixed_missing_i_to_mixed_seg_tail
#check ArrayLib.undef_missing_i_to_undef_seg_tail
#check ArrayLib.missing_i_shape_to_seg_shape_tail
#check ArrayLib.missing_i_to_undef_missing_i
#check ArrayLib.mixed_missing_i_to_undef_missing_i
#check ArrayLib.undef_missing_i_to_mixed_missing_i
#check ArrayLib.missing_i_to_missing_i_shape
#check ArrayLib.full_to_undef_full
#check ArrayLib.mixed_seg_to_undef_full
#check ArrayLib.mixed_full_to_undef_seg
#check ArrayLib.mixed_full_to_undef_full
#check ArrayLib.full_to_full_shape
#check ArrayLibCoreSig.repeat_Z
#check ArrayLibCoreSig.repeat_Z_tail
#check ArrayLibCoreSig.SingleSome

example : ArrayLibCoreSig.repeat_Z (A := Int) 7 3 = [7, 7, 7] := rfl

example : ArrayLibCoreSig.repeat_Z (A := Int) 7 (-3) = [] := rfl

example :
    ArrayLibCoreSig.repeat_Z (A := Int) 7 (2 + 1) =
      ArrayLibCoreSig.repeat_Z (A := Int) 7 2 ++ [7] := by
  exact ArrayLibCoreSig.repeat_Z_tail 7 2 (by omega)

#check ArrayLib.seg_shape_to_undef_seg
#check ArrayLib.full_shape_to_undef_full
#check ArrayLib.undef_seg_to_align
#check ArrayLib.seg_to_align
#check ArrayLib.mixed_seg_to_align
#check ArrayLib.seg_shape_to_align
#check ArrayLib.full_to_align
#check ArrayLib.mixed_full_to_align
#check ArrayLib.undef_full_to_align
#check ArrayLib.full_shape_to_align
#check ArrayLib.undef_full_valid
#check ArrayLib.full_shape_valid
#check ArrayLib.seg_length_range
#check ArrayLib.mixed_seg_length_range
#check ArrayLib.undef_seg_length_range
#check ArrayLib.seg_shape_length_range
#check ArrayLib.full_length_range
#check ArrayLib.mixed_full_length_range
#check ArrayLib.undef_full_length_range
#check ArrayLib.full_shape_length_range
#check ArrayLib.seg_split_to_missing_i
#check ArrayLib.full_split_to_missing_i
#check ArrayLib.mixed_seg_split_to_mixed_missing_i
#check ArrayLib.mixed_full_split_to_mixed_missing_i
#check ArrayLib.missing_i_merge_to_seg
#check ArrayLib.missing_i_merge_to_full
#check ArrayLib.mixed_missing_i_merge_to_mixed_seg
#check ArrayLib.mixed_missing_i_merge_to_mixed_full
#check ArrayLib.undef_seg_split_to_undef_missing_i
#check ArrayLib.undef_full_split_to_undef_missing_i
#check ArrayLib.undef_missing_i_merge_to_undef_seg
#check ArrayLib.undef_missing_i_merge_to_undef_full
#check ArrayLib.mixed_seg_split_to_undef_missing_i
#check ArrayLib.mixed_full_split_to_undef_missing_i
#check ArrayLib.mixed_missing_i_merge_to_undef_seg
#check ArrayLib.mixed_missing_i_merge_to_undef_full
#check ArrayLib.seg_shape_split_to_missing_i_shape
#check ArrayLib.full_shape_split_to_missing_i_shape
#check ArrayLib.missing_i_shape_merge_to_seg_shape
#check ArrayLib.missing_i_shape_merge_to_full_shape
#check ArrayLib.seg_split_to_seg
#check ArrayLib.mixed_seg_split_to_mixed_seg
#check ArrayLib.undef_seg_split_to_undef_seg
#check ArrayLib.seg_shape_split_to_seg_shape
#check ArrayLib.full_split_to_seg
#check ArrayLib.mixed_full_split_to_mixed_seg
#check ArrayLib.full_split_to_full
#check ArrayLib.mixed_full_split_to_mixed_full
#check ArrayLib.undef_full_split_to_undef_seg
#check ArrayLib.undef_full_split_to_undef_full
#check ArrayLib.full_shape_split_to_seg_shape
#check ArrayLib.full_shape_split_to_full_shape
#check ArrayLib.seg_merge_to_seg
#check ArrayLib.mixed_seg_merge_to_mixed_seg
#check ArrayLib.undef_seg_merge_to_undef_seg
#check ArrayLib.seg_shape_merge_to_seg_shape
#check ArrayLib.seg_merge_to_full
#check ArrayLib.mixed_seg_merge_to_mixed_full
#check ArrayLib.undef_seg_merge_to_undef_full
#check ArrayLib.seg_shape_merge_to_full_shape
#check ArrayLib.full_merge_to_full
#check ArrayLib.mixed_full_merge_to_mixed_full
#check ArrayLib.undef_full_merge_to_undef_full
#check ArrayLib.full_shape_merge_to_full_shape

section

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSigCompat.Sig CRules}
variable {SLibSig : StoreLibSigCompat CRules DePredSig}
variable (ES : ELEMENT_STORE Arch32 BigEndian CRules DePredSig SLibSig)

open ArrayLib

local instance : SacContext where
  CRules := CRules

#check ArrayLib.full ES
#check ArrayLib.seg ES
#check ArrayLib.mixed_full ES

-- Every source `ArraySimplify` branch is exercised independently.
example (x lo hi : Int) :
    CRules.logic_equiv (seg ES x lo hi [])
      (CRules.andp (CRules.coq_prop (hi = lo)) CRules.emp) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x lo hi : Int) :
    CRules.logic_equiv (mixed_seg ES x lo hi [])
      (CRules.andp (CRules.coq_prop (hi = lo)) CRules.emp) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x lo : Int) : CRules.logic_equiv (undef_seg ES x lo lo) CRules.emp := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x lo : Int) : CRules.logic_equiv (seg_shape ES x lo lo) CRules.emp := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x lo hi : Int) (a : ES.A) (l : List ES.A) :
    CRules.logic_equiv (seg ES x lo hi (a :: l))
      (CRules.sepcon (ES.storeA x lo a) (seg ES x (lo + 1) hi l)) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x lo hi : Int) (a : Option ES.A) (l : List (Option ES.A)) :
    CRules.logic_equiv (mixed_seg ES x lo hi (a :: l))
      (CRules.sepcon (mixedstoreA ES x lo a)
        (mixed_seg ES x (lo + 1) hi l)) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x i lo hi : Int) :
    CRules.logic_equiv (missing_i ES x i lo hi []) (CRules.coq_prop False) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x i lo hi : Int) :
    CRules.logic_equiv (mixed_missing_i ES x i lo hi [])
      (CRules.coq_prop False) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x i lo : Int) :
    CRules.derivable1 (undef_missing_i ES x i lo lo) (CRules.coq_prop False) := by
  ArraySimplify
  exact CRules.toContext.derivable1_refl _

example (x i lo : Int) :
    CRules.logic_equiv (missing_i_shape ES x i lo lo) (CRules.coq_prop False) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x i lo hi : Int) (a : ES.A) (l : List ES.A) :
    CRules.logic_equiv (missing_i ES x i lo hi (a :: l))
      (CRules.orp
        (CRules.andp (CRules.coq_prop (i = lo)) (seg ES x (lo + 1) hi l))
        (CRules.andp (CRules.coq_prop (i > lo))
          (CRules.sepcon (ES.storeA x lo a)
            (missing_i ES x i (lo + 1) hi l)))) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x i lo hi : Int) (a : Option ES.A) (l : List (Option ES.A)) :
    CRules.logic_equiv (mixed_missing_i ES x i lo hi (a :: l))
      (CRules.orp
        (CRules.andp (CRules.coq_prop (i = lo))
          (mixed_seg ES x (lo + 1) hi l))
        (CRules.andp (CRules.coq_prop (i > lo))
          (CRules.sepcon (mixedstoreA ES x lo a)
            (mixed_missing_i ES x i (lo + 1) hi l)))) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x n : Int) :
    CRules.logic_equiv (full ES x n [])
      (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x n : Int) :
    CRules.logic_equiv (mixed_full ES x n [])
      (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x : Int) : CRules.logic_equiv (undef_full ES x 0) CRules.emp := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x : Int) : CRules.logic_equiv (full_shape ES x 0) CRules.emp := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

-- `entailer!` has the same conservative empty-resource cleanup: it rewrites
-- already-empty array resources, but does not infer emptiness or unfold conses.
example (x n : Int) (h : n = 0) :
    CRules.derivable1 CRules.emp (full ES x n []) := by
  entailer!

example (x lo : Int) :
    CRules.derivable1 CRules.emp (undef_seg ES x lo lo) := by
  entailer!

example (x : Int) :
    CRules.derivable1 CRules.emp (undef_full ES x 0) := by
  entailer!

example (x : Int) :
    CRules.derivable1 CRules.emp (full_shape ES x 0) := by
  entailer!

example (x n : Int) :
    CRules.derivable1 (full ES x n [])
      (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp) := by
  entailer!

set_option linter.unusedVariables false in
set_option linter.unreachableTactic false in
example (x n : Int) (a : ES.A) (l : List ES.A) : True := by
  fail_if_success
    have _h : CRules.derivable1 CRules.emp (full ES x n (a :: l)) := by
      entailer!
    exact True.intro
  trivial

set_option linter.unusedVariables false in
set_option linter.unreachableTactic false in
example (x n : Int) (l : List ES.A) (_hlen : AUXLib.Zlength l = 0) : True := by
  fail_if_success
    have _h : CRules.derivable1 CRules.emp (full ES x n l) := by
      entailer!
    exact True.intro
  trivial

set_option linter.unusedVariables false in
set_option linter.unreachableTactic false in
example (x n : Int) (_hn : n = 0) : True := by
  fail_if_success
    have _h : CRules.derivable1 CRules.emp (undef_full ES x n) := by
      entailer!
    exact True.intro
  trivial

example (x n : Int) (a : ES.A) (l : List ES.A) :
    CRules.logic_equiv (full ES x n (a :: l))
      (CRules.sepcon (ES.storeA x 0 a) (seg ES x 1 n l)) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x n : Int) (a : Option ES.A) (l : List (Option ES.A)) :
    CRules.logic_equiv (mixed_full ES x n (a :: l))
      (CRules.sepcon (mixedstoreA ES x 0 a) (mixed_seg ES x 1 n l)) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x n : Int) (h : n >= 0) :
    CRules.logic_equiv (undef_full ES x (n + 1))
      (CRules.sepcon (ES.undefstoreA x 0) (undef_seg ES x 1 (n + 1))) := by
  ArraySimplify
  · exact CRules.toContext.logic_equiv_refl _
  · exact h

example (x n : Int) (h : n >= 0) :
    CRules.logic_equiv (full_shape ES x (n + 1))
      (CRules.exp ES.A fun a =>
        CRules.sepcon (ES.storeA x 0 a) (seg_shape ES x 1 (n + 1))) := by
  ArraySimplify
  · exact CRules.toContext.logic_equiv_refl _
  · exact h

-- Repetition normalizes nested forms, including overlapping branch families.
example (x n : Int) (a b : ES.A) :
    CRules.logic_equiv (full ES x n [a, b])
      (CRules.sepcon (ES.storeA x 0 a)
        (CRules.sepcon (ES.storeA x 1 b)
          (CRules.andp (CRules.coq_prop (n = 2)) CRules.emp))) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x lo hi : Int) :
    CRules.logic_equiv
      (CRules.sepcon (seg ES x lo hi []) (mixed_seg ES x lo hi []))
      (CRules.sepcon
        (CRules.andp (CRules.coq_prop (hi = lo)) CRules.emp)
        (CRules.andp (CRules.coq_prop (hi = lo)) CRules.emp)) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

-- The source tactic is a successful no-op when no array form is present.
example : True := by
  ArraySimplify
  trivial

end

end ArrayLibCoreTests
