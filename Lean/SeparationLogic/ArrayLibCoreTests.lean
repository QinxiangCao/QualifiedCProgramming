import SimpleC.SL.ArrayLibCore

namespace ArrayLibCoreTests

open SimpleC.SL.CommonAssertion
open SimpleC.SL.StoreAux
open SimpleC.SL.ArrayLibCore
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig

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
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : StoreLibSig CRules DePredSig}
variable (ES : ELEMENT_STORE CRules DePredSig SLibSig)

open ArrayLib

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
