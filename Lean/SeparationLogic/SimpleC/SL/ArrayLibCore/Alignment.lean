import SimpleC.SL.ArrayLibCore.SplitMerge

namespace SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : SimpleC.SL.StoreAux.StoreLibSig CRules DePredSig}

private theorem store_undef_array_rec_mono
    (source target : addr -> Int -> CRules.expr)
    (hstore : forall x i, CRules.derivable1 (source x i) (target x i))
    (x lo hi : Int) (n : Nat) :
    CRules.derivable1
      (store_undef_array_rec CRules source x lo hi n)
      (store_undef_array_rec CRules target x lo hi n) := by
  induction n generalizing lo with
  | zero => exact CRules.toContext.derivable1_refl _
  | succ n ih =>
      simp only [store_undef_array_rec]
      exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (hstore x lo) (ih (lo := lo + 1))

theorem seg_shape_to_undef_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x lo hi : Int) :
    CRules.derivable1 (seg_shape ES x lo hi) (undef_seg ES x lo hi) := by
  apply store_undef_array_rec_mono
  intro p i
  apply Automation.exp_left_rule
  intro a
  exact ES.store_to_undefstore p i a

theorem full_shape_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (full_shape ES x n) (undef_full ES x n) := by
  have hResult := CRules.toContext.derivable1_trans _ _ _
    (full_shape_to_seg_shape ES x n)
    (CRules.toContext.derivable1_trans _ _ _
      (seg_shape_to_undef_seg ES x 0 n)
      (undef_seg_to_undef_full ES x 0 n))
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hResult

private theorem emp_to_store_align_zero (CRules : SeparationLogicSig) :
    CRules.derivable1 CRules.emp (store_align_n CRules 0) := by
  intro state hEmp
  exact ⟨[], ⟨rfl, interval_list_nil⟩, hEmp⟩

private theorem store_undef_array_rec_to_align
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (n : Nat) (hn : n = (hi - lo).toNat) :
    CRules.derivable1
      (store_undef_array_rec CRules ES.undefstoreA x lo hi n)
      (store_align_n CRules ((hi - lo) * ES.sizeA)) := by
  induction n generalizing lo hi with
  | zero =>
      simp only [store_undef_array_rec]
      apply coq_prop_andp_left
      intro hEq
      have hBytes : (hi - lo) * ES.sizeA = 0 := by rw [hEq]; simp
      rw [hBytes]
      exact emp_to_store_align_zero CRules
  | succ n ih =>
      have hnTail : n = (hi - (lo + 1)).toNat := by omega
      simp only [store_undef_array_rec]
      have hTail := ih (lo := lo + 1) (hi := hi) hnTail
      have hCombined := CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (ES.undefstore_to_align x lo) hTail)
        (store_align_merge CRules ES.sizeA ((hi - (lo + 1)) * ES.sizeA))
      have hBytes :
          ES.sizeA + (hi - (lo + 1)) * ES.sizeA =
            (hi - lo) * ES.sizeA := by
        calc
          ES.sizeA + (hi - (lo + 1)) * ES.sizeA =
              1 * ES.sizeA + (hi - (lo + 1)) * ES.sizeA := by simp
          _ = (1 + (hi - (lo + 1))) * ES.sizeA := by
            rw [Int.add_mul]
          _ = (hi - lo) * ES.sizeA := by
            congr 1
            omega
      rw [hBytes] at hCombined
      exact hCombined

theorem undef_seg_to_align
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x lo hi : Int) :
    CRules.derivable1 (undef_seg ES x lo hi)
      (store_align_n CRules ((hi - lo) * ES.sizeA)) := by
  exact store_undef_array_rec_to_align ES x lo hi (hi - lo).toNat rfl

theorem seg_to_align
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (seg ES x lo hi l)
      (store_align_n CRules ((hi - lo) * ES.sizeA)) :=
  CRules.toContext.derivable1_trans _ _ _
    (seg_to_undef_seg ES x lo hi l) (undef_seg_to_align ES x lo hi)

theorem mixed_seg_to_align
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_seg ES x lo hi l)
      (store_align_n CRules ((hi - lo) * ES.sizeA)) :=
  CRules.toContext.derivable1_trans _ _ _
    (mixed_seg_to_undef_seg ES x lo hi l) (undef_seg_to_align ES x lo hi)

theorem seg_shape_to_align
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x lo hi : Int) :
    CRules.derivable1 (seg_shape ES x lo hi)
      (store_align_n CRules ((hi - lo) * ES.sizeA)) :=
  CRules.toContext.derivable1_trans _ _ _
    (seg_shape_to_undef_seg ES x lo hi) (undef_seg_to_align ES x lo hi)

theorem full_to_align
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) :
    CRules.derivable1 (full ES x n l)
      (store_align_n CRules (n * ES.sizeA)) := by
  have hResult := CRules.toContext.derivable1_trans _ _ _
    (full_to_seg ES x n l) (seg_to_align ES x 0 n l)
  simpa only [Int.sub_zero] using hResult

theorem mixed_full_to_align
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_full ES x n l)
      (store_align_n CRules (n * ES.sizeA)) := by
  have hResult := CRules.toContext.derivable1_trans _ _ _
    (mixed_full_to_mixed_seg ES x n l) (mixed_seg_to_align ES x 0 n l)
  simpa only [Int.sub_zero] using hResult

theorem undef_full_to_align
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (undef_full ES x n)
      (store_align_n CRules (n * ES.sizeA)) := by
  have hResult := CRules.toContext.derivable1_trans _ _ _
    (undef_full_to_undef_seg ES x n) (undef_seg_to_align ES x 0 n)
  simpa only [Int.sub_zero] using hResult

theorem full_shape_to_align
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (full_shape ES x n)
      (store_align_n CRules (n * ES.sizeA)) := by
  have hResult := CRules.toContext.derivable1_trans _ _ _
    (full_shape_to_seg_shape ES x n) (seg_shape_to_align ES x 0 n)
  simpa only [Int.sub_zero] using hResult

theorem undef_full_valid
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (undef_full ES x n) (CRules.coq_prop (0 <= n)) := by
  intro _ hs
  change 0 <= n
  by_cases hn : 0 <= n
  · exact hn
  · have hzero : n.toNat = 0 := by omega
    simp only [undef_full, store_undef_array, hzero,
      store_undef_array_rec] at hs
    change 0 = n ∧ _ at hs
    omega

theorem full_shape_valid
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (full_shape ES x n) (CRules.coq_prop (0 <= n)) := by
  intro _ hs
  change 0 <= n
  by_cases hn : 0 <= n
  · exact hn
  · have hzero : n.toNat = 0 := by omega
    simp only [full_shape, store_undef_array, hzero,
      store_undef_array_rec] at hs
    change 0 = n ∧ _ at hs
    omega

private theorem length_range_of_valid_align
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (P : CRules.expr) (count : Int)
    (hvalid : CRules.derivable1 P (CRules.coq_prop (0 <= count)))
    (halign : CRules.derivable1 P
      (store_align_n CRules (count * ES.sizeA))) :
    CRules.derivable1 P
      (CRules.coq_prop
        (0 <= count * ES.sizeA ∧
          count * ES.sizeA <= Int.max_unsigned + 1)) := by
  intro state hs
  have hCount := hvalid state hs
  have hAlign := halign state hs
  have hUpper := store_align_n_valid CRules (count * ES.sizeA) state hAlign
  constructor
  · exact Int.mul_nonneg hCount (Int.le_of_lt ES.sizeA_valid.1)
  · simpa using hUpper

theorem seg_length_range
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (seg ES x lo hi l)
      (CRules.coq_prop
        (0 <= (hi - lo) * ES.sizeA ∧
          (hi - lo) * ES.sizeA <= Int.max_unsigned + 1)) :=
  length_range_of_valid_align ES (seg ES x lo hi l) (hi - lo)
    (by
      intro state hs
      have hv := seg_valid ES x lo hi l state hs
      change 0 <= hi - lo
      exact Int.sub_nonneg.mpr hv)
    (seg_to_align ES x lo hi l)

theorem mixed_seg_length_range
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_seg ES x lo hi l)
      (CRules.coq_prop
        (0 <= (hi - lo) * ES.sizeA ∧
          (hi - lo) * ES.sizeA <= Int.max_unsigned + 1)) :=
  length_range_of_valid_align ES (mixed_seg ES x lo hi l) (hi - lo)
    (by
      intro state hs
      have hv := mixed_seg_valid ES x lo hi l state hs
      change 0 <= hi - lo
      exact Int.sub_nonneg.mpr hv)
    (mixed_seg_to_align ES x lo hi l)

theorem undef_seg_length_range
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x lo hi : Int) :
    CRules.derivable1 (undef_seg ES x lo hi)
      (CRules.coq_prop
        (0 <= (hi - lo) * ES.sizeA ∧
          (hi - lo) * ES.sizeA <= Int.max_unsigned + 1)) :=
  length_range_of_valid_align ES (undef_seg ES x lo hi) (hi - lo)
    (by
      intro state hs
      have hv := undef_seg_valid ES x lo hi state hs
      change 0 <= hi - lo
      exact Int.sub_nonneg.mpr hv)
    (undef_seg_to_align ES x lo hi)

theorem seg_shape_length_range
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x lo hi : Int) :
    CRules.derivable1 (seg_shape ES x lo hi)
      (CRules.coq_prop
        (0 <= (hi - lo) * ES.sizeA ∧
          (hi - lo) * ES.sizeA <= Int.max_unsigned + 1)) :=
  length_range_of_valid_align ES (seg_shape ES x lo hi) (hi - lo)
    (by
      intro state hs
      have hv := seg_shape_valid ES x lo hi state hs
      change 0 <= hi - lo
      exact Int.sub_nonneg.mpr hv)
    (seg_shape_to_align ES x lo hi)

theorem full_length_range
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) :
    CRules.derivable1 (full ES x n l)
      (CRules.coq_prop
        (0 <= n * ES.sizeA ∧ n * ES.sizeA <= Int.max_unsigned + 1)) :=
  length_range_of_valid_align ES (full ES x n l) n
    (by
      intro state hs
      have hlen := full_length ES x n l state hs
      rw [← hlen]
      exact Int.natCast_nonneg _)
    (full_to_align ES x n l)

theorem mixed_full_length_range
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_full ES x n l)
      (CRules.coq_prop
        (0 <= n * ES.sizeA ∧ n * ES.sizeA <= Int.max_unsigned + 1)) :=
  length_range_of_valid_align ES (mixed_full ES x n l) n
    (by
      intro state hs
      have hlen := mixed_full_length ES x n l state hs
      rw [← hlen]
      exact Int.natCast_nonneg _)
    (mixed_full_to_align ES x n l)

theorem undef_full_length_range
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (undef_full ES x n)
      (CRules.coq_prop
        (0 <= n * ES.sizeA ∧ n * ES.sizeA <= Int.max_unsigned + 1)) :=
  length_range_of_valid_align ES (undef_full ES x n) n
    (undef_full_valid ES x n) (undef_full_to_align ES x n)

theorem full_shape_length_range
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (full_shape ES x n)
      (CRules.coq_prop
        (0 <= n * ES.sizeA ∧ n * ES.sizeA <= Int.max_unsigned + 1)) :=
  length_range_of_valid_align ES (full_shape ES x n) n
    (full_shape_valid ES x n) (full_shape_to_align ES x n)

end SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib
