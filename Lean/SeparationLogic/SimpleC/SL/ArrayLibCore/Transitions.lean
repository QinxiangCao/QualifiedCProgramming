import SimpleC.SL.ArrayLibCore.Automation

namespace SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open Unifysl.LogicGenerator.demo932
open scoped SimpleC.SL.SAC

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : SimpleC.SL.StoreAux.StoreLibSig CRules DePredSig}

theorem full_to_seg (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) :
    CRules.derivable1 (full ES x n l) (seg ES x 0 n l) := by
  exact CRules.toContext.derivable1_refl _

theorem undef_full_to_undef_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (undef_full ES x n) (undef_seg ES x 0 n) := by
  simp only [undef_full, undef_seg, store_undef_array, Int.sub_zero]
  exact CRules.toContext.derivable1_refl _

theorem full_shape_to_seg_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (full_shape ES x n) (seg_shape ES x 0 n) := by
  simp only [full_shape, seg_shape, store_undef_array, Int.sub_zero]
  exact CRules.toContext.derivable1_refl _

theorem mixed_full_to_mixed_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_full ES x n l) (mixed_seg ES x 0 n l) := by
  exact CRules.toContext.derivable1_refl _

theorem seg_to_mixed_seg (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (seg ES x lo hi l)
      (mixed_seg ES x lo hi (List.map Option.some l)) := by
  induction l generalizing lo hi with
  | nil =>
      simp only [List.map]
      rel_rw [seg_empty ES x lo hi]
      rel_rw [mixed_seg_empty ES x lo hi]
      exact CRules.toContext.derivable1_refl _
  | cons a l ih =>
      simp only [List.map]
      rel_rw [seg_unfold ES x lo hi l a]
      rel_rw [mixed_seg_unfold ES x lo hi (List.map Option.some l) (some a)]
      simp only [mixedstoreA]
      exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (CRules.toContext.derivable1_refl _) (ih (lo := lo + 1) (hi := hi))

theorem full_to_mixed_seg (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) :
    CRules.derivable1 (full ES x n l)
      (mixed_seg ES x 0 n (List.map Option.some l)) :=
  CRules.toContext.derivable1_trans _ _ _
    (full_to_seg ES x n l) (seg_to_mixed_seg ES x 0 n l)

theorem mixed_seg_to_seg (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (mixed_seg ES x lo hi (List.map Option.some l))
      (seg ES x lo hi l) := by
  induction l generalizing lo hi with
  | nil =>
      simp only [List.map]
      rel_rw [mixed_seg_empty ES x lo hi]
      rel_rw [seg_empty ES x lo hi]
      exact CRules.toContext.derivable1_refl _
  | cons a l ih =>
      simp only [List.map]
      rel_rw [mixed_seg_unfold ES x lo hi (List.map Option.some l) (some a)]
      rel_rw [seg_unfold ES x lo hi l a]
      simp only [mixedstoreA]
      exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (CRules.toContext.derivable1_refl _) (ih (lo := lo + 1) (hi := hi))

theorem missing_i_to_mixed_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (missing_i ES x i lo hi l)
      (mixed_missing_i ES x i lo hi (List.map Option.some l)) := by
  letI : SacContext := ⟨CRules⟩
  induction l generalizing i lo hi with
  | nil =>
      simp only [List.map, missing_i, mixed_missing_i,
        store_array_missing_i_rec]
      entailer!
  | cons a l ih =>
      simp only [List.map, missing_i, mixed_missing_i,
        store_array_missing_i_rec, mixedstoreA]
      Split
      · Intros
        Left
        sep_apply (seg_to_mixed_seg ES x (lo + 1) hi l)
        entailer!
      · Intros
        Right
        apply split_pure_and_spatial_goals
        · exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (CRules.toContext.derivable1_refl _)
            (ih (i := i) (lo := lo + 1) (hi := hi))
        · apply dump_spatial_left
          assumption

theorem mixed_missing_i_to_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List ES.A) :
    CRules.derivable1
      (mixed_missing_i ES x i lo hi (List.map Option.some l))
      (missing_i ES x i lo hi l) := by
  letI : SacContext := ⟨CRules⟩
  induction l generalizing i lo hi with
  | nil =>
      simp only [List.map, mixed_missing_i, missing_i,
        store_array_missing_i_rec]
      entailer!
  | cons a l ih =>
      simp only [List.map, mixed_missing_i, missing_i,
        store_array_missing_i_rec, mixedstoreA]
      Split
      · Intros
        Left
        sep_apply (mixed_seg_to_seg ES x (lo + 1) hi l)
        entailer!
      · Intros
        Right
        apply split_pure_and_spatial_goals
        · exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (CRules.toContext.derivable1_refl _)
            (ih (i := i) (lo := lo + 1) (hi := hi))
        · apply dump_spatial_left
          assumption

private theorem undef_seg_to_mixed_seg_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (n : Nat) (hn : n = (hi - lo).toNat) :
    CRules.derivable1
      (store_undef_array_rec CRules ES.undefstoreA x lo hi n)
      (store_array_rec CRules (mixedstoreA ES) x lo hi
        (List.replicate n none)) := by
  induction n generalizing lo with
  | zero =>
      simp only [store_undef_array_rec, List.replicate, store_array_rec]
      intro _ hs
      exact ⟨hs.1, trivial, hs.2⟩
  | succ n ih =>
      have htail : n = (hi - (lo + 1)).toNat := by omega
      simp only [store_undef_array_rec, List.replicate_succ, store_array_rec,
        mixedstoreA]
      exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (CRules.toContext.derivable1_refl _)
        (ih (lo := lo + 1) htail)

theorem undef_seg_to_mixed_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x lo hi : Int) :
    CRules.derivable1 (undef_seg ES x lo hi)
      (mixed_seg ES x lo hi (List.replicate (hi - lo).toNat none)) := by
  simpa only [undef_seg, mixed_seg] using
    undef_seg_to_mixed_seg_rec ES x lo hi (hi - lo).toNat rfl

theorem undef_full_to_mixed_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (undef_full ES x n)
      (mixed_seg ES x 0 n (List.replicate n.toNat none)) := by
  simpa only [Int.sub_zero] using
    CRules.toContext.derivable1_trans _ _ _
      (undef_full_to_undef_seg ES x n)
      (undef_seg_to_mixed_seg ES x 0 n)

theorem seg_shift (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (l : List ES.A) :
    CRules.logic_equiv (seg ES x (lo + mid) (lo + hi) l)
      (seg ES (x + lo * ES.sizeA) mid hi l) := by
  induction l generalizing lo mid hi with
  | nil =>
      simp only [seg, store_array_rec]
      constructor
      · intro _ hs
        have heq := hs.1
        refine ⟨?_, hs.2⟩
        change mid = hi
        change lo + mid = lo + hi at heq
        omega
      · intro _ hs
        have heq := hs.1
        refine ⟨?_, hs.2⟩
        change lo + mid = lo + hi
        change mid = hi at heq
        omega
  | cons a l ih =>
      simp only [seg, store_array_rec]
      rw [show lo + mid + 1 = lo + (mid + 1) by omega]
      have hstore : CRules.logic_equiv (ES.storeA x (lo + mid) a)
          (ES.storeA (x + lo * ES.sizeA) mid a) := by
        simpa only [Int.add_comm] using
          CRules.toContext.logic_equiv_symm _ _ (ES.storeA_shift x lo mid a)
      exact CRules.toContext.logic_equiv_sepcon_proper.proper _ _ hstore _ _
        (ih (lo := lo) (mid := mid + 1) (hi := hi))

theorem mixed_seg_shift (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (l : List (Option ES.A)) :
    CRules.logic_equiv (mixed_seg ES x (lo + mid) (lo + hi) l)
      (mixed_seg ES (x + lo * ES.sizeA) mid hi l) := by
  induction l generalizing lo mid hi with
  | nil =>
      simp only [mixed_seg, store_array_rec]
      constructor
      · intro _ hs
        have heq := hs.1
        refine ⟨?_, hs.2⟩
        change mid = hi
        change lo + mid = lo + hi at heq
        omega
      · intro _ hs
        have heq := hs.1
        refine ⟨?_, hs.2⟩
        change lo + mid = lo + hi
        change mid = hi at heq
        omega
  | cons a l ih =>
      simp only [mixed_seg, store_array_rec]
      rw [show lo + mid + 1 = lo + (mid + 1) by omega]
      have hstore : CRules.logic_equiv (mixedstoreA ES x (lo + mid) a)
          (mixedstoreA ES (x + lo * ES.sizeA) mid a) := by
        simpa only [Int.add_comm] using
          CRules.toContext.logic_equiv_symm _ _
            (mixedstoreA_shift ES x lo mid a)
      exact CRules.toContext.logic_equiv_sepcon_proper.proper _ _ hstore _ _
        (ih (lo := lo) (mid := mid + 1) (hi := hi))

theorem seg_0_shift (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.logic_equiv (seg ES x lo hi l)
      (seg ES (x + lo * ES.sizeA) 0 (hi - lo) l) := by
  have h := seg_shift ES x lo 0 (hi - lo) l
  rw [show lo + 0 = lo by omega, show lo + (hi - lo) = hi by omega] at h
  exact h

theorem mixed_seg_0_shift (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A)) :
    CRules.logic_equiv (mixed_seg ES x lo hi l)
      (mixed_seg ES (x + lo * ES.sizeA) 0 (hi - lo) l) := by
  have h := mixed_seg_shift ES x lo 0 (hi - lo) l
  rw [show lo + 0 = lo by omega, show lo + (hi - lo) = hi by omega] at h
  exact h

private theorem undef_seg_shift_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (n : Nat) :
    CRules.logic_equiv
      (store_undef_array_rec CRules ES.undefstoreA x
        (lo + mid) (lo + hi) n)
      (store_undef_array_rec CRules ES.undefstoreA
        (x + lo * ES.sizeA) mid hi n) := by
  induction n generalizing mid with
  | zero =>
      simp only [store_undef_array_rec]
      constructor
      · intro _ hs
        have heq := hs.1
        refine ⟨?_, hs.2⟩
        change mid = hi
        change lo + mid = lo + hi at heq
        omega
      · intro _ hs
        have heq := hs.1
        refine ⟨?_, hs.2⟩
        change lo + mid = lo + hi
        change mid = hi at heq
        omega
  | succ n ih =>
      simp only [store_undef_array_rec]
      rw [show lo + mid + 1 = lo + (mid + 1) by omega]
      have hstore : CRules.logic_equiv (ES.undefstoreA x (lo + mid))
          (ES.undefstoreA (x + lo * ES.sizeA) mid) := by
        simpa only [Int.add_comm] using
          CRules.toContext.logic_equiv_symm _ _
            (ES.undefstoreA_shift x lo mid)
      exact CRules.toContext.logic_equiv_sepcon_proper.proper _ _ hstore _ _
        (ih (mid := mid + 1))

theorem undef_seg_shift (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) :
    CRules.logic_equiv (undef_seg ES x (lo + mid) (lo + hi))
      (undef_seg ES (x + lo * ES.sizeA) mid hi) := by
  have hcount : (lo + hi - (lo + mid)).toNat = (hi - mid).toNat := by
    congr 1
    omega
  simp only [undef_seg, hcount]
  exact undef_seg_shift_rec ES x lo mid hi (hi - mid).toNat

theorem undef_seg_0_shift (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) :
    CRules.logic_equiv (undef_seg ES x lo hi)
      (undef_seg ES (x + lo * ES.sizeA) 0 (hi - lo)) := by
  have h := undef_seg_shift ES x lo 0 (hi - lo)
  rw [show lo + 0 = lo by omega, show lo + (hi - lo) = hi by omega] at h
  exact h

private theorem seg_shape_shift_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (n : Nat) :
    CRules.logic_equiv
      (store_undef_array_rec CRules
        (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
        x (lo + mid) (lo + hi) n)
      (store_undef_array_rec CRules
        (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
        (x + lo * ES.sizeA) mid hi n) := by
  induction n generalizing mid with
  | zero =>
      simp only [store_undef_array_rec]
      constructor
      · intro _ hs
        have heq := hs.1
        refine ⟨?_, hs.2⟩
        change mid = hi
        change lo + mid = lo + hi at heq
        omega
      · intro _ hs
        have heq := hs.1
        refine ⟨?_, hs.2⟩
        change lo + mid = lo + hi
        change mid = hi at heq
        omega
  | succ n ih =>
      simp only [store_undef_array_rec]
      rw [show lo + mid + 1 = lo + (mid + 1) by omega]
      have hstore : CRules.logic_equiv
          (CRules.exp ES.A fun a => ES.storeA x (lo + mid) a)
          (CRules.exp ES.A fun a => ES.storeA (x + lo * ES.sizeA) mid a) := by
        apply Automation.logic_equiv_exp_rule
        intro a
        simpa only [Int.add_comm] using
          CRules.toContext.logic_equiv_symm _ _ (ES.storeA_shift x lo mid a)
      exact CRules.toContext.logic_equiv_sepcon_proper.proper _ _ hstore _ _
        (ih (mid := mid + 1))

theorem seg_shape_shift (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) :
    CRules.logic_equiv (seg_shape ES x (lo + mid) (lo + hi))
      (seg_shape ES (x + lo * ES.sizeA) mid hi) := by
  have hcount : (lo + hi - (lo + mid)).toNat = (hi - mid).toNat := by
    congr 1
    omega
  simp only [seg_shape, hcount]
  exact seg_shape_shift_rec ES x lo mid hi (hi - mid).toNat

theorem seg_shape_0_shift (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) :
    CRules.logic_equiv (seg_shape ES x lo hi)
      (seg_shape ES (x + lo * ES.sizeA) 0 (hi - lo)) := by
  have h := seg_shape_shift ES x lo 0 (hi - lo)
  rw [show lo + 0 = lo by omega, show lo + (hi - lo) = hi by omega] at h
  exact h

theorem seg_to_full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (seg ES x lo hi l)
      (full ES (x + lo * ES.sizeA) (hi - lo) l) := by
  simpa only [seg, full, store_array] using (seg_0_shift ES x lo hi l).left

theorem mixed_seg_to_mixed_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_seg ES x lo hi l)
      (mixed_full ES (x + lo * ES.sizeA) (hi - lo) l) := by
  simpa only [mixed_seg, mixed_full, store_array] using
    (mixed_seg_0_shift ES x lo hi l).left

theorem mixed_full_to_full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) :
    CRules.derivable1 (mixed_full ES x n (List.map Option.some l))
      (full ES x n l) :=
  CRules.toContext.derivable1_trans _ _ _
    (mixed_full_to_mixed_seg ES x n (List.map Option.some l))
    (mixed_seg_to_seg ES x 0 n l)

theorem full_to_mixed_full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) :
    CRules.derivable1 (full ES x n l)
      (mixed_full ES x n (List.map Option.some l)) := by
  have h := CRules.toContext.derivable1_trans _ _ _
    (full_to_mixed_seg ES x n l)
    (mixed_seg_to_mixed_full ES x 0 n (List.map Option.some l))
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using h

theorem undef_full_to_mixed_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n : Int) :
    CRules.derivable1 (undef_full ES x n)
      (mixed_full ES x n (List.replicate n.toNat none)) := by
  have h := CRules.toContext.derivable1_trans _ _ _
    (undef_full_to_mixed_seg ES x n)
    (mixed_seg_to_mixed_full ES x 0 n (List.replicate n.toNat none))
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using h

private theorem seg_to_undef_seg_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A)
    (hlen : Zlength l = hi - lo) :
    CRules.derivable1 (seg ES x lo hi l) (undef_seg ES x lo hi) := by
  induction l generalizing lo with
  | nil =>
      have hzero : (hi - lo).toNat = 0 := by
        rw [← hlen]
        simp
      simp only [seg, store_array_rec, undef_seg, hzero, store_undef_array_rec]
      intro _ hs
      exact ⟨hs.1, hs.2.2⟩
  | cons a l ih =>
      have hcount : (hi - lo).toNat = Nat.succ l.length := by
        rw [← hlen]
        simp [Zlength]
      have htail : Zlength l = hi - (lo + 1) := by
        simp only [Zlength_cons] at hlen
        omega
      have htailCount : (hi - (lo + 1)).toNat = l.length := by
        rw [← htail]
        simp [Zlength]
      have ihTail : CRules.derivable1
          (store_array_rec CRules ES.storeA x (lo + 1) hi l)
          (store_undef_array_rec CRules ES.undefstoreA x (lo + 1) hi l.length) := by
        simpa only [seg, undef_seg, htailCount] using ih (lo := lo + 1) htail
      simp only [seg, store_array_rec, undef_seg, hcount, store_undef_array_rec]
      exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (ES.store_to_undefstore x lo a) ihTail

theorem seg_to_undef_seg (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (seg ES x lo hi l) (undef_seg ES x lo hi) := by
  intro state hs
  have hlen := seg_Zlength ES x lo hi l state hs
  change Zlength l = hi - lo at hlen
  exact seg_to_undef_seg_rec ES x lo hi l hlen state hs

private theorem mixed_seg_to_undef_seg_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A))
    (hlen : Zlength l = hi - lo) :
    CRules.derivable1 (mixed_seg ES x lo hi l) (undef_seg ES x lo hi) := by
  induction l generalizing lo with
  | nil =>
      have hzero : (hi - lo).toNat = 0 := by
        rw [← hlen]
        simp
      simp only [mixed_seg, store_array_rec, undef_seg, hzero,
        store_undef_array_rec]
      intro _ hs
      exact ⟨hs.1, hs.2.2⟩
  | cons a l ih =>
      have hcount : (hi - lo).toNat = Nat.succ l.length := by
        rw [← hlen]
        simp [Zlength]
      have htail : Zlength l = hi - (lo + 1) := by
        simp only [Zlength_cons] at hlen
        omega
      have htailCount : (hi - (lo + 1)).toNat = l.length := by
        rw [← htail]
        simp [Zlength]
      have ihTail : CRules.derivable1
          (store_array_rec CRules (mixedstoreA ES) x (lo + 1) hi l)
          (store_undef_array_rec CRules ES.undefstoreA x (lo + 1) hi l.length) := by
        simpa only [mixed_seg, undef_seg, htailCount] using ih (lo := lo + 1) htail
      simp only [mixed_seg, store_array_rec, undef_seg, hcount,
        store_undef_array_rec]
      exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (mixedstoreA_to_undefstoreA ES x lo a) ihTail

theorem mixed_seg_to_undef_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_seg ES x lo hi l) (undef_seg ES x lo hi) := by
  intro state hs
  have hlen := mixed_seg_Zlength ES x lo hi l state hs
  change Zlength l = hi - lo at hlen
  exact mixed_seg_to_undef_seg_rec ES x lo hi l hlen state hs

private theorem seg_to_seg_shape_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A)
    (hlen : Zlength l = hi - lo) :
    CRules.derivable1 (seg ES x lo hi l) (seg_shape ES x lo hi) := by
  induction l generalizing lo with
  | nil =>
      have hzero : (hi - lo).toNat = 0 := by
        rw [← hlen]
        simp
      simp only [seg, store_array_rec, seg_shape, hzero, store_undef_array_rec]
      intro _ hs
      exact ⟨hs.1, hs.2.2⟩
  | cons a l ih =>
      have hcount : (hi - lo).toNat = Nat.succ l.length := by
        rw [← hlen]
        simp [Zlength]
      have htail : Zlength l = hi - (lo + 1) := by
        simp only [Zlength_cons] at hlen
        omega
      have htailCount : (hi - (lo + 1)).toNat = l.length := by
        rw [← htail]
        simp [Zlength]
      have ihTail : CRules.derivable1
          (store_array_rec CRules ES.storeA x (lo + 1) hi l)
          (store_undef_array_rec CRules
            (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
            x (lo + 1) hi l.length) := by
        simpa only [seg, seg_shape, htailCount] using ih (lo := lo + 1) htail
      simp only [seg, store_array_rec, seg_shape, hcount, store_undef_array_rec]
      exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (Automation.exp_right_rule a (CRules.toContext.derivable1_refl _))
        ihTail

theorem seg_to_seg_shape (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (seg ES x lo hi l) (seg_shape ES x lo hi) := by
  intro state hs
  have hlen := seg_Zlength ES x lo hi l state hs
  change Zlength l = hi - lo at hlen
  exact seg_to_seg_shape_rec ES x lo hi l hlen state hs

theorem undef_seg_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x lo hi : Int) :
    CRules.derivable1 (undef_seg ES x lo hi)
      (undef_full ES (x + lo * ES.sizeA) (hi - lo)) := by
  simpa only [undef_seg, undef_full, store_undef_array, Int.sub_zero] using
    (undef_seg_0_shift ES x lo hi).left

theorem seg_shape_to_full_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x lo hi : Int) :
    CRules.derivable1 (seg_shape ES x lo hi)
      (full_shape ES (x + lo * ES.sizeA) (hi - lo)) := by
  simpa only [seg_shape, full_shape, store_undef_array, Int.sub_zero] using
    (seg_shape_0_shift ES x lo hi).left

theorem missing_i_to_seg_head
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (a : ES.A) (l : List ES.A) :
    CRules.derivable1 (missing_i ES x lo lo hi (a :: l))
      (seg ES x (lo + 1) hi l) := by
  simp only [missing_i, store_array_missing_i_rec]
  intro _ hs
  rcases hs with hs | hs
  · exact hs.2
  · have hfalse := hs.1
    change lo > lo at hfalse
    omega

theorem mixed_missing_i_to_mixed_seg_head
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (a : Option ES.A) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_missing_i ES x lo lo hi (a :: l))
      (mixed_seg ES x (lo + 1) hi l) := by
  simp only [mixed_missing_i, store_array_missing_i_rec]
  intro _ hs
  rcases hs with hs | hs
  · exact hs.2
  · have hfalse := hs.1
    change lo > lo at hfalse
    omega

theorem undef_missing_i_to_undef_seg_head
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (h : lo < hi) :
    CRules.derivable1 (undef_missing_i ES x lo lo hi)
      (undef_seg ES x (lo + 1) hi) := by
  have hcount : (hi - lo).toNat = Nat.succ (hi - (lo + 1)).toNat := by omega
  simp only [undef_missing_i, hcount, store_undef_array_missing_i_rec]
  intro _ hs
  rcases hs with hs | hs
  · exact hs.2
  · have hfalse := hs.1
    change lo > lo at hfalse
    omega

theorem missing_i_shape_to_seg_shape_head
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (h : lo < hi) :
    CRules.derivable1 (missing_i_shape ES x lo lo hi)
      (seg_shape ES x (lo + 1) hi) := by
  have hcount : (hi - lo).toNat = Nat.succ (hi - (lo + 1)).toNat := by omega
  simp only [missing_i_shape, hcount, store_undef_array_missing_i_rec]
  intro _ hs
  rcases hs with hs | hs
  · exact hs.2
  · have hfalse := hs.1
    change lo > lo at hfalse
    omega

private theorem missing_i_to_undef_missing_i_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List ES.A) (hlen : Zlength l = hi - lo) :
    CRules.derivable1 (missing_i ES x i lo hi l)
      (undef_missing_i ES x i lo hi) := by
  induction l generalizing lo with
  | nil =>
      have hzero : (hi - lo).toNat = 0 := by
        rw [← hlen]
        simp
      simp only [missing_i, undef_missing_i, store_array_missing_i_rec,
        hzero, store_undef_array_missing_i_rec]
      exact CRules.toContext.derivable1_refl _
  | cons a l ih =>
      have hcount : (hi - lo).toNat = Nat.succ l.length := by
        rw [← hlen]
        simp [Zlength]
      have htail : Zlength l = hi - (lo + 1) := by
        simp only [Zlength_cons] at hlen
        omega
      have htailCount : (hi - (lo + 1)).toNat = l.length := by
        rw [← htail]
        simp [Zlength]
      have hleft : CRules.derivable1
          (store_array_rec CRules ES.storeA x (lo + 1) hi l)
          (store_undef_array_rec CRules ES.undefstoreA x (lo + 1) hi l.length) := by
        simpa only [seg, undef_seg, htailCount] using
          seg_to_undef_seg_rec ES x (lo + 1) hi l htail
      have hright : CRules.derivable1
          (CRules.sepcon (ES.storeA x lo a)
            (store_array_missing_i_rec CRules ES.storeA x i (lo + 1) hi l))
          (CRules.sepcon (ES.undefstoreA x lo)
            (store_undef_array_missing_i_rec CRules ES.undefstoreA
              x i (lo + 1) hi l.length)) := by
        have ihTail : CRules.derivable1
            (store_array_missing_i_rec CRules ES.storeA x i (lo + 1) hi l)
            (store_undef_array_missing_i_rec CRules ES.undefstoreA
              x i (lo + 1) hi l.length) := by
          simpa only [missing_i, undef_missing_i, htailCount] using
            ih (lo := lo + 1) htail
        exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (ES.store_to_undefstore x lo a) ihTail
      simp only [missing_i, undef_missing_i, store_array_missing_i_rec,
        hcount, store_undef_array_missing_i_rec]
      intro state hs
      rcases hs with hs | hs
      · exact Or.inl ⟨hs.1, hleft state hs.2⟩
      · exact Or.inr ⟨hs.1, hright state hs.2⟩

theorem missing_i_to_undef_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (missing_i ES x i lo hi l)
      (undef_missing_i ES x i lo hi) := by
  intro state hs
  have hlen := missing_i_Zlength ES x i lo hi l state hs
  change Zlength l = hi - lo at hlen
  exact missing_i_to_undef_missing_i_rec ES x i lo hi l hlen state hs

private theorem mixed_missing_i_to_undef_missing_i_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List (Option ES.A))
    (hlen : Zlength l = hi - lo) :
    CRules.derivable1 (mixed_missing_i ES x i lo hi l)
      (undef_missing_i ES x i lo hi) := by
  induction l generalizing lo with
  | nil =>
      have hzero : (hi - lo).toNat = 0 := by
        rw [← hlen]
        simp
      simp only [mixed_missing_i, undef_missing_i,
        store_array_missing_i_rec, hzero, store_undef_array_missing_i_rec]
      exact CRules.toContext.derivable1_refl _
  | cons a l ih =>
      have hcount : (hi - lo).toNat = Nat.succ l.length := by
        rw [← hlen]
        simp [Zlength]
      have htail : Zlength l = hi - (lo + 1) := by
        simp only [Zlength_cons] at hlen
        omega
      have htailCount : (hi - (lo + 1)).toNat = l.length := by
        rw [← htail]
        simp [Zlength]
      have hleft : CRules.derivable1
          (store_array_rec CRules (mixedstoreA ES) x (lo + 1) hi l)
          (store_undef_array_rec CRules ES.undefstoreA x (lo + 1) hi l.length) := by
        simpa only [mixed_seg, undef_seg, htailCount] using
          mixed_seg_to_undef_seg_rec ES x (lo + 1) hi l htail
      have hright : CRules.derivable1
          (CRules.sepcon (mixedstoreA ES x lo a)
            (store_array_missing_i_rec CRules (mixedstoreA ES)
              x i (lo + 1) hi l))
          (CRules.sepcon (ES.undefstoreA x lo)
            (store_undef_array_missing_i_rec CRules ES.undefstoreA
              x i (lo + 1) hi l.length)) := by
        have ihTail : CRules.derivable1
            (store_array_missing_i_rec CRules (mixedstoreA ES)
              x i (lo + 1) hi l)
            (store_undef_array_missing_i_rec CRules ES.undefstoreA
              x i (lo + 1) hi l.length) := by
          simpa only [mixed_missing_i, undef_missing_i, htailCount] using
            ih (lo := lo + 1) htail
        exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (mixedstoreA_to_undefstoreA ES x lo a) ihTail
      simp only [mixed_missing_i, undef_missing_i,
        store_array_missing_i_rec, hcount, store_undef_array_missing_i_rec]
      intro state hs
      rcases hs with hs | hs
      · exact Or.inl ⟨hs.1, hleft state hs.2⟩
      · exact Or.inr ⟨hs.1, hright state hs.2⟩

theorem mixed_missing_i_to_undef_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_missing_i ES x i lo hi l)
      (undef_missing_i ES x i lo hi) := by
  intro state hs
  have hlen := mixed_missing_i_Zlength ES x i lo hi l state hs
  change Zlength l = hi - lo at hlen
  exact mixed_missing_i_to_undef_missing_i_rec ES x i lo hi l hlen state hs

private theorem undef_missing_i_to_mixed_missing_i_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (n : Nat) (hn : n = (hi - lo).toNat) :
    CRules.derivable1
      (store_undef_array_missing_i_rec CRules ES.undefstoreA x i lo hi n)
      (store_array_missing_i_rec CRules (mixedstoreA ES) x i lo hi
        (List.replicate n none)) := by
  induction n generalizing lo with
  | zero =>
      simp only [store_undef_array_missing_i_rec, List.replicate,
        store_array_missing_i_rec]
      exact CRules.toContext.derivable1_refl _
  | succ n ih =>
      have htail : n = (hi - (lo + 1)).toNat := by omega
      have hleft := undef_seg_to_mixed_seg_rec ES x (lo + 1) hi n htail
      have hright : CRules.derivable1
          (CRules.sepcon (ES.undefstoreA x lo)
            (store_undef_array_missing_i_rec CRules ES.undefstoreA
              x i (lo + 1) hi n))
          (CRules.sepcon (mixedstoreA ES x lo none)
            (store_array_missing_i_rec CRules (mixedstoreA ES)
              x i (lo + 1) hi (List.replicate n none))) :=
        CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_refl _) (ih (lo := lo + 1) htail)
      simp only [store_undef_array_missing_i_rec, List.replicate_succ,
        store_array_missing_i_rec, mixedstoreA]
      intro state hs
      rcases hs with hs | hs
      · exact Or.inl ⟨hs.1, hleft state hs.2⟩
      · exact Or.inr ⟨hs.1, hright state hs.2⟩

theorem undef_missing_i_to_mixed_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x i lo hi : Int) :
    CRules.derivable1 (undef_missing_i ES x i lo hi)
      (mixed_missing_i ES x i lo hi
        (List.replicate (hi - lo).toNat none)) := by
  simpa only [undef_missing_i, mixed_missing_i] using
    undef_missing_i_to_mixed_missing_i_rec ES x i lo hi (hi - lo).toNat rfl

private theorem missing_i_to_missing_i_shape_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List ES.A) (hlen : Zlength l = hi - lo) :
    CRules.derivable1 (missing_i ES x i lo hi l)
      (missing_i_shape ES x i lo hi) := by
  induction l generalizing lo with
  | nil =>
      have hzero : (hi - lo).toNat = 0 := by
        rw [← hlen]
        simp
      simp only [missing_i, missing_i_shape, store_array_missing_i_rec,
        hzero, store_undef_array_missing_i_rec]
      exact CRules.toContext.derivable1_refl _
  | cons a l ih =>
      have hcount : (hi - lo).toNat = Nat.succ l.length := by
        rw [← hlen]
        simp [Zlength]
      have htail : Zlength l = hi - (lo + 1) := by
        simp only [Zlength_cons] at hlen
        omega
      have htailCount : (hi - (lo + 1)).toNat = l.length := by
        rw [← htail]
        simp [Zlength]
      have hleft : CRules.derivable1
          (store_array_rec CRules ES.storeA x (lo + 1) hi l)
          (store_undef_array_rec CRules
            (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
            x (lo + 1) hi l.length) := by
        simpa only [seg, seg_shape, htailCount] using
          seg_to_seg_shape_rec ES x (lo + 1) hi l htail
      have hright : CRules.derivable1
          (CRules.sepcon (ES.storeA x lo a)
            (store_array_missing_i_rec CRules ES.storeA x i (lo + 1) hi l))
          (CRules.sepcon (CRules.exp ES.A fun a => ES.storeA x lo a)
            (store_undef_array_missing_i_rec CRules
              (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
              x i (lo + 1) hi l.length)) := by
        have ihTail : CRules.derivable1
            (store_array_missing_i_rec CRules ES.storeA x i (lo + 1) hi l)
            (store_undef_array_missing_i_rec CRules
              (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
              x i (lo + 1) hi l.length) := by
          simpa only [missing_i, missing_i_shape, htailCount] using
            ih (lo := lo + 1) htail
        exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (Automation.exp_right_rule a (CRules.toContext.derivable1_refl _)) ihTail
      simp only [missing_i, missing_i_shape, store_array_missing_i_rec,
        hcount, store_undef_array_missing_i_rec]
      intro state hs
      rcases hs with hs | hs
      · exact Or.inl ⟨hs.1, hleft state hs.2⟩
      · exact Or.inr ⟨hs.1, hright state hs.2⟩

theorem missing_i_to_missing_i_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (missing_i ES x i lo hi l)
      (missing_i_shape ES x i lo hi) := by
  intro state hs
  have hlen := missing_i_Zlength ES x i lo hi l state hs
  change Zlength l = hi - lo at hlen
  exact missing_i_to_missing_i_shape_rec ES x i lo hi l hlen state hs

theorem full_to_undef_full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) :
    CRules.derivable1 (full ES x n l) (undef_full ES x n) := by
  have h := CRules.toContext.derivable1_trans _ _ _ (full_to_seg ES x n l) <|
    CRules.toContext.derivable1_trans _ _ _ (seg_to_undef_seg ES x 0 n l)
      (undef_seg_to_undef_full ES x 0 n)
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using h

theorem mixed_seg_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_seg ES x lo hi l)
      (undef_full ES (x + lo * ES.sizeA) (hi - lo)) :=
  CRules.toContext.derivable1_trans _ _ _
    (mixed_seg_to_undef_seg ES x lo hi l) (undef_seg_to_undef_full ES x lo hi)

theorem mixed_full_to_undef_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_full ES x n l) (undef_seg ES x 0 n) :=
  CRules.toContext.derivable1_trans _ _ _
    (mixed_full_to_mixed_seg ES x n l) (mixed_seg_to_undef_seg ES x 0 n l)

theorem mixed_full_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_full ES x n l) (undef_full ES x n) := by
  have h := CRules.toContext.derivable1_trans _ _ _
    (mixed_full_to_undef_seg ES x n l) (undef_seg_to_undef_full ES x 0 n)
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using h

theorem full_to_full_shape (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) :
    CRules.derivable1 (full ES x n l) (full_shape ES x n) := by
  have h := CRules.toContext.derivable1_trans _ _ _ (full_to_seg ES x n l) <|
    CRules.toContext.derivable1_trans _ _ _ (seg_to_seg_shape ES x 0 n l)
      (seg_shape_to_full_shape ES x 0 n)
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using h

private theorem sepcon_coq_false_elim (CRules : SeparationLogicSig)
    (P Q : CRules.expr) :
    CRules.derivable1 (CRules.sepcon P (CRules.coq_prop False)) Q := by
  intro _ hs
  rcases hs with ⟨_, _, _, _, hfalse⟩
  change False at hfalse
  exact False.elim hfalse

theorem missing_i_to_seg_tail
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (a : ES.A) (l : List ES.A) :
    CRules.derivable1 (missing_i ES x hi lo hi (l ++ [a]))
      (seg ES x lo (hi - 1) l) := by
  induction l generalizing lo with
  | nil =>
      simp only [List.nil_append, missing_i, store_array_missing_i_rec]
      intro state hs
      rcases hs with hs | hs
      · have heq := hs.1
        change hi = lo at heq
        have hlen := seg_Zlength ES x (lo + 1) hi [] state hs.2
        change Zlength ([] : List ES.A) = hi - (lo + 1) at hlen
        simp at hlen
        omega
      · exact sepcon_coq_false_elim CRules (ES.storeA x lo a)
          (seg ES x lo (hi - 1) []) state hs.2
  | cons b l ih =>
      simp only [List.cons_append, missing_i, store_array_missing_i_rec,
        seg, store_array_rec]
      intro state hs
      rcases hs with hs | hs
      · have heq := hs.1
        change hi = lo at heq
        have hlen := seg_Zlength ES x (lo + 1) hi (l ++ [a]) state hs.2
        change Zlength (l ++ [a]) = hi - (lo + 1) at hlen
        simp [Zlength] at hlen
        omega
      · exact (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_refl _)
          (ih (lo := lo + 1))) state hs.2

theorem mixed_missing_i_to_mixed_seg_tail
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (a : Option ES.A) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_missing_i ES x hi lo hi (l ++ [a]))
      (mixed_seg ES x lo (hi - 1) l) := by
  induction l generalizing lo with
  | nil =>
      simp only [List.nil_append, mixed_missing_i, store_array_missing_i_rec]
      intro state hs
      rcases hs with hs | hs
      · have heq := hs.1
        change hi = lo at heq
        have hlen := mixed_seg_Zlength ES x (lo + 1) hi [] state hs.2
        change Zlength ([] : List (Option ES.A)) = hi - (lo + 1) at hlen
        simp at hlen
        omega
      · exact sepcon_coq_false_elim CRules (mixedstoreA ES x lo a)
          (mixed_seg ES x lo (hi - 1) []) state hs.2
  | cons b l ih =>
      simp only [List.cons_append, mixed_missing_i, store_array_missing_i_rec,
        mixed_seg, store_array_rec]
      intro state hs
      rcases hs with hs | hs
      · have heq := hs.1
        change hi = lo at heq
        have hlen := mixed_seg_Zlength ES x (lo + 1) hi (l ++ [a]) state hs.2
        change Zlength (l ++ [a]) = hi - (lo + 1) at hlen
        simp [Zlength] at hlen
        omega
      · exact (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_refl _)
          (ih (lo := lo + 1))) state hs.2

private theorem undef_missing_i_to_undef_seg_tail_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (n : Nat) (hlt : lo < hi)
    (hn : n = (hi - (lo + 1)).toNat) :
    CRules.derivable1
      (store_undef_array_missing_i_rec CRules ES.undefstoreA
        x hi lo hi (Nat.succ n))
      (store_undef_array_rec CRules ES.undefstoreA x lo (hi - 1) n) := by
  induction n generalizing lo with
  | zero =>
      simp only [store_undef_array_missing_i_rec, store_undef_array_rec]
      intro state hs
      rcases hs with hs | hs
      · have heq := hs.1
        change hi = lo at heq
        omega
      · exact sepcon_coq_false_elim CRules (ES.undefstoreA x lo)
          (CRules.andp (CRules.coq_prop (lo = hi - 1)) CRules.emp) state hs.2
  | succ n ih =>
      have hltTail : lo + 1 < hi := by omega
      have hnTail : n = (hi - ((lo + 1) + 1)).toNat := by omega
      simp only [store_undef_array_missing_i_rec, store_undef_array_rec]
      intro state hs
      rcases hs with hs | hs
      · have heq := hs.1
        change hi = lo at heq
        omega
      · exact (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_refl _)
          (ih (lo := lo + 1) hltTail hnTail)) state hs.2

theorem undef_missing_i_to_undef_seg_tail
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (h : lo < hi) :
    CRules.derivable1 (undef_missing_i ES x hi lo hi)
      (undef_seg ES x lo (hi - 1)) := by
  have hsource : (hi - lo).toNat = Nat.succ (hi - (lo + 1)).toNat := by omega
  have htarget : (hi - 1 - lo).toNat = (hi - (lo + 1)).toNat := by
    congr 1
    omega
  simp only [undef_missing_i, undef_seg, hsource, htarget]
  exact undef_missing_i_to_undef_seg_tail_rec ES x lo hi
    (hi - (lo + 1)).toNat h rfl

private theorem missing_i_shape_to_seg_shape_tail_rec
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (n : Nat) (hlt : lo < hi)
    (hn : n = (hi - (lo + 1)).toNat) :
    CRules.derivable1
      (store_undef_array_missing_i_rec CRules
        (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
        x hi lo hi (Nat.succ n))
      (store_undef_array_rec CRules
        (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
        x lo (hi - 1) n) := by
  induction n generalizing lo with
  | zero =>
      simp only [store_undef_array_missing_i_rec, store_undef_array_rec]
      intro state hs
      rcases hs with hs | hs
      · have heq := hs.1
        change hi = lo at heq
        omega
      · exact sepcon_coq_false_elim CRules
          (CRules.exp ES.A fun a => ES.storeA x lo a)
          (CRules.andp (CRules.coq_prop (lo = hi - 1)) CRules.emp) state hs.2
  | succ n ih =>
      have hltTail : lo + 1 < hi := by omega
      have hnTail : n = (hi - ((lo + 1) + 1)).toNat := by omega
      simp only [store_undef_array_missing_i_rec, store_undef_array_rec]
      intro state hs
      rcases hs with hs | hs
      · have heq := hs.1
        change hi = lo at heq
        omega
      · exact (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_refl _)
          (ih (lo := lo + 1) hltTail hnTail)) state hs.2

theorem missing_i_shape_to_seg_shape_tail
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (h : lo < hi) :
    CRules.derivable1 (missing_i_shape ES x hi lo hi)
      (seg_shape ES x lo (hi - 1)) := by
  have hsource : (hi - lo).toNat = Nat.succ (hi - (lo + 1)).toNat := by omega
  have htarget : (hi - 1 - lo).toNat = (hi - (lo + 1)).toNat := by
    congr 1
    omega
  simp only [missing_i_shape, seg_shape, hsource, htarget]
  exact missing_i_shape_to_seg_shape_tail_rec ES x lo hi
    (hi - (lo + 1)).toNat h rfl

end SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib
