import SimpleC.SL.ArrayLibCore.Transitions

namespace SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open Unifysl.LogicGenerator.demo932

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : SimpleC.SL.StoreAux.StoreLibSig CRules DePredSig}

theorem seg_split_to_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo n m : Int) (l : List ES.A) (a : ES.A)
    (h : lo <= n ∧ n < m) :
    CRules.derivable1 (seg ES x lo m l)
      (CRules.sepcon (ES.storeA x n (Znth (n - lo) l a))
        (missing_i ES x n lo m l)) := by
  simpa only [seg, missing_i] using
    store_array_rec_split_to_missing_i CRules ES.A ES.storeA x lo n m l a h

theorem full_split_to_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (l : List ES.A) (a : ES.A)
    (h : 0 <= n ∧ n < m) :
    CRules.derivable1 (full ES x m l)
      (CRules.sepcon (ES.storeA x n (Znth n l a))
        (missing_i ES x n 0 m l)) := by
  simpa only [full, missing_i] using
    store_array_split_to_missing_i CRules ES.A ES.storeA x n m l a h

theorem mixed_seg_split_to_mixed_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo n m : Int) (l : List (Option ES.A)) (a : Option ES.A)
    (h : lo <= n ∧ n < m) :
    CRules.derivable1 (mixed_seg ES x lo m l)
      (CRules.sepcon (mixedstoreA ES x n (Znth (n - lo) l a))
        (mixed_missing_i ES x n lo m l)) := by
  simpa only [mixed_seg, mixed_missing_i] using
    store_array_rec_split_to_missing_i CRules (Option ES.A) (mixedstoreA ES)
      x lo n m l a h

theorem mixed_full_split_to_mixed_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (l : List (Option ES.A)) (a : Option ES.A)
    (h : 0 <= n ∧ n < m) :
    CRules.derivable1 (mixed_full ES x m l)
      (CRules.sepcon (mixedstoreA ES x n (Znth n l a))
        (mixed_missing_i ES x n 0 m l)) := by
  simpa only [mixed_full, mixed_missing_i] using
    store_array_split_to_missing_i CRules (Option ES.A) (mixedstoreA ES)
      x n m l a h

theorem missing_i_merge_to_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo n m : Int) (a : ES.A) (l : List ES.A)
    (h : lo <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (ES.storeA x n a) (missing_i ES x n lo m l))
      (seg ES x lo m (replace_Znth (n - lo) a l)) := by
  simpa only [missing_i, seg] using
    store_array_missing_i_merge_to_rec CRules ES.A ES.storeA
      x lo n m a l h

theorem missing_i_merge_to_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (a : ES.A) (l : List ES.A)
    (h : 0 <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (ES.storeA x n a) (missing_i ES x n 0 m l))
      (full ES x m (replace_Znth n a l)) := by
  simpa only [missing_i, full] using
    store_array_missing_i_merge_to_array CRules ES.A ES.storeA
      x n m a l h

theorem mixed_missing_i_merge_to_mixed_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo n m : Int) (a : Option ES.A) (l : List (Option ES.A))
    (h : lo <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (mixedstoreA ES x n a)
        (mixed_missing_i ES x n lo m l))
      (mixed_seg ES x lo m (replace_Znth (n - lo) a l)) := by
  simpa only [mixed_missing_i, mixed_seg] using
    store_array_missing_i_merge_to_rec CRules (Option ES.A) (mixedstoreA ES)
      x lo n m a l h

theorem mixed_missing_i_merge_to_mixed_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (a : Option ES.A) (l : List (Option ES.A))
    (h : 0 <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (mixedstoreA ES x n a)
        (mixed_missing_i ES x n 0 m l))
      (mixed_full ES x m (replace_Znth n a l)) := by
  simpa only [mixed_missing_i, mixed_full] using
    store_array_missing_i_merge_to_array CRules (Option ES.A) (mixedstoreA ES)
      x n m a l h

theorem undef_seg_split_to_undef_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo n m : Int) (h : lo <= n ∧ n < m) :
    CRules.derivable1 (undef_seg ES x lo m)
      (CRules.sepcon (ES.undefstoreA x n) (undef_missing_i ES x n lo m)) := by
  let values := List.replicate (m - lo).toNat (none : Option ES.A)
  have hSplit := mixed_seg_split_to_mixed_missing_i ES x lo n m values none h
  have hForget : CRules.derivable1
      (CRules.sepcon (mixedstoreA ES x n (Znth (n - lo) values none))
        (mixed_missing_i ES x n lo m values))
      (CRules.sepcon (ES.undefstoreA x n) (undef_missing_i ES x n lo m)) := by
    simpa only [values, Znth_repeat, mixedstoreA] using
      CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (CRules.toContext.derivable1_refl _)
        (mixed_missing_i_to_undef_missing_i ES x n lo m values)
  exact CRules.toContext.derivable1_trans _ _ _
    (undef_seg_to_mixed_seg ES x lo m)
    (CRules.toContext.derivable1_trans _ _ _ hSplit hForget)

theorem undef_full_split_to_undef_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (h : 0 <= n ∧ n < m) :
    CRules.derivable1 (undef_full ES x m)
      (CRules.sepcon (ES.undefstoreA x n) (undef_missing_i ES x n 0 m)) :=
  CRules.toContext.derivable1_trans _ _ _
    (undef_full_to_undef_seg ES x m)
    (undef_seg_split_to_undef_missing_i ES x 0 n m h)

theorem undef_missing_i_merge_to_undef_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo n m : Int) (h : lo <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (ES.undefstoreA x n) (undef_missing_i ES x n lo m))
      (undef_seg ES x lo m) := by
  let values := List.replicate (m - lo).toNat (none : Option ES.A)
  have hToMixed : CRules.derivable1
      (CRules.sepcon (ES.undefstoreA x n) (undef_missing_i ES x n lo m))
      (CRules.sepcon (mixedstoreA ES x n none)
        (mixed_missing_i ES x n lo m values)) :=
    CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (CRules.toContext.derivable1_refl _)
      (undef_missing_i_to_mixed_missing_i ES x n lo m)
  have hreplace : replace_Znth (n - lo) none values = values := by
    simpa only [values, Znth_repeat] using
      (replace_Znth_Znth (n - lo) values none)
  have hMerge := mixed_missing_i_merge_to_mixed_seg ES
    x lo n m none values h
  rw [hreplace] at hMerge
  exact CRules.toContext.derivable1_trans _ _ _ hToMixed <|
    CRules.toContext.derivable1_trans _ _ _ hMerge
      (mixed_seg_to_undef_seg ES x lo m values)

theorem undef_missing_i_merge_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (h : 0 <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (ES.undefstoreA x n) (undef_missing_i ES x n 0 m))
      (undef_full ES x m) := by
  have hMerge := CRules.toContext.derivable1_trans _ _ _
    (undef_missing_i_merge_to_undef_seg ES x 0 n m h)
    (undef_seg_to_undef_full ES x 0 m)
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hMerge

theorem mixed_seg_split_to_undef_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo n m : Int) (l : List (Option ES.A))
    (h : lo <= n ∧ n < m) :
    CRules.derivable1 (mixed_seg ES x lo m l)
      (CRules.sepcon (ES.undefstoreA x n) (undef_missing_i ES x n lo m)) :=
  CRules.toContext.derivable1_trans _ _ _
    (mixed_seg_to_undef_seg ES x lo m l)
    (undef_seg_split_to_undef_missing_i ES x lo n m h)

theorem mixed_full_split_to_undef_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (l : List (Option ES.A))
    (h : 0 <= n ∧ n < m) :
    CRules.derivable1 (mixed_full ES x m l)
      (CRules.sepcon (ES.undefstoreA x n) (undef_missing_i ES x n 0 m)) :=
  CRules.toContext.derivable1_trans _ _ _
    (mixed_full_to_undef_full ES x m l)
    (undef_full_split_to_undef_missing_i ES x n m h)

theorem mixed_missing_i_merge_to_undef_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo n m : Int) (a : Option ES.A) (l : List (Option ES.A))
    (h : lo <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (mixedstoreA ES x n a)
        (mixed_missing_i ES x n lo m l))
      (undef_seg ES x lo m) := by
  have hForget := CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (mixedstoreA_to_undefstoreA ES x n a)
    (mixed_missing_i_to_undef_missing_i ES x n lo m l)
  exact CRules.toContext.derivable1_trans _ _ _ hForget
    (undef_missing_i_merge_to_undef_seg ES x lo n m h)

theorem mixed_missing_i_merge_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (a : Option ES.A) (l : List (Option ES.A))
    (h : 0 <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (mixedstoreA ES x n a)
        (mixed_missing_i ES x n 0 m l))
      (undef_full ES x m) := by
  have hMerge := CRules.toContext.derivable1_trans _ _ _
    (mixed_missing_i_merge_to_undef_seg ES x 0 n m a l h)
    (undef_seg_to_undef_full ES x 0 m)
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hMerge

private def shapeElementStore
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) :
    ELEMENT_STORE CRules DePredSig SLibSig where
  A := Unit
  sizeA := ES.sizeA
  storeA := fun x i _ => CRules.exp ES.A fun a => ES.storeA x i a
  undefstoreA := fun x i => CRules.exp ES.A fun a => ES.storeA x i a
  store_to_undefstore := by
    intro x i _
    exact CRules.toContext.derivable1_refl _
  storeA_shift := by
    intro x n i _
    apply Automation.logic_equiv_exp_rule
    intro a
    exact ES.storeA_shift x n i a
  undefstoreA_shift := by
    intro x n i
    apply Automation.logic_equiv_exp_rule
    intro a
    exact ES.storeA_shift x n i a
  store_to_align := by
    intro x i _
    apply Automation.exp_left_rule
    intro a
    exact ES.store_to_align x i a
  undefstore_to_align := by
    intro x i
    apply Automation.exp_left_rule
    intro a
    exact ES.store_to_align x i a
  sizeA_valid := ES.sizeA_valid

theorem seg_shape_split_to_missing_i_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo n m : Int) (h : lo <= n ∧ n < m) :
    CRules.derivable1 (seg_shape ES x lo m)
      (CRules.exp ES.A fun a =>
        CRules.sepcon (ES.storeA x n a) (missing_i_shape ES x n lo m)) := by
  have hSplit := undef_seg_split_to_undef_missing_i
    (shapeElementStore ES) x lo n m h
  have hMove := (ex_logic_equiv_sepcon CRules
    (fun a => ES.storeA x n a) (missing_i_shape ES x n lo m)).left
  exact CRules.toContext.derivable1_trans _ _ _
    (by simpa only [seg_shape, undef_seg, shapeElementStore] using hSplit)
    hMove

theorem full_shape_split_to_missing_i_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (h : 0 <= n ∧ n < m) :
    CRules.derivable1 (full_shape ES x m)
      (CRules.exp ES.A fun a =>
        CRules.sepcon (ES.storeA x n a) (missing_i_shape ES x n 0 m)) :=
  CRules.toContext.derivable1_trans _ _ _
    (full_shape_to_seg_shape ES x m)
    (seg_shape_split_to_missing_i_shape ES x 0 n m h)

theorem missing_i_shape_merge_to_seg_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo n m : Int) (a : ES.A) (h : lo <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (ES.storeA x n a) (missing_i_shape ES x n lo m))
      (seg_shape ES x lo m) := by
  have hInject : CRules.derivable1 (ES.storeA x n a)
      (CRules.exp ES.A fun value => ES.storeA x n value) :=
    Automation.exp_right_rule a (CRules.toContext.derivable1_refl _)
  have hMerge := undef_missing_i_merge_to_undef_seg
    (shapeElementStore ES) x lo n m h
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _ hInject
      (CRules.toContext.derivable1_refl _))
    (by simpa only [missing_i_shape, undef_missing_i, seg_shape, undef_seg,
        shapeElementStore] using hMerge)

theorem missing_i_shape_merge_to_full_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (a : ES.A) (h : 0 <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (ES.storeA x n a) (missing_i_shape ES x n 0 m))
      (full_shape ES x m) := by
  have hMerge := CRules.toContext.derivable1_trans _ _ _
    (missing_i_shape_merge_to_seg_shape ES x 0 n m a h)
    (seg_shape_to_full_shape ES x 0 m)
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hMerge

theorem seg_split_to_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (l : List ES.A)
    (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1 (seg ES x lo hi l)
      (CRules.sepcon
        (seg ES x lo mid (sublist 0 (mid - lo) l))
        (seg ES x mid hi (sublist (mid - lo) (hi - lo) l))) := by
  letI : SacContext := ⟨CRules⟩
  induction l generalizing lo mid hi with
  | nil =>
      rw [Zsublist_of_nil, Zsublist_of_nil]
      simp only [seg, store_array_rec]
      apply coq_prop_andp_left
      intro hEnd
      apply coq_prop_andp_left
      intro _
      have hMid : mid = lo := by omega
      have hHi : hi = mid := by omega
      have hTrivial : CRules.derivable1 CRules.emp
          (CRules.andp (CRules.coq_prop True) CRules.emp) :=
        coq_prop_andp_right CRules True CRules.emp CRules.emp
          (CRules.toContext.derivable1_refl _) trivial
      have hLeft : CRules.derivable1 CRules.emp
          (CRules.andp (CRules.coq_prop (lo = mid))
            (CRules.andp (CRules.coq_prop True) CRules.emp)) :=
        coq_prop_andp_right CRules (lo = mid) _ CRules.emp hTrivial hMid.symm
      have hRight : CRules.derivable1 CRules.emp
          (CRules.andp (CRules.coq_prop (mid = hi))
            (CRules.andp (CRules.coq_prop True) CRules.emp)) :=
        coq_prop_andp_right CRules (mid = hi) _ CRules.emp hTrivial hHi.symm
      exact CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.derivable1_sepcon_emp_r CRules.emp)
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _ hLeft hRight)
  | cons a l ih =>
      simp only [seg, store_array_rec]
      refine CRules.toContext.derivable1_trans _
        (CRules.andp
          (CRules.coq_prop (Int.ofNat l.length = hi - (lo + 1)))
          (CRules.sepcon (ES.storeA x lo a) (seg ES x (lo + 1) hi l)))
        _ ?_ ?_
      · intro state hs
        rcases hs with ⟨s1, s2, hj, hHead, hTail⟩
        exact ⟨seg_length ES x (lo + 1) hi l s2 hTail,
          ⟨s1, s2, hj, hHead, hTail⟩⟩
      · apply coq_prop_andp_left
        intro hlen
        have hlenNonneg : 0 <= Int.ofNat l.length := Int.natCast_nonneg _
        by_cases hmid : mid < lo + 1
        · have hEq : mid = lo := by omega
          subst mid
          rw [show lo - lo = 0 by omega]
          rw [Zsublist_nil (a :: l) 0 0 (by omega)]
          rw [sublist_cons1 (hi - lo) a l (by omega)]
          simp only [seg, store_array_rec]
          rw [sublist_self l (hi - lo - 1) (by
            rw [Zlength_correct]
            omega)]
          have hEmpty1 : CRules.derivable1 CRules.emp
              (CRules.andp (CRules.coq_prop True) CRules.emp) :=
            coq_prop_andp_right CRules True CRules.emp CRules.emp
              (CRules.toContext.derivable1_refl _) trivial
          have hEmpty2 : CRules.derivable1 CRules.emp
              (CRules.andp (CRules.coq_prop True)
                (CRules.andp (CRules.coq_prop True) CRules.emp)) :=
            coq_prop_andp_right CRules True _ CRules.emp hEmpty1 trivial
          have hPre : CRules.derivable1
              (CRules.sepcon (ES.storeA x lo a)
                (store_array_rec CRules ES.storeA x (lo + 1) hi l))
              (CRules.sepcon CRules.emp
                (CRules.sepcon (ES.storeA x lo a)
                  (store_array_rec CRules ES.storeA x (lo + 1) hi l))) :=
            CRules.toContext.derivable1_trans _ _ _
              (CRules.toContext.derivable1_sepcon_emp_r _)
              (CRules.toContext.logic_equiv_sepcon_comm _ _).left
          exact CRules.toContext.derivable1_trans _ _ _
            hPre
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _ hEmpty2
              (CRules.toContext.derivable1_refl _))
        · rw [sublist_cons1 (mid - lo) a l (by omega)]
          rw [sublist_cons2 (mid - lo) (hi - lo) a l (by omega) (by
            rw [Zlength_cons, Zlength_correct]
            omega)]
          rw [show mid - lo - 1 = mid - (lo + 1) by omega]
          rw [show hi - lo - 1 = hi - (lo + 1) by omega]
          simp only [seg, store_array_rec]
          sep_apply (ih (lo := lo + 1) (mid := mid) (hi := hi) (by omega))
          exact CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.logic_equiv_sepcon_comm _ _).left
            (CRules.toContext.logic_equiv_sepcon_assoc _ _ _).left

private def mixedElementStore
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) :
    ELEMENT_STORE CRules DePredSig SLibSig where
  A := Option ES.A
  sizeA := ES.sizeA
  storeA := mixedstoreA ES
  undefstoreA := ES.undefstoreA
  store_to_undefstore := mixedstoreA_to_undefstoreA ES
  storeA_shift := mixedstoreA_shift ES
  undefstoreA_shift := ES.undefstoreA_shift
  store_to_align := by
    intro x i a
    exact CRules.toContext.derivable1_trans _ _ _
      (mixedstoreA_to_undefstoreA ES x i a)
      (ES.undefstore_to_align x i)
  undefstore_to_align := ES.undefstore_to_align
  sizeA_valid := ES.sizeA_valid

theorem mixed_seg_split_to_mixed_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (l : List (Option ES.A))
    (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1 (mixed_seg ES x lo hi l)
      (CRules.sepcon
        (mixed_seg ES x lo mid (sublist 0 (mid - lo) l))
        (mixed_seg ES x mid hi (sublist (mid - lo) (hi - lo) l))) := by
  simpa only [mixed_seg, seg, mixedElementStore] using
    seg_split_to_seg (mixedElementStore ES) x lo mid hi l h

private theorem store_undef_array_rec_split
    (storeA : addr -> Int -> CRules.expr)
    (x lo mid hi : Int) (n1 n2 : Nat)
    (h : lo <= mid ∧ mid <= hi)
    (hn1 : n1 = (mid - lo).toNat)
    (hn2 : n2 = (hi - mid).toNat) :
    CRules.derivable1
      (store_undef_array_rec CRules storeA x lo hi (n1 + n2))
      (CRules.sepcon
        (store_undef_array_rec CRules storeA x lo mid n1)
        (store_undef_array_rec CRules storeA x mid hi n2)) := by
  induction n1 generalizing lo mid hi with
  | zero =>
      have hEq : mid = lo := by omega
      subst mid
      simp only [Nat.zero_add, store_undef_array_rec]
      have hEmpty : CRules.derivable1 CRules.emp
          (CRules.andp (CRules.coq_prop True) CRules.emp) :=
        coq_prop_andp_right CRules True CRules.emp CRules.emp
          (CRules.toContext.derivable1_refl _) trivial
      have hPre : CRules.derivable1
          (store_undef_array_rec CRules storeA x lo hi n2)
          (CRules.sepcon CRules.emp
            (store_undef_array_rec CRules storeA x lo hi n2)) :=
        CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.derivable1_sepcon_emp_r _)
          (CRules.toContext.logic_equiv_sepcon_comm _ _).left
      exact CRules.toContext.derivable1_trans _ _ _ hPre
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _ hEmpty
          (CRules.toContext.derivable1_refl _))
  | succ n ih =>
      have hn1' : n = (mid - (lo + 1)).toNat := by omega
      simp only [Nat.succ_add, store_undef_array_rec]
      have hTail := ih (lo := lo + 1) (mid := mid) (hi := hi)
        (by omega) hn1' hn2
      exact CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_refl _) hTail)
        (CRules.toContext.logic_equiv_sepcon_assoc _ _ _).left

theorem undef_seg_split_to_undef_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1 (undef_seg ES x lo hi)
      (CRules.sepcon (undef_seg ES x lo mid) (undef_seg ES x mid hi)) := by
  let n1 := (mid - lo).toNat
  let n2 := (hi - mid).toNat
  have hsum : (hi - lo).toNat = n1 + n2 := by
    simp only [n1, n2]
    omega
  simp only [undef_seg, hsum]
  exact store_undef_array_rec_split ES.undefstoreA x lo mid hi n1 n2 h
    (by simp only [n1]) (by simp only [n2])

theorem seg_shape_split_to_seg_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1 (seg_shape ES x lo hi)
      (CRules.sepcon (seg_shape ES x lo mid) (seg_shape ES x mid hi)) := by
  simpa only [seg_shape, undef_seg, shapeElementStore] using
    undef_seg_split_to_undef_seg (shapeElementStore ES) x lo mid hi h

theorem full_split_to_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (l : List ES.A) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1 (full ES x m l)
      (CRules.sepcon
        (seg ES x 0 n (sublist 0 n l))
        (seg ES x n m (sublist n m l))) := by
  have hSplit := CRules.toContext.derivable1_trans _ _ _
    (full_to_seg ES x m l) (seg_split_to_seg ES x 0 n m l h)
  simpa only [Int.sub_zero] using hSplit

theorem mixed_full_split_to_mixed_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (l : List (Option ES.A)) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1 (mixed_full ES x m l)
      (CRules.sepcon
        (mixed_seg ES x 0 n (sublist 0 n l))
        (mixed_seg ES x n m (sublist n m l))) := by
  have hSplit := CRules.toContext.derivable1_trans _ _ _
    (mixed_full_to_mixed_seg ES x m l)
    (mixed_seg_split_to_mixed_seg ES x 0 n m l h)
  simpa only [Int.sub_zero] using hSplit

theorem full_split_to_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (l : List ES.A) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1 (full ES x m l)
      (CRules.sepcon
        (full ES x n (sublist 0 n l))
        (full ES (x + n * ES.sizeA) (m - n) (sublist n m l))) := by
  have hConvert := CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (seg_to_full ES x 0 n (sublist 0 n l))
    (seg_to_full ES x n m (sublist n m l))
  have hResult := CRules.toContext.derivable1_trans _ _ _
    (full_split_to_seg ES x n m l h) hConvert
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hResult

theorem mixed_full_split_to_mixed_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (l : List (Option ES.A)) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1 (mixed_full ES x m l)
      (CRules.sepcon
        (mixed_full ES x n (sublist 0 n l))
        (mixed_full ES (x + n * ES.sizeA) (m - n) (sublist n m l))) := by
  have hConvert := CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (mixed_seg_to_mixed_full ES x 0 n (sublist 0 n l))
    (mixed_seg_to_mixed_full ES x n m (sublist n m l))
  have hResult := CRules.toContext.derivable1_trans _ _ _
    (mixed_full_split_to_mixed_seg ES x n m l h) hConvert
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hResult

theorem undef_full_split_to_undef_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1 (undef_full ES x m)
      (CRules.sepcon (undef_seg ES x 0 n) (undef_seg ES x n m)) :=
  CRules.toContext.derivable1_trans _ _ _
    (undef_full_to_undef_seg ES x m)
    (undef_seg_split_to_undef_seg ES x 0 n m h)

theorem undef_full_split_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1 (undef_full ES x m)
      (CRules.sepcon (undef_full ES x n)
        (undef_full ES (x + n * ES.sizeA) (m - n))) := by
  have hConvert := CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (undef_seg_to_undef_full ES x 0 n)
    (undef_seg_to_undef_full ES x n m)
  have hResult := CRules.toContext.derivable1_trans _ _ _
    (undef_full_split_to_undef_seg ES x n m h) hConvert
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hResult

theorem full_shape_split_to_seg_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1 (full_shape ES x m)
      (CRules.sepcon (seg_shape ES x 0 n) (seg_shape ES x n m)) :=
  CRules.toContext.derivable1_trans _ _ _
    (full_shape_to_seg_shape ES x m)
    (seg_shape_split_to_seg_shape ES x 0 n m h)

theorem full_shape_split_to_full_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1 (full_shape ES x m)
      (CRules.sepcon (full_shape ES x n)
        (full_shape ES (x + n * ES.sizeA) (m - n))) := by
  have hConvert := CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (seg_shape_to_full_shape ES x 0 n)
    (seg_shape_to_full_shape ES x n m)
  have hResult := CRules.toContext.derivable1_trans _ _ _
    (full_shape_split_to_seg_shape ES x n m h) hConvert
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hResult

theorem seg_merge_to_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (l1 l2 : List ES.A)
    (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1
      (CRules.sepcon (seg ES x lo mid l1) (seg ES x mid hi l2))
      (seg ES x lo hi (l1 ++ l2)) := by
  induction l1 generalizing lo mid hi with
  | nil =>
      simp only [List.nil_append, seg, store_array_rec]
      intro state hs
      rcases hs with ⟨s1, s2, hj, hEmpty, hRight⟩
      have hEq : lo = mid := hEmpty.1
      subst mid
      have hDrop : CRules.derivable1
          (CRules.sepcon CRules.emp
            (store_array_rec CRules ES.storeA x lo hi l2))
          (store_array_rec CRules ES.storeA x lo hi l2) :=
        CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.logic_equiv_sepcon_comm _ _).left
          (CRules.toContext.derivable1_sepcon_emp_l _)
      exact hDrop state ⟨s1, s2, hj, hEmpty.2.2, hRight⟩
  | cons a l ih =>
      simp only [List.cons_append, seg, store_array_rec]
      let source := CRules.sepcon
        (CRules.sepcon (ES.storeA x lo a)
          (store_array_rec CRules ES.storeA x (lo + 1) mid l))
        (store_array_rec CRules ES.storeA x mid hi l2)
      refine CRules.toContext.derivable1_trans source
        (CRules.andp
          (CRules.coq_prop (Int.ofNat l.length = mid - (lo + 1))) source)
        _ ?_ ?_
      · intro state hs
        rcases hs with ⟨s12, s3, hjOuter, hLeft, hThird⟩
        rcases hLeft with ⟨s1, s2, hjInner, hHead, hTail⟩
        exact ⟨seg_length ES x (lo + 1) mid l s2 hTail,
          ⟨s12, s3, hjOuter, ⟨s1, s2, hjInner, hHead, hTail⟩, hThird⟩⟩
      · apply coq_prop_andp_left
        intro hlen
        have hlenNonneg : 0 <= Int.ofNat l.length := Int.natCast_nonneg _
        have hTailBounds : lo + 1 <= mid ∧ mid <= hi := by omega
        have hMerge := ih (lo := lo + 1) (mid := mid) (hi := hi)
          hTailBounds
        exact CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.logic_equiv_sepcon_assoc _ _ _).right
          (CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (CRules.toContext.derivable1_refl _) hMerge)

theorem mixed_seg_merge_to_mixed_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (l1 l2 : List (Option ES.A))
    (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1
      (CRules.sepcon (mixed_seg ES x lo mid l1)
        (mixed_seg ES x mid hi l2))
      (mixed_seg ES x lo hi (l1 ++ l2)) := by
  simpa only [mixed_seg, seg, mixedElementStore] using
    seg_merge_to_seg (mixedElementStore ES) x lo mid hi l1 l2 h

private theorem store_undef_array_rec_merge
    (storeA : addr -> Int -> CRules.expr)
    (x lo mid hi : Int) (n1 n2 : Nat)
    (h : lo <= mid ∧ mid <= hi)
    (hn1 : n1 = (mid - lo).toNat)
    (hn2 : n2 = (hi - mid).toNat) :
    CRules.derivable1
      (CRules.sepcon
        (store_undef_array_rec CRules storeA x lo mid n1)
        (store_undef_array_rec CRules storeA x mid hi n2))
      (store_undef_array_rec CRules storeA x lo hi (n1 + n2)) := by
  induction n1 generalizing lo mid hi with
  | zero =>
      have hEq : mid = lo := by omega
      subst mid
      simp only [Nat.zero_add, store_undef_array_rec]
      intro state hs
      rcases hs with ⟨s1, s2, hj, hEmpty, hRight⟩
      have hDrop : CRules.derivable1
          (CRules.sepcon CRules.emp
            (store_undef_array_rec CRules storeA x lo hi n2))
          (store_undef_array_rec CRules storeA x lo hi n2) :=
        CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.logic_equiv_sepcon_comm _ _).left
          (CRules.toContext.derivable1_sepcon_emp_l _)
      exact hDrop state ⟨s1, s2, hj, hEmpty.2, hRight⟩
  | succ n ih =>
      have hn1' : n = (mid - (lo + 1)).toNat := by omega
      simp only [Nat.succ_add, store_undef_array_rec]
      have hTail := ih (lo := lo + 1) (mid := mid) (hi := hi)
        (by omega) hn1' hn2
      exact CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.logic_equiv_sepcon_assoc _ _ _).right
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_refl _) hTail)

theorem undef_seg_merge_to_undef_seg
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1
      (CRules.sepcon (undef_seg ES x lo mid) (undef_seg ES x mid hi))
      (undef_seg ES x lo hi) := by
  let n1 := (mid - lo).toNat
  let n2 := (hi - mid).toNat
  have hsum : (hi - lo).toNat = n1 + n2 := by
    simp only [n1, n2]
    omega
  simp only [undef_seg, hsum]
  exact store_undef_array_rec_merge ES.undefstoreA x lo mid hi n1 n2 h
    (by simp only [n1]) (by simp only [n2])

theorem seg_shape_merge_to_seg_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1
      (CRules.sepcon (seg_shape ES x lo mid) (seg_shape ES x mid hi))
      (seg_shape ES x lo hi) := by
  simpa only [seg_shape, undef_seg, shapeElementStore] using
    undef_seg_merge_to_undef_seg (shapeElementStore ES) x lo mid hi h

theorem seg_merge_to_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (l1 l2 : List ES.A)
    (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1
      (CRules.sepcon (seg ES x lo mid l1) (seg ES x mid hi l2))
      (full ES (x + lo * ES.sizeA) (hi - lo) (l1 ++ l2)) :=
  CRules.toContext.derivable1_trans _ _ _
    (seg_merge_to_seg ES x lo mid hi l1 l2 h)
    (seg_to_full ES x lo hi (l1 ++ l2))

theorem mixed_seg_merge_to_mixed_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (l1 l2 : List (Option ES.A))
    (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1
      (CRules.sepcon (mixed_seg ES x lo mid l1)
        (mixed_seg ES x mid hi l2))
      (mixed_full ES (x + lo * ES.sizeA) (hi - lo) (l1 ++ l2)) :=
  CRules.toContext.derivable1_trans _ _ _
    (mixed_seg_merge_to_mixed_seg ES x lo mid hi l1 l2 h)
    (mixed_seg_to_mixed_full ES x lo hi (l1 ++ l2))

theorem undef_seg_merge_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1
      (CRules.sepcon (undef_seg ES x lo mid) (undef_seg ES x mid hi))
      (undef_full ES (x + lo * ES.sizeA) (hi - lo)) :=
  CRules.toContext.derivable1_trans _ _ _
    (undef_seg_merge_to_undef_seg ES x lo mid hi h)
    (undef_seg_to_undef_full ES x lo hi)

theorem seg_shape_merge_to_full_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo mid hi : Int) (h : lo <= mid ∧ mid <= hi) :
    CRules.derivable1
      (CRules.sepcon (seg_shape ES x lo mid) (seg_shape ES x mid hi))
      (full_shape ES (x + lo * ES.sizeA) (hi - lo)) :=
  CRules.toContext.derivable1_trans _ _ _
    (seg_shape_merge_to_seg_shape ES x lo mid hi h)
    (seg_shape_to_full_shape ES x lo hi)

theorem full_merge_to_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (l1 l2 : List ES.A) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1
      (CRules.sepcon (full ES x n l1)
        (full ES (x + n * ES.sizeA) (m - n) l2))
      (full ES x m (l1 ++ l2)) := by
  have hSecondShift := (seg_shift ES x n 0 (m - n) l2).right
  rw [show n + 0 = n by omega, show n + (m - n) = m by omega] at hSecondShift
  have hSecond := CRules.toContext.derivable1_trans _ _ _
    (full_to_seg ES (x + n * ES.sizeA) (m - n) l2) hSecondShift
  have hPrepare := CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (full_to_seg ES x n l1) hSecond
  have hResult := CRules.toContext.derivable1_trans _ _ _ hPrepare
    (seg_merge_to_full ES x 0 n m l1 l2 h)
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hResult

theorem mixed_full_merge_to_mixed_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (l1 l2 : List (Option ES.A))
    (h : 0 <= n ∧ n <= m) :
    CRules.derivable1
      (CRules.sepcon (mixed_full ES x n l1)
        (mixed_full ES (x + n * ES.sizeA) (m - n) l2))
      (mixed_full ES x m (l1 ++ l2)) := by
  have hSecondShift := (mixed_seg_shift ES x n 0 (m - n) l2).right
  rw [show n + 0 = n by omega, show n + (m - n) = m by omega] at hSecondShift
  have hSecond := CRules.toContext.derivable1_trans _ _ _
    (mixed_full_to_mixed_seg ES (x + n * ES.sizeA) (m - n) l2)
    hSecondShift
  have hPrepare := CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (mixed_full_to_mixed_seg ES x n l1) hSecond
  have hResult := CRules.toContext.derivable1_trans _ _ _ hPrepare
    (mixed_seg_merge_to_mixed_full ES x 0 n m l1 l2 h)
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hResult

theorem undef_full_merge_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1
      (CRules.sepcon (undef_full ES x n)
        (undef_full ES (x + n * ES.sizeA) (m - n)))
      (undef_full ES x m) := by
  have hSecondShift := (undef_seg_shift ES x n 0 (m - n)).right
  rw [show n + 0 = n by omega, show n + (m - n) = m by omega] at hSecondShift
  have hSecond := CRules.toContext.derivable1_trans _ _ _
    (undef_full_to_undef_seg ES (x + n * ES.sizeA) (m - n)) hSecondShift
  have hPrepare := CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (undef_full_to_undef_seg ES x n) hSecond
  have hResult := CRules.toContext.derivable1_trans _ _ _ hPrepare
    (undef_seg_merge_to_undef_full ES x 0 n m h)
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hResult

theorem full_shape_merge_to_full_shape
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (h : 0 <= n ∧ n <= m) :
    CRules.derivable1
      (CRules.sepcon (full_shape ES x n)
        (full_shape ES (x + n * ES.sizeA) (m - n)))
      (full_shape ES x m) := by
  have hSecondShift := (seg_shape_shift ES x n 0 (m - n)).right
  rw [show n + 0 = n by omega, show n + (m - n) = m by omega] at hSecondShift
  have hSecond := CRules.toContext.derivable1_trans _ _ _
    (full_shape_to_seg_shape ES (x + n * ES.sizeA) (m - n)) hSecondShift
  have hPrepare := CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (full_shape_to_seg_shape ES x n) hSecond
  have hResult := CRules.toContext.derivable1_trans _ _ _ hPrepare
    (seg_shape_merge_to_full_shape ES x 0 n m h)
  simpa only [Int.zero_mul, Int.add_zero, Int.sub_zero] using hResult

end SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib
