import SimpleC.SL.ArrayLibCore.General

namespace SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open Unifysl.LogicGenerator.demo932

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : SimpleC.SL.StoreAux.StoreLibSig CRules DePredSig}

private theorem emp_to_array_tail (CRules : SeparationLogicSig) :
    CRules.derivable1 CRules.emp
      (CRules.andp (CRules.coq_prop True)
        (CRules.andp (CRules.coq_prop True) CRules.emp)) := by
  intro _ hs
  exact ⟨trivial, trivial, hs⟩

private theorem singleton_tail (CRules : SeparationLogicSig) (P : CRules.expr) :
    CRules.derivable1 P
      (CRules.sepcon P
        (CRules.andp (CRules.coq_prop True)
          (CRules.andp (CRules.coq_prop True) CRules.emp))) :=
  CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_emp_r P)
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (CRules.toContext.derivable1_refl P) (emp_to_array_tail CRules))

private theorem exists_singleton_tail (CRules : SeparationLogicSig)
    {A : Type} (storeA : A -> CRules.expr) (a : A) :
    CRules.derivable1 (storeA a)
      (CRules.sepcon (CRules.exp A storeA)
        (CRules.andp (CRules.coq_prop True)
          (CRules.andp (CRules.coq_prop True) CRules.emp))) :=
  CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_emp_r (storeA a))
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (Automation.exp_right_rule a (CRules.toContext.derivable1_refl _))
      (emp_to_array_tail CRules))

private theorem emp_to_undef_tail (CRules : SeparationLogicSig) :
    CRules.derivable1 CRules.emp
      (CRules.andp (CRules.coq_prop True) CRules.emp) := by
  intro _ hs
  exact ⟨trivial, hs⟩

private theorem undef_singleton_tail (CRules : SeparationLogicSig)
    (P : CRules.expr) :
    CRules.derivable1 P
      (CRules.sepcon P (CRules.andp (CRules.coq_prop True) CRules.emp)) :=
  CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_emp_r P)
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (CRules.toContext.derivable1_refl P) (emp_to_undef_tail CRules))

private theorem exists_undef_singleton_tail (CRules : SeparationLogicSig)
    {A : Type} (storeA : A -> CRules.expr) (a : A) :
    CRules.derivable1 (storeA a)
      (CRules.sepcon (CRules.exp A storeA)
        (CRules.andp (CRules.coq_prop True) CRules.emp)) :=
  CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_emp_r (storeA a))
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (Automation.exp_right_rule a (CRules.toContext.derivable1_refl _))
      (emp_to_undef_tail CRules))

theorem mixedstoreA_to_undefstoreA
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x lo : Int)
    (a : Option ES.A) :
    CRules.derivable1 (mixedstoreA ES x lo a) (ES.undefstoreA x lo) := by
  cases a with
  | none => exact CRules.toContext.derivable1_refl _
  | some value => exact ES.store_to_undefstore x lo value

theorem mixedstoreA_shift
    (ES : ELEMENT_STORE CRules DePredSig SLibSig) (x n lo : Int)
    (a : Option ES.A) :
    CRules.logic_equiv
      (mixedstoreA ES (x + n * ES.sizeA) lo a)
      (mixedstoreA ES x (lo + n) a) := by
  cases a with
  | none => exact ES.undefstoreA_shift x n lo
  | some value => exact ES.storeA_shift x n lo value

theorem seg_length (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (seg ES x lo hi l)
      (CRules.coq_prop (Int.ofNat l.length = hi - lo)) := by
  simpa [seg] using
    store_array_rec_length CRules ES.A ES.storeA x lo hi l

theorem seg_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (seg ES x lo hi l)
      (CRules.coq_prop (Zlength l = hi - lo)) := by
  simpa [seg] using
    store_array_rec_Zlength CRules ES.A ES.storeA x lo hi l

theorem seg_nil (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo : Int) (l : List ES.A) :
    CRules.derivable1 (seg ES x lo lo l)
      (CRules.andp (CRules.coq_prop (l = [])) CRules.emp) := by
  simpa [seg] using store_array_rec_nil CRules ES.A ES.storeA x lo l

theorem seg_single (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo : Int) (a : ES.A) :
    CRules.derivable1 (ES.storeA x lo a) (seg ES x lo (lo + 1) [a]) := by
  simpa [seg, store_array_rec] using singleton_tail CRules (ES.storeA x lo a)

theorem mixed_seg_single (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo : Int) (a : Option ES.A) :
    CRules.derivable1 (mixedstoreA ES x lo a)
      (mixed_seg ES x lo (lo + 1) [a]) := by
  simpa [mixed_seg, store_array_rec] using
    singleton_tail CRules (mixedstoreA ES x lo a)

theorem undef_seg_single (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo : Int) :
    CRules.derivable1 (ES.undefstoreA x lo) (undef_seg ES x lo (lo + 1)) := by
  have hcount : (lo + 1 - lo).toNat = 1 := by omega
  simp only [undef_seg, hcount, store_undef_array_rec]
  exact undef_singleton_tail CRules (ES.undefstoreA x lo)

theorem seg_shape_single (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo : Int) (a : ES.A) :
    CRules.derivable1 (ES.storeA x lo a) (seg_shape ES x lo (lo + 1)) := by
  have hcount : (lo + 1 - lo).toNat = 1 := by omega
  simp only [seg_shape, hcount, store_undef_array_rec]
  exact exists_undef_singleton_tail CRules (fun value => ES.storeA x lo value) a

theorem full_length (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) :
    CRules.derivable1 (full ES x n l)
      (CRules.coq_prop (Int.ofNat l.length = n)) := by
  simpa [full] using store_array_length CRules ES.A ES.storeA x n l

theorem full_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) :
    CRules.derivable1 (full ES x n l)
      (CRules.coq_prop (Zlength l = n)) := by
  simpa [full] using store_array_Zlength CRules ES.A ES.storeA x n l

theorem mixed_seg_length (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_seg ES x lo hi l)
      (CRules.coq_prop (Int.ofNat l.length = hi - lo)) := by
  simpa [mixed_seg] using
    store_array_rec_length CRules (Option ES.A) (mixedstoreA ES) x lo hi l

theorem mixed_seg_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_seg ES x lo hi l)
      (CRules.coq_prop (Zlength l = hi - lo)) := by
  simpa [mixed_seg] using
    store_array_rec_Zlength CRules (Option ES.A) (mixedstoreA ES) x lo hi l

theorem mixed_seg_nil (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_seg ES x lo lo l)
      (CRules.andp (CRules.coq_prop (l = [])) CRules.emp) := by
  simpa [mixed_seg] using
    store_array_rec_nil CRules (Option ES.A) (mixedstoreA ES) x lo l

theorem mixed_full_length (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_full ES x n l)
      (CRules.coq_prop (Int.ofNat l.length = n)) := by
  simpa [mixed_full] using
    store_array_length CRules (Option ES.A) (mixedstoreA ES) x n l

theorem mixed_full_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_full ES x n l)
      (CRules.coq_prop (Zlength l = n)) := by
  simpa [mixed_full] using
    store_array_Zlength CRules (Option ES.A) (mixedstoreA ES) x n l

theorem mixed_missing_i_length (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_missing_i ES x i lo hi l)
      (CRules.coq_prop (Int.ofNat l.length = hi - lo)) := by
  simpa [mixed_missing_i] using
    store_array_missing_i_rec_length CRules (Option ES.A) (mixedstoreA ES)
      x i lo hi l

theorem mixed_missing_i_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_missing_i ES x i lo hi l)
      (CRules.coq_prop (Zlength l = hi - lo)) := by
  simpa [mixed_missing_i] using
    store_array_missing_i_rec_Zlength CRules (Option ES.A) (mixedstoreA ES)
      x i lo hi l

theorem missing_i_length (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (missing_i ES x i lo hi l)
      (CRules.coq_prop (Int.ofNat l.length = hi - lo)) := by
  simpa [missing_i] using
    store_array_missing_i_rec_length CRules ES.A ES.storeA x i lo hi l

theorem missing_i_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (missing_i ES x i lo hi l)
      (CRules.coq_prop (Zlength l = hi - lo)) := by
  simpa [missing_i] using
    store_array_missing_i_rec_Zlength CRules ES.A ES.storeA x i lo hi l

theorem seg_valid (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) :
    CRules.derivable1 (seg ES x lo hi l) (CRules.coq_prop (lo <= hi)) := by
  simpa [seg] using store_array_rec_valid CRules ES.A ES.storeA x lo hi l

theorem mixed_seg_valid (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A)) :
    CRules.derivable1 (mixed_seg ES x lo hi l)
      (CRules.coq_prop (lo <= hi)) := by
  simpa [mixed_seg] using
    store_array_rec_valid CRules (Option ES.A) (mixedstoreA ES) x lo hi l

theorem undef_seg_valid (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) :
    CRules.derivable1 (undef_seg ES x lo hi) (CRules.coq_prop (lo <= hi)) := by
  intro state hs
  change lo <= hi
  by_cases hle : lo <= hi
  · exact hle
  · have hzero : (hi - lo).toNat = 0 := by omega
    simp only [undef_seg, hzero, store_undef_array_rec] at hs
    change lo = hi ∧ _ at hs
    omega

theorem seg_shape_valid (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) :
    CRules.derivable1 (seg_shape ES x lo hi) (CRules.coq_prop (lo <= hi)) := by
  intro state hs
  change lo <= hi
  by_cases hle : lo <= hi
  · exact hle
  · have hzero : (hi - lo).toNat = 0 := by omega
    simp only [seg_shape, hzero, store_undef_array_rec] at hs
    change lo = hi ∧ _ at hs
    omega

theorem seg_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) :
    CRules.logic_equiv (seg ES x lo hi [])
      (CRules.andp (CRules.coq_prop (hi = lo)) CRules.emp) := by
  simp only [seg, store_array_rec]
  constructor
  · intro _ hs
    exact ⟨hs.1.symm, hs.2.2⟩
  · intro _ hs
    exact ⟨hs.1.symm, trivial, hs.2⟩

theorem mixed_seg_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) :
    CRules.logic_equiv (mixed_seg ES x lo hi [])
      (CRules.andp (CRules.coq_prop (hi = lo)) CRules.emp) := by
  simp only [mixed_seg, store_array_rec]
  constructor
  · intro _ hs
    exact ⟨hs.1.symm, hs.2.2⟩
  · intro _ hs
    exact ⟨hs.1.symm, trivial, hs.2⟩

theorem undef_seg_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo : Int) : CRules.logic_equiv (undef_seg ES x lo lo) CRules.emp := by
  have hzero : (lo - lo).toNat = 0 := by omega
  simp only [undef_seg, hzero, store_undef_array_rec]
  constructor
  · intro _ hs
    exact hs.2
  · intro _ hs
    exact ⟨trivial, hs⟩

theorem seg_shape_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo : Int) : CRules.logic_equiv (seg_shape ES x lo lo) CRules.emp := by
  have hzero : (lo - lo).toNat = 0 := by omega
  simp only [seg_shape, hzero, store_undef_array_rec]
  constructor
  · intro _ hs
    exact hs.2
  · intro _ hs
    exact ⟨trivial, hs⟩

theorem seg_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List ES.A) (a : ES.A) :
    CRules.logic_equiv (seg ES x lo hi (a :: l))
      (CRules.sepcon (ES.storeA x lo a) (seg ES x (lo + 1) hi l)) := by
  exact CRules.toContext.logic_equiv_refl _

theorem mixed_seg_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (l : List (Option ES.A)) (a : Option ES.A) :
    CRules.logic_equiv (mixed_seg ES x lo hi (a :: l))
      (CRules.sepcon (mixedstoreA ES x lo a)
        (mixed_seg ES x (lo + 1) hi l)) := by
  exact CRules.toContext.logic_equiv_refl _

theorem undef_seg_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (h : lo < hi) :
    CRules.logic_equiv (undef_seg ES x lo hi)
      (CRules.sepcon (ES.undefstoreA x lo) (undef_seg ES x (lo + 1) hi)) := by
  have hcount : (hi - lo).toNat = (hi - (lo + 1)).toNat + 1 := by omega
  unfold undef_seg
  rw [hcount]
  exact CRules.toContext.logic_equiv_refl _

theorem seg_shape_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x lo hi : Int) (h : lo < hi) :
    CRules.logic_equiv (seg_shape ES x lo hi)
      (CRules.exp ES.A fun a =>
        CRules.sepcon (ES.storeA x lo a) (seg_shape ES x (lo + 1) hi)) := by
  have hcount : (hi - lo).toNat = (hi - (lo + 1)).toNat + 1 := by omega
  unfold seg_shape
  rw [hcount]
  exact ex_logic_equiv_sepcon CRules
    (fun a => ES.storeA x lo a)
    (store_undef_array_rec CRules
      (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
      x (lo + 1) hi (hi - (lo + 1)).toNat)

theorem missing_i_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) :
    CRules.logic_equiv (missing_i ES x i lo hi []) (CRules.coq_prop False) :=
  CRules.toContext.logic_equiv_refl _

theorem mixed_missing_i_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) :
    CRules.logic_equiv (mixed_missing_i ES x i lo hi [])
      (CRules.coq_prop False) :=
  CRules.toContext.logic_equiv_refl _

theorem undef_missing_i_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo : Int) :
    CRules.derivable1 (undef_missing_i ES x i lo lo) (CRules.coq_prop False) := by
  have hzero : (lo - lo).toNat = 0 := by omega
  simp only [undef_missing_i, hzero, store_undef_array_missing_i_rec]
  exact CRules.toContext.derivable1_refl _

theorem missing_i_shape_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo : Int) :
    CRules.logic_equiv (missing_i_shape ES x i lo lo)
      (CRules.coq_prop False) := by
  have hzero : (lo - lo).toNat = 0 := by omega
  simp only [missing_i_shape, hzero, store_undef_array_missing_i_rec]
  exact CRules.toContext.logic_equiv_refl _

theorem missing_i_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List ES.A) (a : ES.A) :
    CRules.logic_equiv (missing_i ES x i lo hi (a :: l))
      (CRules.orp
        (CRules.andp (CRules.coq_prop (i = lo)) (seg ES x (lo + 1) hi l))
        (CRules.andp (CRules.coq_prop (i > lo))
          (CRules.sepcon (ES.storeA x lo a)
            (missing_i ES x i (lo + 1) hi l)))) :=
  CRules.toContext.logic_equiv_refl _

theorem mixed_missing_i_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (l : List (Option ES.A)) (a : Option ES.A) :
    CRules.logic_equiv (mixed_missing_i ES x i lo hi (a :: l))
      (CRules.orp
        (CRules.andp (CRules.coq_prop (i = lo))
          (mixed_seg ES x (lo + 1) hi l))
        (CRules.andp (CRules.coq_prop (i > lo))
          (CRules.sepcon (mixedstoreA ES x lo a)
            (mixed_missing_i ES x i (lo + 1) hi l)))) :=
  CRules.toContext.logic_equiv_refl _

theorem undef_missing_i_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (h : lo < hi) :
    CRules.logic_equiv (undef_missing_i ES x i lo hi)
      (CRules.orp
        (CRules.andp (CRules.coq_prop (i = lo)) (undef_seg ES x (lo + 1) hi))
        (CRules.andp (CRules.coq_prop (i > lo))
          (CRules.sepcon (ES.undefstoreA x lo)
            (undef_missing_i ES x i (lo + 1) hi)))) := by
  have hcount : (hi - lo).toNat = (hi - (lo + 1)).toNat + 1 := by omega
  unfold undef_missing_i undef_seg
  rw [hcount]
  exact CRules.toContext.logic_equiv_refl _

theorem missing_i_shape_unfold
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi : Int) (h : lo < hi) :
    CRules.logic_equiv (missing_i_shape ES x i lo hi)
      (CRules.orp
        (CRules.andp (CRules.coq_prop (i = lo)) (seg_shape ES x (lo + 1) hi))
        (CRules.andp (CRules.coq_prop (i > lo))
          (CRules.sepcon (CRules.exp ES.A fun a => ES.storeA x lo a)
            (missing_i_shape ES x i (lo + 1) hi)))) := by
  have hcount : (hi - lo).toNat = (hi - (lo + 1)).toNat + 1 := by omega
  unfold missing_i_shape seg_shape
  rw [hcount]
  exact CRules.toContext.logic_equiv_refl _

theorem full_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) :
    CRules.logic_equiv (full ES x n [])
      (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp) := by
  simpa [full, store_array] using seg_empty ES x 0 n

theorem mixed_full_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) :
    CRules.logic_equiv (mixed_full ES x n [])
      (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp) := by
  simpa [mixed_full, store_array] using mixed_seg_empty ES x 0 n

theorem undef_full_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : Int) : CRules.logic_equiv (undef_full ES x 0) CRules.emp := by
  simpa [undef_full, store_undef_array] using undef_seg_empty ES x 0

theorem full_shape_empty (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : Int) : CRules.logic_equiv (full_shape ES x 0) CRules.emp := by
  simpa [full_shape, store_undef_array] using seg_shape_empty ES x 0

theorem full_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List ES.A) (a : ES.A) :
    CRules.logic_equiv (full ES x n (a :: l))
      (CRules.sepcon (ES.storeA x 0 a) (seg ES x 1 n l)) :=
  CRules.toContext.logic_equiv_refl _

theorem mixed_full_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (l : List (Option ES.A)) (a : Option ES.A) :
    CRules.logic_equiv (mixed_full ES x n (a :: l))
      (CRules.sepcon (mixedstoreA ES x 0 a) (mixed_seg ES x 1 n l)) :=
  CRules.toContext.logic_equiv_refl _

theorem undef_full_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (_l : List ES.A) (h : n >= 0) :
    CRules.logic_equiv (undef_full ES x (n + 1))
      (CRules.sepcon (ES.undefstoreA x 0) (undef_seg ES x 1 (n + 1))) := by
  have hcount : (n + 1).toNat = n.toNat + 1 := by omega
  have htail : (n + 1 - 1).toNat = n.toNat := by omega
  unfold undef_full store_undef_array undef_seg
  rw [hcount, htail]
  exact CRules.toContext.logic_equiv_refl _

theorem full_shape_unfold (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (_l : List ES.A) (h : n >= 0) :
    CRules.logic_equiv (full_shape ES x (n + 1))
      (CRules.exp ES.A fun a =>
        CRules.sepcon (ES.storeA x 0 a) (seg_shape ES x 1 (n + 1))) := by
  have hcount : (n + 1).toNat = n.toNat + 1 := by omega
  have htail : (n + 1 - 1).toNat = n.toNat := by omega
  unfold full_shape store_undef_array seg_shape
  rw [hcount, htail]
  exact ex_logic_equiv_sepcon CRules
    (fun a => ES.storeA x 0 a)
    (store_undef_array_rec CRules
      (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
      x 1 (n + 1) n.toNat)

end SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib
