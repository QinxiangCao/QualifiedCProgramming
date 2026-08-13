import SimpleC.SL.ArrayLibCore.Definitions

namespace SimpleC.SL.ArrayLibCore.ArrayLibCoreSig

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open Unifysl.LogicGenerator.demo932
open scoped SimpleC.SL.SAC

section Proofs

variable [sac : SacContext]

private theorem store_array_rec_length_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x lo hi : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array_rec SacContext.rules storeA x lo hi l)
      (SacContext.rules.coq_prop (Int.ofNat l.length = hi - lo)) := by
  induction l generalizing lo with
  | nil =>
      simp only [store_array_rec, List.length_nil]
      intro _ hs
      change lo = hi ∧ _ at hs
      change (0 : Int) = hi - lo
      omega
  | cons a l ih =>
      simp only [store_array_rec, List.length_cons]
      intro _ hs
      rcases hs with ⟨s1, s2, _hj, _ha, htail⟩
      have hlen := ih (lo + 1) s2 htail
      change Int.ofNat l.length = hi - (lo + 1) at hlen
      change Int.ofNat l.length + 1 = hi - lo
      omega

private theorem store_array_rec_Zlength_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x lo hi : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array_rec SacContext.rules storeA x lo hi l)
      (SacContext.rules.coq_prop (Zlength l = hi - lo)) := by
  intro state hs
  rw [Zlength_correct]
  exact store_array_rec_length_proof A storeA x lo hi l state hs

private theorem store_array_rec_nil_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x lo : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array_rec SacContext.rules storeA x lo lo l)
      (SacContext.rules.andp (SacContext.rules.coq_prop (l = []))
        SacContext.rules.emp) := by
  intro state hs
  have hlen := store_array_rec_length_proof A storeA x lo lo l state hs
  cases l with
  | nil =>
      simp only [store_array_rec] at hs
      exact ⟨rfl, hs.2.2⟩
  | cons a l =>
      change Int.ofNat (a :: l).length = lo - lo at hlen
      simp only [List.length_cons] at hlen
      have hpos : 0 < Int.ofNat (l.length + 1) :=
        Int.natCast_pos.mpr (by omega)
      rw [hlen] at hpos
      omega

private theorem store_array_rec_valid_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x lo hi : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array_rec SacContext.rules storeA x lo hi l)
      (SacContext.rules.coq_prop (lo <= hi)) := by
  intro state hs
  have hlen := store_array_rec_length_proof A storeA x lo hi l state hs
  change Int.ofNat l.length = hi - lo at hlen
  change lo <= hi
  apply Int.sub_nonneg.mp
  rw [← hlen]
  exact Int.natCast_nonneg l.length

private theorem store_array_length_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x n : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array SacContext.rules storeA x n l)
      (SacContext.rules.coq_prop (Int.ofNat l.length = n)) := by
  unfold store_array
  simpa using store_array_rec_length_proof A storeA x 0 n l

private theorem store_array_Zlength_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x n : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array SacContext.rules storeA x n l)
      (SacContext.rules.coq_prop (Zlength l = n)) := by
  rw [Zlength_correct]
  exact store_array_length_proof A storeA x n l

private theorem store_array_valid_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x n : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array SacContext.rules storeA x n l)
      (SacContext.rules.coq_prop (0 <= n)) := by
  intro state hs
  have hlen := store_array_length_proof A storeA x n l state hs
  change Int.ofNat l.length = n at hlen
  change 0 <= n
  rw [← hlen]
  exact Int.natCast_nonneg l.length

private theorem store_array_missing_i_rec_length_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x i lo hi : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array_missing_i_rec SacContext.rules storeA x i lo hi l)
      (SacContext.rules.coq_prop (Int.ofNat l.length = hi - lo)) := by
  induction l generalizing i lo hi with
  | nil =>
      simp only [store_array_missing_i_rec]
      intro _ hfalse
      exact hfalse.elim
  | cons a l ih =>
      simp only [store_array_missing_i_rec, List.length_cons]
      intro _ hs
      rcases hs with hEq | hGt
      · have hlen := store_array_rec_length_proof A storeA x (lo + 1) hi l
          _ hEq.2
        change Int.ofNat l.length = hi - (lo + 1) at hlen
        change Int.ofNat l.length + 1 = hi - lo
        omega
      · rcases hGt.2 with ⟨s1, s2, _hj, _ha, htail⟩
        have hlen := ih i (lo + 1) hi s2 htail
        change Int.ofNat l.length = hi - (lo + 1) at hlen
        change Int.ofNat l.length + 1 = hi - lo
        omega

private theorem store_array_missing_i_rec_Zlength_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x i lo hi : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array_missing_i_rec SacContext.rules storeA x i lo hi l)
      (SacContext.rules.coq_prop (Zlength l = hi - lo)) := by
  intro state hs
  rw [Zlength_correct]
  exact store_array_missing_i_rec_length_proof A storeA x i lo hi l state hs

private theorem store_array_missing_i_rec_valid_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x i lo hi : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array_missing_i_rec SacContext.rules storeA x i lo hi l)
      (SacContext.rules.coq_prop (lo <= hi)) := by
  intro state hs
  have hlen := store_array_missing_i_rec_length_proof A storeA x i lo hi l
    state hs
  change Int.ofNat l.length = hi - lo at hlen
  change lo <= hi
  apply Int.sub_nonneg.mp
  rw [← hlen]
  exact Int.natCast_nonneg l.length

private theorem store_array_missing_i_valid_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x i n : Int) (l : List A) :
    SacContext.rules.derivable1
      (store_array_missing_i_rec SacContext.rules storeA x i 0 n l)
      (SacContext.rules.coq_prop (0 <= n)) := by
  exact store_array_missing_i_rec_valid_proof A storeA x i 0 n l

private theorem store_array_rec_split_to_missing_i_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x lo n m : Int) (l : List A) (a : A) (h : lo <= n ∧ n < m) :
    SacContext.rules.derivable1
      (store_array_rec SacContext.rules storeA x lo m l)
      (SacContext.rules.sepcon (storeA x n (Znth (n - lo) l a))
        (store_array_missing_i_rec SacContext.rules storeA x n lo m l)) := by
  induction l generalizing lo with
  | nil =>
      simp only [store_array_rec]
      intro _ hs
      have heq : lo = m := hs.1
      omega
  | cons b l ih =>
      simp only [store_array_rec, store_array_missing_i_rec]
      by_cases hlt : lo < n
      · rw [Znth_cons a (n - lo) b l (by omega)]
        have heq : n - (lo + 1) = n - lo - 1 := by omega
        rw [← heq]
        refine SacContext.rules.toContext.derivable1_trans _
          (SacContext.rules.sepcon
            (storeA x n (Znth (n - (lo + 1)) l a))
            (SacContext.rules.andp (SacContext.rules.coq_prop (n > lo))
              (SacContext.rules.sepcon (storeA x lo b)
                (store_array_missing_i_rec SacContext.rules storeA x n
                  (lo + 1) m l)))) _ ?_ ?_
        · refine SacContext.rules.toContext.derivable1_trans _
            (SacContext.rules.sepcon (storeA x lo b)
              (SacContext.rules.sepcon
                (storeA x n (Znth (n - (lo + 1)) l a))
                (store_array_missing_i_rec SacContext.rules storeA x n
                  (lo + 1) m l))) _ ?_ ?_
          · exact SacContext.rules.toContext.derivable1_sepcon_mono _ _ _ _
              (SacContext.rules.toContext.derivable1_refl _)
              (ih (lo + 1) (by omega))
          · refine SacContext.rules.toContext.derivable1_trans _
              (SacContext.rules.sepcon
                (storeA x n (Znth (n - (lo + 1)) l a))
                (SacContext.rules.sepcon (storeA x lo b)
                  (store_array_missing_i_rec SacContext.rules storeA x n
                    (lo + 1) m l))) _ ?_ ?_
            · exact (Automation.logic_equiv_sepcon_swap_rule SacContext.rules
                (storeA x lo b)
                (storeA x n (Znth (n - (lo + 1)) l a))
                (store_array_missing_i_rec SacContext.rules storeA x n
                  (lo + 1) m l)).left
            · exact SacContext.rules.toContext.derivable1_sepcon_mono _ _ _ _
                (SacContext.rules.toContext.derivable1_refl _)
                (coq_prop_andp_right SacContext.rules (n > lo) _ _
                  (SacContext.rules.toContext.derivable1_refl _) hlt)
        · exact SacContext.rules.toContext.derivable1_sepcon_mono _ _ _ _
            (SacContext.rules.toContext.derivable1_refl _)
            (Automation.orp_intros_right
              (SacContext.rules.toContext.derivable1_refl _))
      · have heq : n = lo := by omega
        subst n
        have hzero : lo - lo = 0 := by omega
        rw [hzero, Znth0_cons]
        refine SacContext.rules.toContext.derivable1_trans _
          (SacContext.rules.sepcon (storeA x lo b)
            (SacContext.rules.andp (SacContext.rules.coq_prop (lo = lo))
              (store_array_rec SacContext.rules storeA x (lo + 1) m l)))
          _ ?_ ?_
        · exact SacContext.rules.toContext.derivable1_sepcon_mono _ _ _ _
            (SacContext.rules.toContext.derivable1_refl _)
            (coq_prop_andp_right SacContext.rules (lo = lo) _ _
              (SacContext.rules.toContext.derivable1_refl _) rfl)
        · exact SacContext.rules.toContext.derivable1_sepcon_mono _ _ _ _
            (SacContext.rules.toContext.derivable1_refl _)
            (Automation.orp_intros_left
              (SacContext.rules.toContext.derivable1_refl _))

private theorem store_array_split_to_missing_i_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x n m : Int) (l : List A) (a : A) (h : 0 <= n ∧ n < m) :
    SacContext.rules.derivable1
      (store_array SacContext.rules storeA x m l)
      (SacContext.rules.sepcon (storeA x n (Znth n l a))
        (store_array_missing_i_rec SacContext.rules storeA x n 0 m l)) := by
  simpa [store_array] using
    store_array_rec_split_to_missing_i_proof A storeA x 0 n m l a h

private theorem store_array_missing_i_merge_to_rec_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x lo n m : Int) (a : A) (l : List A) (h : lo <= n ∧ n < m) :
    SacContext.rules.derivable1
      (SacContext.rules.sepcon (storeA x n a)
        (store_array_missing_i_rec SacContext.rules storeA x n lo m l))
      (store_array_rec SacContext.rules storeA x lo m
        (replace_Znth (n - lo) a l)) := by
  induction l generalizing lo with
  | nil =>
      simp only [store_array_missing_i_rec]
      intro _ hs
      rcases hs with ⟨_, _, _, _, hfalse⟩
      exact hfalse.elim
  | cons b l ih =>
      simp only [store_array_missing_i_rec]
      Split
      · rel_rw [SacContext.rules.toContext.logic_equiv_sepcon_coq_prop_andp]
        rel_rw [SacContext.rules.toContext.logic_equiv_coq_prop_andp_sepcon]
        apply coq_prop_andp_left
        intro hn
        subst n
        simp only [Int.sub_self, replace_Znth]
        exact SacContext.rules.toContext.derivable1_refl _
      · rel_rw [SacContext.rules.toContext.logic_equiv_sepcon_coq_prop_andp]
        rel_rw [SacContext.rules.toContext.logic_equiv_coq_prop_andp_sepcon]
        apply coq_prop_andp_left
        intro hgt
        rw [replace_Znth_cons (n - lo) a b l (by omega)]
        have heq : n - lo - 1 = n - (lo + 1) := by omega
        rw [heq]
        simp only [store_array_rec]
        refine SacContext.rules.toContext.derivable1_trans _
          (SacContext.rules.sepcon (storeA x lo b)
            (SacContext.rules.sepcon (storeA x n a)
              (store_array_missing_i_rec SacContext.rules storeA x n
                (lo + 1) m l))) _ ?_ ?_
        · exact (Automation.logic_equiv_sepcon_swap_rule SacContext.rules
            (storeA x n a) (storeA x lo b)
            (store_array_missing_i_rec SacContext.rules storeA x n
              (lo + 1) m l)).left
        · exact SacContext.rules.toContext.derivable1_sepcon_mono _ _ _ _
            (SacContext.rules.toContext.derivable1_refl _)
            (ih (lo + 1) (by omega))

private theorem store_array_missing_i_merge_to_array_proof (A : Type)
    (storeA : addr -> Int -> A -> SacContext.rules.expr)
    (x n m : Int) (a : A) (l : List A) (h : 0 <= n ∧ n < m) :
    SacContext.rules.derivable1
      (SacContext.rules.sepcon (storeA x n a)
        (store_array_missing_i_rec SacContext.rules storeA x n 0 m l))
      (store_array SacContext.rules storeA x m (replace_Znth n a l)) := by
  simpa [store_array] using
    store_array_missing_i_merge_to_rec_proof A storeA x 0 n m a l h

end Proofs

theorem store_array_rec_length (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr) (x lo hi : Int) (l : List A) :
    CRules.derivable1 (store_array_rec CRules storeA x lo hi l)
      (CRules.coq_prop (Int.ofNat l.length = hi - lo)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_rec_length_proof A storeA x lo hi l

theorem store_array_rec_Zlength (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr) (x lo hi : Int) (l : List A) :
    CRules.derivable1 (store_array_rec CRules storeA x lo hi l)
      (CRules.coq_prop (Zlength l = hi - lo)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_rec_Zlength_proof A storeA x lo hi l

theorem store_array_rec_nil (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr) (x lo : Int) (l : List A) :
    CRules.derivable1 (store_array_rec CRules storeA x lo lo l)
      (CRules.andp (CRules.coq_prop (l = [])) CRules.emp) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_rec_nil_proof A storeA x lo l

theorem store_array_rec_valid (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr) (x lo hi : Int) (l : List A) :
    CRules.derivable1 (store_array_rec CRules storeA x lo hi l)
      (CRules.coq_prop (lo <= hi)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_rec_valid_proof A storeA x lo hi l

theorem store_array_length (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr) (x n : Int) (l : List A) :
    CRules.derivable1 (store_array CRules storeA x n l)
      (CRules.coq_prop (Int.ofNat l.length = n)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_length_proof A storeA x n l

theorem store_array_Zlength (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr) (x n : Int) (l : List A) :
    CRules.derivable1 (store_array CRules storeA x n l)
      (CRules.coq_prop (Zlength l = n)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_Zlength_proof A storeA x n l

theorem store_array_valid (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr) (x n : Int) (l : List A) :
    CRules.derivable1 (store_array CRules storeA x n l)
      (CRules.coq_prop (0 <= n)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_valid_proof A storeA x n l

theorem store_array_missing_i_rec_length (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr)
    (x i lo hi : Int) (l : List A) :
    CRules.derivable1 (store_array_missing_i_rec CRules storeA x i lo hi l)
      (CRules.coq_prop (Int.ofNat l.length = hi - lo)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_missing_i_rec_length_proof A storeA x i lo hi l

theorem store_array_missing_i_rec_Zlength (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr)
    (x i lo hi : Int) (l : List A) :
    CRules.derivable1 (store_array_missing_i_rec CRules storeA x i lo hi l)
      (CRules.coq_prop (Zlength l = hi - lo)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_missing_i_rec_Zlength_proof A storeA x i lo hi l

theorem store_array_missing_i_rec_valid (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr)
    (x i lo hi : Int) (l : List A) :
    CRules.derivable1 (store_array_missing_i_rec CRules storeA x i lo hi l)
      (CRules.coq_prop (lo <= hi)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_missing_i_rec_valid_proof A storeA x i lo hi l

theorem store_array_missing_i_valid (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr)
    (x i n : Int) (l : List A) :
    CRules.derivable1 (store_array_missing_i_rec CRules storeA x i 0 n l)
      (CRules.coq_prop (0 <= n)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_missing_i_valid_proof A storeA x i n l

theorem store_array_rec_split_to_missing_i (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr)
    (x lo n m : Int) (l : List A) (a : A) (h : lo <= n ∧ n < m) :
    CRules.derivable1 (store_array_rec CRules storeA x lo m l)
      (CRules.sepcon (storeA x n (Znth (n - lo) l a))
        (store_array_missing_i_rec CRules storeA x n lo m l)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_rec_split_to_missing_i_proof A storeA x lo n m l a h

theorem store_array_split_to_missing_i (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr)
    (x n m : Int) (l : List A) (a : A) (h : 0 <= n ∧ n < m) :
    CRules.derivable1 (store_array CRules storeA x m l)
      (CRules.sepcon (storeA x n (Znth n l a))
        (store_array_missing_i_rec CRules storeA x n 0 m l)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_split_to_missing_i_proof A storeA x n m l a h

theorem store_array_missing_i_merge_to_rec (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr)
    (x lo n m : Int) (a : A) (l : List A) (h : lo <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (storeA x n a)
        (store_array_missing_i_rec CRules storeA x n lo m l))
      (store_array_rec CRules storeA x lo m (replace_Znth (n - lo) a l)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_missing_i_merge_to_rec_proof A storeA x lo n m a l h

theorem store_array_missing_i_merge_to_array (CRules : SeparationLogicSig) (A : Type)
    (storeA : addr -> Int -> A -> CRules.expr)
    (x n m : Int) (a : A) (l : List A) (h : 0 <= n ∧ n < m) :
    CRules.derivable1
      (CRules.sepcon (storeA x n a)
        (store_array_missing_i_rec CRules storeA x n 0 m l))
      (store_array CRules storeA x m (replace_Znth n a l)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_array_missing_i_merge_to_array_proof A storeA x n m a l h

end SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
