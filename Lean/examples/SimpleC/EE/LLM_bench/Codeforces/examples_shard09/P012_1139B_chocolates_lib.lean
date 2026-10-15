import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_lib
open AUXLib


open MaxMinLib

def FeasiblePurchase (a x : List Int) : Prop :=
  Zlength x = Zlength a ∧
  (∀ i, (0 ≤ i ∧ i < Zlength a) → (0 ≤ Znth i x 0 ∧ Znth i x 0 ≤ Znth i a 0)) ∧
  (∀ j i, ((0 ≤ j ∧ j < i) ∧ i < Zlength a) → Znth j x 0 = 0 ∨ Znth j x 0 < Znth i x 0)
def Pre (a : List Int) : Prop :=
  (1 ≤ Zlength a ∧ Zlength a ≤ 200000) ∧ Forall (fun x => 1 ≤ x ∧ x ≤ 1000000000) a
def Spec (a : List Int) (out : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun v => ∃ x, FeasiblePurchase a x ∧ v = x.foldr (· + ·) 0) (fun x => x) out

def DominantPurchase (a x : List Int) : Prop :=
  FeasiblePurchase a x ∧ ∀ y, FeasiblePurchase a y → ∀ k, (0 ≤ k ∧ k < Zlength a) → Znth k y 0 ≤ Znth k x 0

def SuffixDominantState (a : List Int) (lo total prev : Int) : Prop :=
  ∃ x, DominantPurchase (sublist lo (Zlength a) a) x ∧
    total = x.foldr (· + ·) 0 ∧ (lo = Zlength a → prev = 0) ∧ (lo < Zlength a → prev = Znth 0 x 0)

theorem dominant_purchase_empty__initialization (a : List Int) :
    DominantPurchase (sublist (Zlength a) (Zlength a) a) [] := by
  rw [Zsublist_nil a _ _ (le_refl _)]
  refine ⟨⟨rfl,?_,?_⟩,?_⟩
  · intro i hi; simp only [Zlength_nil] at hi; omega
  · intro j i hi; simp only [Zlength_nil] at hi; omega
  · intro y hy k hk; simp only [Zlength_nil] at hk; omega

theorem sublist_step__backward_transitions (a : List Int) (i : Int) :
    (0≤i ∧ i<Zlength a) → sublist i (Zlength a) a=Znth i a 0::sublist (i+1) (Zlength a) a := by
  intro hi
  rw [sublist_split i (Zlength a) (i+1) a ⟨hi.1,by omega⟩ ⟨by omega,le_refl _⟩,
    sublist_single 0 i a hi]
  rfl

theorem feasible_purchase_cons__backward_transitions (cur p : Int) (s x : List Int) :
    FeasiblePurchase s x → (0≤p ∧ p≤cur) →
    (∀ k, (0≤k ∧ k<Zlength x) → p=0 ∨ p<Znth k x 0) → FeasiblePurchase (cur::s) (p::x) := by
  rintro ⟨hl,hb,ho⟩ hp ht
  refine ⟨by simp only [Zlength_cons,hl],?_,?_⟩
  · intro k hk
    simp only [Zlength_cons] at hk
    by_cases he : k=0
    · subst k; simpa only [Znth0_cons] using hp
    · rw [Znth_cons 0 k p x (by omega),Znth_cons 0 k cur s (by omega)]
      exact hb (k-1) ⟨by omega,by omega⟩
  · intro j k hjk
    simp only [Zlength_cons] at hjk
    by_cases he : j=0
    · subst j
      rw [Znth0_cons,Znth_cons 0 k p x (by omega)]
      exact ht (k-1) ⟨by omega,by omega⟩
    · rw [Znth_cons 0 j p x (by omega),Znth_cons 0 k p x (by omega)]
      exact ho (j-1) (k-1) ⟨⟨by omega,by omega⟩,by omega⟩

theorem feasible_purchase_tail__backward_transitions (cur : Int) (s y : List Int) :
    FeasiblePurchase (cur::s) y → FeasiblePurchase s y.tail := by
  rintro ⟨hl,hb,ho⟩
  cases y with
  | nil =>
    have hsn := Zlength_nonneg s
    simp only [Zlength_nil,Zlength_cons] at hl
    omega
  | cons q y =>
    simp only [List.tail_cons]
    simp only [Zlength_cons] at hl
    refine ⟨by omega,?_,?_⟩
    · intro k hk
      have hh := hb (k+1) (by simp only [Zlength_cons]; omega)
      rw [Znth_cons 0 (k+1) q y (by omega),Znth_cons 0 (k+1) cur s (by omega)] at hh
      simpa only [add_sub_cancel_right] using hh
    · intro j k hjk
      have hh := ho (j+1) (k+1) (by simp only [Zlength_cons]; omega)
      rw [Znth_cons 0 (j+1) q y (by omega),Znth_cons 0 (k+1) q y (by omega)] at hh
      simpa only [add_sub_cancel_right] using hh

theorem dominant_purchase_cons__backward_transitions (cur p : Int) (s x : List Int) :
    DominantPurchase s x → (0≤p ∧ p≤cur) →
    (∀ k, (0≤k ∧ k<Zlength x) → p=0 ∨ p<Znth k x 0) →
    (∀ y, FeasiblePurchase (cur::s) y → Znth 0 y 0≤p) → DominantPurchase (cur::s) (p::x) := by
  rintro ⟨hf,hd⟩ hp ht hh
  refine ⟨feasible_purchase_cons__backward_transitions cur p s x hf hp ht,?_⟩
  intro y hy k hk
  by_cases he : k=0
  · subst k
    rw [Znth0_cons]
    exact hh y hy
  · cases y with
    | nil =>
      have hl := hy.1
      simp only [Zlength_nil] at hl
      omega
    | cons q y =>
      rw [Znth_cons 0 k q y (by omega),Znth_cons 0 k p x (by omega)]
      exact hd y (feasible_purchase_tail__backward_transitions cur s (q::y) hy)
        (k-1) (by simp only [Zlength_cons] at hk; omega)

theorem suffix_dominant_prepend__backward_transitions (values : List Int) (i total prev p : Int) :
    (0≤i ∧ i<Zlength values) → SuffixDominantState values (i+1) total prev →
    (0≤p ∧ p≤Znth i values 0) →
    (∀ x, DominantPurchase (sublist (i+1) (Zlength values) values) x →
      ∀ k, (0≤k ∧ k<Zlength x) → p=0 ∨ p<Znth k x 0) →
    (∀ x, DominantPurchase (sublist (i+1) (Zlength values) values) x →
      ∀ y, FeasiblePurchase (Znth i values 0::sublist (i+1) (Zlength values) values) y → Znth 0 y 0≤p) →
    SuffixDominantState values i (total+p) p := by
  rintro hi ⟨x,hd,ht,he,hp⟩ hpb htop hhead
  refine ⟨p::x,?_,?_,?_,?_⟩
  · rw [sublist_step__backward_transitions values i hi]
    exact dominant_purchase_cons__backward_transitions (Znth i values 0) p _ x hd hpb (htop x hd) (hhead x hd)
  · simp only [List.foldr_cons]; omega
  · intro h; omega
  · intro h; rfl

theorem fold_right_Z_add_le__final_result (xs ys : List Int) :
    Zlength xs=Zlength ys → (∀ k, (0≤k ∧ k<Zlength xs) → Znth k xs 0≤Znth k ys 0) →
    xs.foldr (·+·) 0≤ys.foldr (·+·) 0 := by
  induction xs generalizing ys with
  | nil =>
    intro hl _
    have he : ys=[] := by apply List.length_eq_zero_iff.mp; exact Int.ofNat_inj.mp hl.symm
    subst ys
    exact le_refl _
  | cons x xs ih =>
    intro hl hp
    cases ys with
    | nil => simp only [Zlength_cons,Zlength_nil] at hl; have := Zlength_nonneg xs; omega
    | cons y ys =>
      have hhead := hp 0 (by simp only [Zlength_cons]; have := Zlength_nonneg xs; omega)
      simp only [Znth0_cons] at hhead
      have htail := ih ys (by simp only [Zlength_cons] at hl; omega) (by
        intro k hk
        have hh := hp (k+1) (by simp only [Zlength_cons]; omega)
        rw [Znth_cons 0 (k+1) x xs (by omega),Znth_cons 0 (k+1) y ys (by omega)] at hh
        simpa only [add_sub_cancel_right] using hh)
      simp only [List.foldr_cons]
      omega

theorem suffix_dominant_state_to_spec__final_result (a : List Int) (total prev : Int) :
    SuffixDominantState a 0 total prev → Spec a total := by
  rintro ⟨x,hd,ht,_,_⟩
  rw [sublist_self a (Zlength a) rfl] at hd
  unfold Spec max_value_of_subset max_object_of_subset
  refine ⟨x.foldr (·+·) 0,⟨⟨x,hd.1,rfl⟩,?_⟩,ht.symm⟩
  rintro v ⟨y,hy,rfl⟩
  exact fold_right_Z_add_le__final_result y x (hy.1.trans hd.1.1.symm)
    (fun k hk => hd.2 y hy k (by rw [hy.1] at hk; exact hk))

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_lib
