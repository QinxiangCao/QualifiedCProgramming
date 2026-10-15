import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_lib
open AUXLib

/-- The length-l segment starting at start in the doubled input. -/
def MRRotation (l : List Int) (start : Int) : List Int :=
  sublist start (start + Zlength l) (l ++ l)

def MRValidStart (l : List Int) (start : Int) : Prop := 0 ≤ start ∧ start < Zlength l

def MRRotationValue (l : List Int) (start offset : Int) : Int := Znth (start + offset) (l ++ l) 0

def MRRotationPrefixEq (l : List Int) (left right prefix_len : Int) : Prop :=
  ∀ offset, (0 ≤ offset ∧ offset < prefix_len) →
    MRRotationValue l left offset = MRRotationValue l right offset

def MRRotationEq (l : List Int) (left right : Int) : Prop :=
  MRRotationPrefixEq l left right (Zlength l)

def MRRotationLt (l : List Int) (left right : Int) : Prop :=
  ∃ first_diff, (0 ≤ first_diff ∧ first_diff < Zlength l) ∧
    MRRotationPrefixEq l left right first_diff ∧
    MRRotationValue l left first_diff < MRRotationValue l right first_diff

def MRRotationLe (l : List Int) (left right : Int) : Prop :=
  MRRotationLt l left right ∨ MRRotationEq l left right

def MRMinimalRotationAt (l : List Int) (start : Int) : Prop :=
  MRValidStart l start ∧ ∀ other, MRValidStart l other → MRRotationLe l start other

def MRFirstMinimalRotationAt (l : List Int) (start : Int) : Prop :=
  MRMinimalRotationAt l start ∧
    ∀ other, MRValidStart l other → MRRotationEq l start other → start ≤ other

def MRCandidateState (l : List Int) (best i j : Int) : Prop :=
  best = i ∨ best = j ∨ (max i j ≤ best ∧ ¬ MRRotationEq l i j)

private theorem getD_append_left (l1 l2 : List Int) (d : Int) (n : Nat) (hn : n < l1.length) :
    (l1 ++ l2).getD n d = l1.getD n d := by
  induction l1 generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n (by simpa using hn)

private theorem app_Znth1 (d : Int) (l1 l2 : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l1) : Znth i (l1 ++ l2) d = Znth i l1 d := by
  unfold Znth
  exact getD_append_left l1 l2 d i.toNat (by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega)

theorem Znth_double_add_length__candidate_transitions (l : List Int) (z : Int)
    (hz : 0 ≤ z ∧ z < Zlength l) :
    Znth (z + Zlength l) (l ++ l) 0 = Znth z (l ++ l) 0 := by
  rw [app_Znth2 0 l l (z+Zlength l) (by omega), app_Znth1 0 l l z hz]
  congr 1
  omega

theorem MRRotationValue_sub_length__candidate_transitions (l : List Int) (start offset : Int)
    (hs : Zlength l ≤ start) (ho : 0 ≤ offset) (hu : start+offset < 2*Zlength l) :
    MRRotationValue l (start-Zlength l) offset = MRRotationValue l start offset := by
  unfold MRRotationValue
  rw [show start+offset = (start-Zlength l+offset)+Zlength l by omega]
  exact (Znth_double_add_length__candidate_transitions l (start-Zlength l+offset) (by omega)).symm

theorem MRRotationEq_sym__candidate_transitions (l : List Int) (a b : Int)
    (h : MRRotationEq l a b) : MRRotationEq l b a := by
  intro offset ho
  exact (h offset ho).symm

theorem MRRotationPrefixEq_sym__candidate_transitions (l : List Int) (a b k : Int)
    (h : MRRotationPrefixEq l a b k) : MRRotationPrefixEq l b a k := by
  intro offset ho
  exact (h offset ho).symm

theorem MRRotationEq_shift__candidate_transitions (l : List Int) (a b shift : Int)
    (hl : 0 < Zlength l) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ shift)
    (has : a+shift < Zlength l) (hbs : b+shift < Zlength l)
    (heq : MRRotationEq l a b) : MRRotationEq l (a+shift) (b+shift) := by
  intro offset ho
  by_cases hn : shift+offset < Zlength l
  · have h := heq (shift+offset) (by omega)
    simpa only [MRRotationValue, Int.add_assoc] using h
  · have h := heq (shift+offset-Zlength l) (by omega)
    unfold MRRotationValue at h ⊢
    rw [show a+shift+offset = (a+(shift+offset-Zlength l))+Zlength l by omega,
        show b+shift+offset = (b+(shift+offset-Zlength l))+Zlength l by omega,
        Znth_double_add_length__candidate_transitions l _ (by omega),
        Znth_double_add_length__candidate_transitions l _ (by omega)]
    exact h

theorem MRRotationLt_not_le_rev__candidate_transitions (l : List Int) (a b : Int)
    (hlt : MRRotationLt l a b) : ¬ MRRotationLe l b a := by
  rcases hlt with ⟨da, hda, hab, hlt⟩
  rintro (⟨db, hdb, hba, hgt⟩ | heq)
  · by_cases hd : da < db
    · have := hba da (by omega); omega
    · by_cases hd2 : db < da
      · have := hab db (by omega); omega
      · have hd : db = da := by omega
        subst db
        omega
  · have := heq da hda
    omega

theorem MRRotationEq_frontier_neq__candidate_transitions (l : List Int) (best x y : Int)
    (hf : MRFirstMinimalRotationAt l best) (hx : MRValidStart l x) (hy : MRValidStart l y)
    (hfront : max x y ≤ best) (hxy : x ≠ y) : ¬ MRRotationEq l x y := by
  intro heq
  have hbest := hf.1.1
  dsimp only [MRValidStart] at hx hy hbest
  by_cases hlt : x < y
  · have hshift := MRRotationEq_shift__candidate_transitions l x y (best-y)
      (by omega) hx.1 hy.1 (by omega) (by omega) (by omega) heq
    have ht := hf.2 (x+(best-y)) (by constructor <;> omega)
      (by simpa only [show y+(best-y) = best by omega] using
        MRRotationEq_sym__candidate_transitions l _ _ hshift)
    omega
  · have hshift := MRRotationEq_shift__candidate_transitions l y x (best-x)
      (by omega) hy.1 hx.1 (by omega) (by omega) (by omega)
      (MRRotationEq_sym__candidate_transitions l x y heq)
    have ht := hf.2 (y+(best-x)) (by constructor <;> omega)
      (by simpa only [show x+(best-x) = best by omega] using
        MRRotationEq_sym__candidate_transitions l _ _ hshift)
    omega

theorem MRCandidateState_swap__candidate_transitions (l : List Int) (best i j : Int)
    (hs : MRCandidateState l best i j) : MRCandidateState l best j i := by
  rcases hs with hi | hj | ⟨hf, hne⟩
  · exact Or.inr (Or.inl hi)
  · exact Or.inl hj
  · exact Or.inr (Or.inr ⟨by simpa only [Int.max_comm] using hf,
      fun h => hne (MRRotationEq_sym__candidate_transitions l j i h)⟩)

theorem MRFirstMinimal_excludes_left_interval__candidate_transitions
    (l : List Int) (best i j k : Int) (hf : MRFirstMinimalRotationAt l best)
    (hi : MRValidStart l i) (hj : MRValidStart l j) (hk : 0 ≤ k ∧ k < Zlength l)
    (hp : MRRotationPrefixEq l i j k) (hm : MRRotationValue l j k < MRRotationValue l i k)
    (hib : i ≤ best) : i+k < best := by
  have hb : 0 ≤ best ∧ best < Zlength l := hf.1.1
  dsimp only [MRValidStart] at hi hj
  by_cases hd : i+k < best
  · exact hd
  · let d := best-i
    have hdb : 0 ≤ d ∧ d ≤ k := by dsimp [d]; omega
    have hrawprefix : MRRotationPrefixEq l (j+d) best (k-d) := by
      intro offset ho
      have h := hp (d+offset) (by omega)
      unfold MRRotationValue at h ⊢
      rw [show j+d+offset = j+(d+offset) by omega,
          show best+offset = i+(d+offset) by dsimp [d]; omega]
      exact h.symm
    have hrawlt : MRRotationValue l (j+d) (k-d) < MRRotationValue l best (k-d) := by
      unfold MRRotationValue at hm ⊢
      rw [show j+d+(k-d) = j+k by omega,
          show best+(k-d) = i+k by dsimp [d]; omega]
      exact hm
    by_cases hwrap : j+d < Zlength l
    · have hloses : MRRotationLt l (j+d) best := ⟨k-d, by omega, hrawprefix, hrawlt⟩
      exact False.elim (MRRotationLt_not_le_rev__candidate_transitions l (j+d) best hloses
        (hf.1.2 (j+d) (by constructor <;> omega)))
    · have hloses : MRRotationLt l (j+d-Zlength l) best := by
        refine ⟨k-d, by omega, ?_, ?_⟩
        · intro offset ho
          rw [MRRotationValue_sub_length__candidate_transitions l (j+d) offset (by omega) (by omega) (by omega)]
          exact hrawprefix offset ho
        · rw [MRRotationValue_sub_length__candidate_transitions l (j+d) (k-d) (by omega) (by omega) (by omega)]
          exact hrawlt
      exact False.elim (MRRotationLt_not_le_rev__candidate_transitions l (j+d-Zlength l) best hloses
        (hf.1.2 (j+d-Zlength l) (by constructor <;> omega)))

theorem MRCandidateState_advance_left__candidate_transitions
    (l : List Int) (best i j k : Int) (hf : MRFirstMinimalRotationAt l best)
    (hi : MRValidStart l i) (hj : MRValidStart l j) (hk : 0 ≤ k ∧ k < Zlength l)
    (hp : MRRotationPrefixEq l i j k) (hm : MRRotationValue l j k < MRRotationValue l i k)
    (hs : MRCandidateState l best i j) :
    (i+k+1 = j → MRCandidateState l best (i+k+2) j) ∧
    (i+k+1 ≠ j → MRCandidateState l best (i+k+1) j) := by
  have hb : 0 ≤ best ∧ best < Zlength l := hf.1.1
  dsimp only [MRValidStart] at hi hj
  rcases hs with hbi | hbj | ⟨hfront, hne⟩
  · have h := MRFirstMinimal_excludes_left_interval__candidate_transitions l best i j k hf hi hj hk hp hm (by omega)
    omega
  · exact ⟨fun _ => Or.inr (Or.inl hbj), fun _ => Or.inr (Or.inl hbj)⟩
  · have ha := MRFirstMinimal_excludes_left_interval__candidate_transitions l best i j k hf hi hj hk hp hm (by omega)
    constructor
    · intro hcollision
      by_cases hbj : best = j
      · exact Or.inr (Or.inl hbj)
      · exact Or.inr (Or.inr ⟨by omega,
          MRRotationEq_frontier_neq__candidate_transitions l best (i+k+2) j hf
            (by constructor <;> omega) hj (by omega) (by omega)⟩)
    · intro hcollision
      exact Or.inr (Or.inr ⟨by omega,
        MRRotationEq_frontier_neq__candidate_transitions l best (i+k+1) j hf
          (by constructor <;> omega) hj (by omega) hcollision⟩)

theorem MRCandidateState_advance_right__candidate_transitions
    (l : List Int) (best i j k : Int) (hf : MRFirstMinimalRotationAt l best)
    (hi : MRValidStart l i) (hj : MRValidStart l j) (hk : 0 ≤ k ∧ k < Zlength l)
    (hp : MRRotationPrefixEq l i j k) (hm : MRRotationValue l i k < MRRotationValue l j k)
    (hs : MRCandidateState l best i j) :
    (j+k+1 = i → MRCandidateState l best i (j+k+2)) ∧
    (j+k+1 ≠ i → MRCandidateState l best i (j+k+1)) := by
  have h := MRCandidateState_advance_left__candidate_transitions l best j i k hf hj hi hk
    (MRRotationPrefixEq_sym__candidate_transitions l i j k hp) hm
    (MRCandidateState_swap__candidate_transitions l best i j hs)
  exact ⟨fun hc => MRCandidateState_swap__candidate_transitions l best _ _ (h.1 hc),
    fun hn => MRCandidateState_swap__candidate_transitions l best _ _ (h.2 hn)⟩

theorem MRRotationEq_sym__candidate_boundaries (l : List Int) (i j : Int)
    (h : MRRotationEq l i j) : MRRotationEq l j i := by
  exact MRRotationEq_sym__candidate_transitions l i j h

theorem MRRotationEq_zero_one_all__candidate_boundaries (l : List Int)
    (hl : 1 ≤ Zlength l) (heq : MRRotationEq l 0 1) (start : Int) (hs : MRValidStart l start) :
    MRRotationEq l start 0 := by
  dsimp only [MRValidStart] at hs
  have hchainN (m : Nat) : (m : Int) ≤ Zlength l → Znth (m : Int) (l++l) 0 = Znth 0 (l++l) 0 := by
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have he := heq (m : Int) (by omega)
      simp only [MRRotationValue, Int.zero_add] at he
      rw [show (m.succ : Int) = 1+(m : Int) by omega, ← he]
      exact ih (by omega)
  have hchain (z : Int) (hz : 0 ≤ z ∧ z ≤ Zlength l) : Znth z (l++l) 0 = Znth 0 (l++l) 0 := by
    have h := hchainN z.toNat (by omega)
    simpa only [Int.toNat_of_nonneg hz.1] using h
  have hall (z : Int) (hz : 0 ≤ z ∧ z < 2*Zlength l) : Znth z (l++l) 0 = Znth 0 (l++l) 0 := by
    by_cases hn : z < Zlength l
    · exact hchain z (by omega)
    · rw [show z = (z-Zlength l)+Zlength l by omega,
        Znth_double_add_length__candidate_transitions l _ (by omega)]
      exact hchain (z-Zlength l) (by omega)
  intro offset ho
  unfold MRRotationValue
  exact (hall (start+offset) (by omega)).trans (hall (0+offset) (by omega)).symm

theorem MRCandidateState_initial__candidate_boundaries (l : List Int) (best : Int)
    (hl : 1 ≤ Zlength l) (hf : MRFirstMinimalRotationAt l best) : MRCandidateState l best 0 1 := by
  have hb : 0 ≤ best ∧ best < Zlength l := hf.1.1
  by_cases h0 : best = 0
  · exact Or.inl h0
  · by_cases h1 : best = 1
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
      intro heq
      have he := MRRotationEq_zero_one_all__candidate_boundaries l hl heq best hb
      have ht := hf.2 0 (by constructor <;> omega) he
      omega

theorem MRCandidateState_equal_exit__candidate_boundaries (l : List Int) (best i j : Int)
    (hi : MRValidStart l i) (hj : MRValidStart l j) (hne : i ≠ j)
    (hf : MRFirstMinimalRotationAt l best) (hs : MRCandidateState l best i j)
    (heq : MRRotationEq l i j) : (i < j → i = best) ∧ (i ≥ j → j = best) := by
  rcases hs with hbi | hbj | ⟨_, hneq⟩
  · have ht := hf.2 j hj (by rw [hbi]; exact heq)
    constructor <;> intro h <;> omega
  · have ht := hf.2 i hi (by rw [hbj]; exact MRRotationEq_sym__candidate_boundaries l i j heq)
    constructor <;> intro h <;> omega
  · exact False.elim (hneq heq)

theorem MRRotation_Zlength__output_finalization (l : List Int) (start : Int)
    (hs : MRValidStart l start) : Zlength (MRRotation l start) = Zlength l := by
  dsimp only [MRValidStart] at hs
  change Int.ofNat (sublist start (start+Zlength l) (l++l)).length = Zlength l
  rw [sublist_length start (start+Zlength l) (l++l) (by have := Zlength_nonneg l; omega)
    (by rw [Zlength_app]; omega)]
  have hn := Zlength_nonneg l
  rw [show start+Zlength l-start = Zlength l by omega]
  exact Int.toNat_of_nonneg hn

theorem MRRotation_Znth__output_finalization (l : List Int) (start offset : Int)
    (hs : MRValidStart l start) (ho : 0 ≤ offset ∧ offset < Zlength l) :
    Znth offset (MRRotation l start) 0 = Znth (start+offset) (l++l) 0 := by
  unfold MRRotation
  rw [Znth_sublist 0 start offset (start+Zlength l) (l++l) hs.1 (by omega)]
  congr 1
  omega

end SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_lib
namespace SimpleC.EE.LLM_bench.Algorithms.minimal_representation
export minimal_representation_lib (MRRotation MRValidStart MRRotationValue MRRotationPrefixEq MRRotationEq
  MRRotationLt MRRotationLe MRMinimalRotationAt MRFirstMinimalRotationAt MRCandidateState)
end SimpleC.EE.LLM_bench.Algorithms.minimal_representation
