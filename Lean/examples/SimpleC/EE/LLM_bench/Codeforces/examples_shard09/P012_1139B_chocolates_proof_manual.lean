import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P012_1139B_chocolates_goal P012_1139B_chocolates_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem suffix_length (values : List Int) (lo : Int) (hlo : 0≤lo ∧ lo≤Zlength values) :
    Zlength (sublist lo (Zlength values) values)=Zlength values-lo := by
  change Int.ofNat (sublist lo (Zlength values) values).length=Zlength values-lo
  rw [sublist_length lo (AUXLib.Zlength values) values hlo (le_refl _)]
  exact Int.toNat_of_nonneg (by omega)

private theorem greedy_nonempty_step (values : List Int) (i total prev p : Int)
    (hi : 0≤i ∧ i+1<Zlength values) (hs : SuffixDominantState values (i+1) total prev)
    (hp : 0≤p ∧ p≤Znth i values 0) (htop : p=0 ∨ p<prev)
    (hmax : ∀ q, 0≤q → q≤Znth i values 0 → (q=0 ∨ q<prev) → q≤p) :
    SuffixDominantState values i (total+p) p := by
  rcases hs with ⟨x,hd,ht,he,hpr⟩
  have hprev := hpr hi.2
  have hslen := suffix_length values (i+1) ⟨by omega,by omega⟩
  refine ⟨p::x,?_,?_,?_,?_⟩
  · rw [sublist_step__backward_transitions values i ⟨hi.1,by omega⟩]
    apply dominant_purchase_cons__backward_transitions _ p _ x hd hp
    · intro k hk
      rcases htop with hz|hlt
      · exact Or.inl hz
      · right
        by_cases hk0 : k=0
        · subst k; rwa [←hprev]
        · have ho := hd.1.2.2 0 k ⟨⟨by omega,by omega⟩,by rw [←hd.1.1]; exact hk.2⟩
          rcases ho with hz|hlt'
          · rw [hz] at hprev; omega
          · rw [←hprev] at hlt'; omega
    · intro y hy
      have hqb := hy.2.1 0 (by simp only [Zlength_cons]; have := Zlength_nonneg (sublist (i+1) (Zlength values) values); omega)
      simp only [Znth0_cons] at hqb
      apply hmax _ hqb.1 hqb.2
      cases y with
      | nil => exact Or.inl rfl
      | cons q y =>
        have ho := hy.2.2 0 1 (by simp only [Zlength_cons]; omega)
        rw [Znth0_cons,Znth_cons 0 1 q y (by omega)] at ho
        change q=0 ∨ q<Znth 0 y 0 at ho
        have htail := feasible_purchase_tail__backward_transitions _ _ (q::y) hy
        have hdom := hd.2 y htail 0 ⟨by omega,by omega⟩
        rw [←hprev] at hdom
        change q=0 ∨ q<prev
        rcases ho with hz|hlt
        · exact Or.inl hz
        · exact Or.inr (by omega)
  · simp only [List.foldr_cons]; omega
  · intro h; omega
  · intro h; rfl

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n values h1 h2 h3 h4
  rw [show n-1+1=Zlength values by omega]
  exact ⟨[],dominant_purchase_empty__initialization values,rfl,fun _ => rfl,fun h => False.elim (by omega)⟩

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n values h1 h2 h3 h4
  exact h3

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rw [show n-1-1+1=i by omega,←h1]
  have hstock := h6 i ⟨h2,h8⟩
  apply suffix_dominant_prepend__backward_transitions values i total prev (Znth i values 0) ⟨h2,by omega⟩ h13 ⟨by omega,le_refl _⟩
  · intro z hz k hk
    have hem : sublist (i+1) (Zlength values) values=[] := Zsublist_nil values _ _ (by omega)
    have hl := hz.1.1
    rw [hem,Zlength_nil] at hl
    omega
  · intro z hz y hy
    have hh := hy.2.1 0 (by simp only [Zlength_cons]; have := Zlength_nonneg (sublist (i+1) (Zlength values) values); omega)
    simpa only [Znth0_cons] using hh.2

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  have hs := h8 i ⟨h4,h10⟩
  omega

theorem proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1 := by
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  rw [sub_add_cancel]
  have hs := h8 i ⟨h4,h10⟩
  apply greedy_nonempty_step values i total prev 0 ⟨h4,by omega⟩ h15 ⟨le_refl _,by omega⟩ (Or.inl rfl)
  intro q hq hc hh
  rcases hh with hz|hlt <;> omega

theorem proof_of_solver_entail_wit_2_4_split_goal_1 : solver_entail_wit_2_4_split_goal_1 := by
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  rw [sub_add_cancel]
  apply greedy_nonempty_step values i total prev (Znth i values 0) ⟨h4,by omega⟩ h15
    ⟨h1,le_refl _⟩ (Or.inr (by omega))
  intro q hq hc hh
  exact hc

theorem proof_of_solver_entail_wit_2_5_split_goal_1 : solver_entail_wit_2_5_split_goal_1 := by
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  rw [sub_add_cancel]
  apply greedy_nonempty_step values i total prev (prev-1) ⟨h4,by omega⟩ h15
    ⟨h1,h2⟩ (Or.inr (by omega))
  intro q hq hc hh
  rcases hh with hz|hlt <;> omega

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  apply suffix_dominant_state_to_spec__final_result values total prev
  simpa only [show i+1=0 by omega] using h12

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n values h1 h2 h3 h4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n values h1 h2 h3 h4
      | exact proof_of_solver_entail_wit_1_split_goal_2 n values h1 h2 h3 h4

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  unfold solver_entail_wit_2_1
  right
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_1_split_goal_1 n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  unfold solver_entail_wit_2_2
  right
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_2_split_goal_1 n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

theorem proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3 := by
  unfold solver_entail_wit_2_3
  right
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_3_split_goal_1 n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

theorem proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4 := by
  unfold solver_entail_wit_2_4
  right
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_4_split_goal_1 n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

theorem proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5 := by
  unfold solver_entail_wit_2_5
  right
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_5_split_goal_1 n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_1_split_goal_1 n values prev total i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_proof_manual
