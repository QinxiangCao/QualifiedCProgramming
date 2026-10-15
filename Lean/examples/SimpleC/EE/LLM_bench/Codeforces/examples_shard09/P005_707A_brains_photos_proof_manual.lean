import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P005_707A_brains_photos_goal P005_707A_brains_photos_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro m n photo default h1 h2 h3 h4 h5 h6 h7
  intro k hk
  omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro m n photo default h1 h2 h3 h4 h5 h6 h7
  exact pre_rectangular_facts__initialization photo n m default h5 h6

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro m n photo default h1 h2 h3 h4 h5 h6 h7
  exact h7

theorem proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4 := by
  intro m n photo default h1 h2 h3 h4 h5 h6 h7
  exact h6

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro m n photo default h1 h2 h3 h4 h5 h6 h7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 m n photo default h1 h2 h3 h4 h5 h6 h7
      | exact proof_of_solver_entail_wit_1_split_goal_2 m n photo default h1 h2 h3 h4 h5 h6 h7
      | exact proof_of_solver_entail_wit_1_split_goal_3 m n photo default h1 h2 h3 h4 h5 h6 h7
      | exact proof_of_solver_entail_wit_1_split_goal_4 m n photo default h1 h2 h3 h4 h5 h6 h7

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro m n photo i default h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hn : ¬ HasColor photo := by
    intro hc
    rcases (has_color_concat_characterization__results photo).mp hc with ⟨c, hc, hp⟩
    rcases In_Znth_Zlength__results (concat photo) c 0 hc with ⟨k, hk, he⟩
    have hkflat : 0 ≤ k ∧ k < Zlength (List.flatten photo) := hk
    have hh := h12 k (by omega)
    rw [he] at hh
    rcases hp with hp | hp | hp
    · exact hh.1.1 hp
    · exact hh.1.2 hp
    · exact hh.2 hp
  have hs : Spec photo false := Or.inr ⟨rfl, hn⟩
  have hb : SolverReturnBridge false 0 := Or.inr ⟨rfl, rfl⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) false ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | exact hb

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro m n photo i default h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  have hc : HasColor photo := by
    apply (has_color_concat_characterization__results photo).mpr
    exact ⟨Znth i (concat photo) 0, Znth_In_range__results (List.flatten photo) i 0 (by omega), Or.inr (Or.inl h1)⟩
  have hs : Spec photo true := Or.inl ⟨rfl, hc⟩
  have hb : SolverReturnBridge true 1 := Or.inl ⟨rfl, rfl⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) true ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | exact hb

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  unfold solver_return_wit_3
  right
  intro m n photo i default h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have hc : HasColor photo := by
    apply (has_color_concat_characterization__results photo).mpr
    exact ⟨Znth i (concat photo) 0, Znth_In_range__results (List.flatten photo) i 0 (by omega), Or.inl h1⟩
  have hs : Spec photo true := Or.inl ⟨rfl, hc⟩
  have hb : SolverReturnBridge true 1 := Or.inl ⟨rfl, rfl⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) true ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | exact hb

theorem proof_of_solver_return_wit_4 : solver_return_wit_4 := by
  unfold solver_return_wit_4
  right
  intro m n photo i default h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  have hc : HasColor photo := by
    apply (has_color_concat_characterization__results photo).mpr
    exact ⟨Znth i (concat photo) 0, Znth_In_range__results (List.flatten photo) i 0 (by omega), Or.inr (Or.inr h1)⟩
  have hs : Spec photo true := Or.inl ⟨rfl, hc⟩
  have hb : SolverReturnBridge true 1 := Or.inl ⟨rfl, rfl⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) true ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | exact hb

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_proof_manual
