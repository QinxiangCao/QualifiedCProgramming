import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P030_1220C_substring_game_in_the_lesson_goal P030_1220C_substring_game_in_the_lesson_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev charArray := naive_C_Rules.CharArray

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n text h1 h2 h3 h4
  exact ⟨rfl,fun i hi => False.elim (by omega)⟩

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n text h1 h2 h3 h4
  exact ⟨⟨by omega,by omega⟩,Or.inl ⟨rfl,rfl⟩⟩

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro n text h1 h2 h3 h4
  exact h3

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n text h1 h2 h3 h4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n text h1 h2 h3 h4
      | exact proof_of_solver_entail_wit_1_split_goal_2 n text h1 h2 h3 h4
      | exact proof_of_solver_entail_wit_1_split_goal_3 n text h1 h2 h3 h4

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  apply spec_prefix_snoc__prefix_transitions text k out 0 h11 h8
  have hc := (h6 k ⟨h8,h3⟩).2
  have he := ann_wins_iff_prefix_min_lt__prefix_transitions text k mn (by omega) hc h10
  exact Or.inr ⟨rfl,fun hw => by have hh:=he.mp hw;omega⟩

theorem proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2 := by
  intro n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have hs := prefix_minimum_step__prefix_transitions text k mn (by omega) (h6 k ⟨h8,h3⟩).2 h10
  rw [min_eq_right (by omega)] at hs
  exact hs

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  unfold solver_entail_wit_2_1
  right
  intro n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_1_split_goal_1 n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      | exact proof_of_solver_entail_wit_2_1_split_goal_2 n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  apply spec_prefix_snoc__prefix_transitions text k out 0 h11 h8
  have hc := (h6 k ⟨h8,h3⟩).2
  have he := ann_wins_iff_prefix_min_lt__prefix_transitions text k mn (by omega) hc h10
  exact Or.inr ⟨rfl,fun hw => by have hh:=he.mp hw;omega⟩

theorem proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2 := by
  intro n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have hs := prefix_minimum_step__prefix_transitions text k mn (by omega) (h6 k ⟨h8,h3⟩).2 h10
  rw [min_eq_left (by omega)] at hs
  exact hs

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  unfold solver_entail_wit_2_2
  right
  intro n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_2_split_goal_1 n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      | exact proof_of_solver_entail_wit_2_2_split_goal_2 n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1 := by
  intro n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  apply spec_prefix_snoc__prefix_transitions text k out 1 h11 h8
  have hc := (h6 k ⟨h8,h3⟩).2
  have he := ann_wins_iff_prefix_min_lt__prefix_transitions text k mn (by omega) hc h10
  exact Or.inl ⟨rfl,he.mpr h2⟩

theorem proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2 := by
  intro n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have hs := prefix_minimum_step__prefix_transitions text k mn (by omega) (h6 k ⟨h8,h3⟩).2 h10
  rw [min_eq_left (by omega)] at hs
  exact hs

theorem proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3 := by
  unfold solver_entail_wit_2_3
  right
  intro n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_3_split_goal_1 n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      | exact proof_of_solver_entail_wit_2_3_split_goal_2 n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro win n text out mn k h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hk : k=n := by omega
  subst k
  Exists out
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact ⟨h9.1.trans h5,fun i hi => h9.2 i (by omega)⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_proof_manual
