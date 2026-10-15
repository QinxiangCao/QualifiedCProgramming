import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_proof_auto
import ListLib.General.Length

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P021_2030C_a_true_battle_goal P021_2030C_a_true_battle_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem nth_append (d : Int) (l l' : List Int) (i : Int)
    (h : 0 ≤ i ∧ i < Zlength l) : Znth i (l ++ l') d = Znth i l d :=
  ListLib.app_Znth1 d l l' i h

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  intro k hk
  omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  rwa [nth_append 0 values [0] (n_pre - 1) (by omega)] at PreH1

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  rwa [nth_append 0 values [0] 0 (by omega)] at PreH2

theorem proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4 := by
  intro n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact PreH6

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
      | exact proof_of_solver_entail_wit_1_split_goal_2 n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
      | exact proof_of_solver_entail_wit_1_split_goal_3 n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
      | exact proof_of_solver_entail_wit_1_split_goal_4 n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  apply no_adjacent_ones_before_succ__loop_transition values i PreH9 PreH11
  left
  rwa [nth_append 0 values [0] i (by omega)] at PreH1

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  unfold solver_entail_wit_2_1
  right
  intro n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_1_split_goal_1 n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  apply no_adjacent_ones_before_succ__loop_transition values i PreH10 PreH12
  right
  rwa [nth_append 0 values [0] (i + 1) (by omega)] at PreH1

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  unfold solver_entail_wit_2_2
  right
  intro n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_2_2_split_goal_1 n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact spec_zero_from_completed_scan__final_results values n_pre i PreH2 PreH8 PreH9 PreH1 PreH6 PreH7 PreH10

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_1_split_goal_1 n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  intro n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  rw [nth_append 0 values [0] (i + 1) (by omega)] at PreH1
  rw [nth_append 0 values [0] i (by omega)] at PreH2
  exact ⟨Or.inr rfl, ⟨fun _ => Or.inr (Or.inr ⟨i, PreH10, by omega, PreH2, PreH1⟩), fun _ => rfl⟩⟩

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_2_split_goal_1 n_pre values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1 := by
  intro n_pre values PreH1 PreH2 PreH3 PreH4 PreH5
  rw [nth_append 0 values [0] 0 (by omega)] at PreH1
  exact ⟨Or.inr rfl, ⟨fun _ => Or.inl PreH1, fun _ => rfl⟩⟩

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  unfold solver_return_wit_3
  right
  intro n_pre values PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_3_split_goal_1 n_pre values PreH1 PreH2 PreH3 PreH4 PreH5

theorem proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1 := by
  intro n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  rw [nth_append 0 values [0] (n_pre - 1) (by omega), PreH3] at PreH1
  exact ⟨Or.inr rfl, ⟨fun _ => Or.inr (Or.inl PreH1), fun _ => rfl⟩⟩

theorem proof_of_solver_return_wit_4 : solver_return_wit_4 := by
  unfold solver_return_wit_4
  right
  intro n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_4_split_goal_1 n_pre values PreH1 PreH2 PreH3 PreH4 PreH5 PreH6

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_proof_manual
