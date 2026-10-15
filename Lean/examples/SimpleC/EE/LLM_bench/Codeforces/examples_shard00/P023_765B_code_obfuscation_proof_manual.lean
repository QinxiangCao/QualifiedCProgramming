import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_goal
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro text PreH1 PreH2 PreH3
  exact obfuscation_prefix_init__initialization text PreH1 PreH3

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro text PreH1 PreH2 PreH3
  exact PreH3

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro text PreH1 PreH2 PreH3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 text PreH1 PreH2 PreH3
      | exact proof_of_solver_entail_wit_1_split_goal_2 text PreH1 PreH2 PreH3

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hi:=app_zero_nonzero_index_lt_length__prefix_transitions text i (by omega) PreH12
  rw [nth_app_left text [0] i (by omega)] at PreH2
  exact obfuscation_prefix_step_equal_increment__prefix_transitions text i next (by omega) PreH2 PreH1 PreH11

theorem proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2 := by
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hi:=app_zero_nonzero_index_lt_length__prefix_transitions text i (by omega) PreH12
  omega

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  right
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_1_split_goal_1 text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_2_1_split_goal_2 text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hi:=app_zero_nonzero_index_lt_length__prefix_transitions text i (by omega) PreH11
  rw [nth_app_left text [0] i (by omega)] at PreH1 PreH2
  exact obfuscation_prefix_step_below__prefix_transitions text i next (by omega) (PreH5 i (by omega)).1 PreH2 PreH1 PreH10

theorem proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2 := by
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hi:=app_zero_nonzero_index_lt_length__prefix_transitions text i (by omega) PreH11
  omega

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  right
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_2_split_goal_1 text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_solver_entail_wit_2_2_split_goal_2 text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1 := by
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hi:=app_zero_nonzero_index_lt_length__prefix_transitions text i (by omega) PreH12
  rw [nth_app_left text [0] i (by omega)] at PreH2
  exact obfuscation_prefix_step_max__prefix_transitions text i next (by omega) PreH2 PreH1 PreH10 PreH11

theorem proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2 := by
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hi:=app_zero_nonzero_index_lt_length__prefix_transitions text i (by omega) PreH12
  omega

theorem proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3 := by
  right
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_3_split_goal_1 text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_2_3_split_goal_2 text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have he:=app_zero_terminator_index_eq_length__final_results text i (fun k hk=>(PreH3 k hk).1) (by omega) PreH9
  rw [he] at PreH8
  exact obfuscation_prefix_success_spec__final_results text next PreH3 PreH8

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_1_split_goal_1 text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact obfuscation_prefix_failure_spec__final_results text next i PreH1 PreH4 (by omega) (by omega) PreH9 PreH10

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  right
  intro text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_2_split_goal_1 text next i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_proof_manual
