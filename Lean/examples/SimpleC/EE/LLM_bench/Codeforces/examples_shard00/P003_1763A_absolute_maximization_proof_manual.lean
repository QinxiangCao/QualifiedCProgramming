import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_goal
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n_pre input PreH1 PreH2 PreH3 PreH4
  apply bitwise_scan_state_zero__scan_core
  omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n_pre input PreH1 PreH2 PreH3 PreH4
  intro k hk
  exact PreH4 k (by omega)

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro n_pre input PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n_pre input PreH1 PreH2 PreH3 PreH4
      | exact proof_of_solver_entail_wit_1_split_goal_2 n_pre input PreH1 PreH2 PreH3 PreH4

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  apply bitwise_scan_state_succ__scan_core
  · omega
  · exact PreH12

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hi := PreH7 i (by omega)
  have hb := bounded_lor_land__scan_core all_and (Znth i input 0) (by omega) (by omega)
  omega

theorem proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3 := by
  intro n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hi := PreH7 i (by omega)
  have hb := bounded_lor_land__scan_core all_and (Znth i input 0) (by omega) (by omega)
  omega

theorem proof_of_solver_entail_wit_2_split_goal_4 : solver_entail_wit_2_split_goal_4 := by
  intro n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hi := PreH7 i (by omega)
  have hb := bounded_lor_land__scan_core all_or (Znth i input 0) (by omega) (by omega)
  omega

theorem proof_of_solver_entail_wit_2_split_goal_5 : solver_entail_wit_2_split_goal_5 := by
  intro n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hi := PreH7 i (by omega)
  have hb := bounded_lor_land__scan_core all_or (Znth i input 0) (by omega) (by omega)
  omega

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  right
  intro n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_2_split_goal_2 n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_2_split_goal_3 n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_2_split_goal_4 n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_2_split_goal_5 n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : i=n_pre := by omega
  rw [he] at PreH12
  apply bitwise_scan_final_implies_spec__final_result n_pre input all_or all_and
  all_goals solve | omega | exact PreH12 | exact PreH7

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_1_split_goal_1 n_pre input all_and all_or i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_proof_manual
