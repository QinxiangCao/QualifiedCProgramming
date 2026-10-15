import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_goal
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n_pre input PreH1 PreH2 PreH3 PreH4
  refine ⟨⟨[],rfl,List.nodup_nil,?_⟩,Or.inl ⟨rfl,rfl⟩⟩
  intro i
  simp only [List.not_mem_nil,false_iff]
  intro h
  omega

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n_pre input PreH1 PreH2 PreH3 PreH4
  exact PreH4

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro n_pre input PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n_pre input PreH1 PreH2 PreH3 PreH4
      | exact proof_of_solver_entail_wit_1_split_goal_2 n_pre input PreH1 PreH2 PreH3 PreH4

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact scan_state_step_zero__scan_state_transitions input i runs inside (by omega) PreH1 PreH14

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  right
  intro n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_1_split_goal_1 n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  rw [PreH2] at PreH15
  exact scan_state_step_new_run__scan_state_transitions input i runs (by omega) PreH1 PreH15

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  right
  intro n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_2_split_goal_1 n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1 := by
  intro n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  apply scan_state_step_inside_run__scan_state_transitions
  all_goals solve | assumption | omega

theorem proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3 := by
  right
  intro n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_3_split_goal_1 n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have he : i=Zlength input := by omega
  rw [he] at PreH13
  have hh:=scan_state_complete_spec__final_spec input runs inside (by omega) (fun k hk=>(PreH6 k hk).2) PreH13
  simpa only [min_eq_right (by omega : 2≤runs)] using hh

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_1_split_goal_1 n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  intro n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have he : i=Zlength input := by omega
  rw [he] at PreH13
  have hh:=scan_state_complete_spec__final_spec input runs inside (by omega) (fun k hk=>(PreH6 k hk).2) PreH13
  simpa only [min_eq_left (by omega : runs≤2)] using hh

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  right
  intro n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_2_split_goal_1 n_pre input inside runs i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_proof_manual
