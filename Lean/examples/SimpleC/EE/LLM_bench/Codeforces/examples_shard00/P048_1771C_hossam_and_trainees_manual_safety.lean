import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_goal

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_proof_manual
open AUXLib MaxMinLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray

theorem proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1 := by
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hb := (complete_prime_table_index_bounds__safety_prime_bounds prime_data j PreH19 ⟨by omega,by omega⟩).2
  have hs := bounded_prime_square_int64__safety_prime_bounds _ hb
  dump_pre_spatial
  omega

theorem proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2 := by
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  dump_pre_spatial
  have hh := mul_self_nonneg (Znth j prime_data 0)
  omega

theorem proof_of_solver_safety_wit_19 : solver_safety_wit_19 := by
  unfold solver_safety_wit_19
  right
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pures <;> first
    | exact proof_of_solver_safety_wit_19_split_goal_1 n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
    | exact proof_of_solver_safety_wit_19_split_goal_2 n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_solver_safety_wit_20_split_goal_1 : solver_safety_wit_20_split_goal_1 := by
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  left
  simp only [INT_MIN]
  omega

theorem proof_of_solver_safety_wit_20_split_goal_2 : solver_safety_wit_20_split_goal_2 := by
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hb := (complete_prime_table_index_bounds__safety_prime_bounds prime_data j PreH20 ⟨by omega,by omega⟩).2
  dump_pre_spatial
  omega

theorem proof_of_solver_safety_wit_20 : solver_safety_wit_20 := by
  unfold solver_safety_wit_20
  right
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pures <;> first
    | exact proof_of_solver_safety_wit_20_split_goal_1 n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    | exact proof_of_solver_safety_wit_20_split_goal_2 n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1 := by
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  dump_pre_spatial
  left
  simp only [INT_MIN]
  omega

theorem proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2 := by
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hh := (factor_divide_state_current_prime__safety_prime_bounds a prime_data i j x factor_data PreH20).2
  dump_pre_spatial
  exact hh

theorem proof_of_solver_safety_wit_23 : solver_safety_wit_23 := by
  unfold solver_safety_wit_23
  right
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pures <;> first
    | exact proof_of_solver_safety_wit_23_split_goal_1 n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
    | exact proof_of_solver_safety_wit_23_split_goal_2 n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1 := by
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  dump_pre_spatial
  left
  simp only [INT_MIN]
  omega

theorem proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2 := by
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hh := (factor_divide_state_current_prime__safety_prime_bounds a prime_data i j x factor_data PreH21).2
  dump_pre_spatial
  exact hh

theorem proof_of_solver_safety_wit_25 : solver_safety_wit_25 := by
  unfold solver_safety_wit_25
  right
  intro n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pures <;> first
    | exact proof_of_solver_safety_wit_25_split_goal_1 n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    | exact proof_of_solver_safety_wit_25_split_goal_2 n_pre values_pre a factors factor_data count composite_data prime_data x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_proof_manual
