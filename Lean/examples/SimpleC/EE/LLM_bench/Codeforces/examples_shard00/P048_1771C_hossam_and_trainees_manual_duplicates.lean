import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_manual_advance

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

theorem proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1 := by
  intro n_pre a factor_data count composite_data_2 prime_data_2 pc i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  exact duplicate_scan_loop_initial__duplicate_init_result sorted_2 count PreH3 PreH16

theorem proof_of_solver_entail_wit_11_split_goal_2 : solver_entail_wit_11_split_goal_2 := by
  intro n_pre a factor_data count composite_data_2 prime_data_2 pc i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have he : i = n_pre := by omega
  rw [he] at PreH19
  exact prime_factor_bag_prefix_permutation__duplicate_init_result a n_pre factor_data sorted_2 PreH1 PreH19

theorem proof_of_solver_entail_wit_11 : solver_entail_wit_11 := by
  unfold solver_entail_wit_11
  right
  intro n_pre a factor_data count composite_data_2 prime_data_2 pc i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_11_split_goal_1 n_pre a factor_data count composite_data_2 prime_data_2 pc i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_solver_entail_wit_11_split_goal_2 n_pre a factor_data count composite_data_2 prime_data_2 pc i sorted_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1 := by
  intro n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  apply prime_factor_duplicate_spec__duplicate_init_result a sorted_2 count ok PreH13
  · rwa [← PreH2]
  · exact duplicate_scan_loop_exit__duplicate_init_result sorted_2 count i ok PreH1 PreH16

theorem proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2 := by
  intro n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact duplicate_scan_loop_exit__duplicate_init_result sorted_2 count i ok PreH1 PreH16

theorem proof_of_solver_entail_wit_12 : solver_entail_wit_12 := by
  unfold solver_entail_wit_12
  right
  intro n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_12_split_goal_1 n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    | exact proof_of_solver_entail_wit_12_split_goal_2 n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_solver_entail_wit_13_1_split_goal_1 : solver_entail_wit_13_1_split_goal_1 := by
  intro n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact duplicate_scan_equal_step__duplicate_loop sorted_2 count i ok PreH14 PreH17 PreH8 PreH2 PreH1

theorem proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1 := by
  unfold solver_entail_wit_13_1
  right
  intro n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_13_1_split_goal_1 n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_13_2_split_goal_1 : solver_entail_wit_13_2_split_goal_1 := by
  intro n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact duplicate_scan_unequal_step__duplicate_loop sorted_2 count i ok PreH14 PreH15 PreH17 PreH8 PreH2 PreH1

theorem proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2 := by
  unfold solver_entail_wit_13_2
  right
  intro n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_13_2_split_goal_1 n_pre a ok sorted_2 composite_data_2 prime_data_2 pc i count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_14_split_goal_spatial : solver_entail_wit_14_split_goal_spatial := by
  intro n_pre a prime_data composite_data sorted count pc ok PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  sep_apply (intArray.full_to_undef_full (&("primes")) pc prime_data)
  sep_apply (intArray.undef_full_to_undef_seg (&("primes")) pc)
  sep_apply (intArray.undef_seg_merge_to_undef_full (&("primes")) 0 pc 4000 ⟨by omega,by omega⟩)
  simp only [zero_mul,add_zero,sub_zero]
  sep_apply (ucharArray.full_to_undef_full (&("composite")) 31624 composite_data)
  exact (naive_C_Rules.toContext.logic_equiv_sepcon_comm _ _).1

theorem proof_of_solver_entail_wit_14 : solver_entail_wit_14 := by
  unfold solver_entail_wit_14
  right
  intro n_pre a prime_data composite_data sorted count pc ok PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact proof_of_solver_entail_wit_14_split_goal_spatial n_pre a prime_data composite_data sorted count pc ok PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_proof_manual
