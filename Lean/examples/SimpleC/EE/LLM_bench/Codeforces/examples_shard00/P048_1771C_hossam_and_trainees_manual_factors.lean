import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_manual_sieve

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

theorem proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1 := by
  intro n_pre a composite_data_2 prime_data_2 pc i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact prime_factor_bag_prefix_zero__sieve_marking_exits a

theorem proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2 := by
  intro n_pre a composite_data_2 prime_data_2 pc i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have he : i = 31624 := by omega
  rw [he] at PreH13
  exact prime_prefix_table2_complete__sieve_marking_exits prime_data_2 composite_data_2 PreH13

theorem proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3 := by
  intro n_pre a composite_data_2 prime_data_2 pc i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rfl

theorem proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4 := by
  intro n_pre a composite_data_2 prime_data_2 pc i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH6

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  unfold solver_entail_wit_5
  right
  intro n_pre a composite_data_2 prime_data_2 pc i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_5_split_goal_1 n_pre a composite_data_2 prime_data_2 pc i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    | exact proof_of_solver_entail_wit_5_split_goal_2 n_pre a composite_data_2 prime_data_2 pc i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    | exact proof_of_solver_entail_wit_5_split_goal_3 n_pre a composite_data_2 prime_data_2 pc i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    | exact proof_of_solver_entail_wit_5_split_goal_4 n_pre a composite_data_2 prime_data_2 pc i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  intro hh
  omega

theorem proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact factor_scan_state2_initial__factor_scan_divide a prime_data_2 i factor_data_2 PreH16 ⟨by omega,by omega⟩ (PreH5 i ⟨by omega,by omega⟩).1

theorem proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact FactorScanState2_implies_FactorScanState _ _ _ _ _ _
    (proof_of_solver_entail_wit_6_split_goal_2 n_pre a factor_data_2 count composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)

theorem proof_of_solver_entail_wit_6_split_goal_4 : solver_entail_wit_6_split_goal_4 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact PreH5

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_6_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    | exact proof_of_solver_entail_wit_6_split_goal_2 n_pre a factor_data_2 count composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    | exact proof_of_solver_entail_wit_6_split_goal_3 n_pre a factor_data_2 count composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    | exact proof_of_solver_entail_wit_6_split_goal_4 n_pre a factor_data_2 count composite_data_2 prime_data_2 pc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hd := complete_prime_table_mod_zero_divides__factor_scan_divide prime_data_2 j x PreH21 ⟨by omega,by omega⟩ PreH1
  exact factor_scan_state2_append_divisor__factor_scan_divide a prime_data_2 i j x factor_data_2 PreH21 PreH23 ⟨by omega,by omega⟩ hd

theorem proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact FactorDivideState2_implies_FactorDivideState _ _ _ _ _ _
    (proof_of_solver_entail_wit_7_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24)

theorem proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hd := complete_prime_table_mod_zero_divides__factor_scan_divide prime_data_2 j x PreH21 ⟨by omega,by omega⟩ PreH1
  exact PreH24 ⟨⟨by omega,by omega⟩,hd⟩

theorem proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  rw [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_solver_entail_wit_7_split_goal_5 : solver_entail_wit_7_split_goal_5 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact PreH7

theorem proof_of_solver_entail_wit_7 : solver_entail_wit_7 := by
  unfold solver_entail_wit_7
  right
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_7_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_7_split_goal_2 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_7_split_goal_3 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_7_split_goal_4 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_7_split_goal_5 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hd := complete_prime_table_mod_zero_divides__factor_scan_divide prime_data_2 j x PreH19 ⟨by omega,by omega⟩ PreH1
  exact factor_divide_state2_reduce__factor_scan_divide a prime_data_2 i j x factor_data_2 PreH21 hd

theorem proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact FactorDivideState2_implies_FactorDivideState _ _ _ _ _ _
    (proof_of_solver_entail_wit_8_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21)

theorem proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hred := proof_of_solver_entail_wit_8_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  obtain ⟨done,picked,p,hf,hbag,hi,hj,hp,hprime,hdiv,hbounds,hrest⟩ := hred
  have he := Znth_indep a i 0 1 hi
  have hb := (PreH5 i hi).2
  omega

theorem proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hred := proof_of_solver_entail_wit_8_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  obtain ⟨done,picked,p,hf,hbag,hi,hj,hp,hprime,hdiv,hbounds,hrest⟩ := hred
  exact hbounds.1

theorem proof_of_solver_entail_wit_8 : solver_entail_wit_8 := by
  unfold solver_entail_wit_8
  right
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_8_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    | exact proof_of_solver_entail_wit_8_split_goal_2 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    | exact proof_of_solver_entail_wit_8_split_goal_3 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    | exact proof_of_solver_entail_wit_8_split_goal_4 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_proof_manual
