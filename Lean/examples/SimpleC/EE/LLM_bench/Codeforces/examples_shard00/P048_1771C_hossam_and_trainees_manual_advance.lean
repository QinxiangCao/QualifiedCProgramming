import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_manual_factors

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

theorem proof_of_solver_entail_wit_9_1_split_goal_1 : solver_entail_wit_9_1_split_goal_1 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hn := factor_divide2_to_scan2_next__factor_scan_advance a prime_data_2 i j x factor_data_2 PreH19 PreH21 PreH1
  exact factor_scan2_capacity_next__factor_scan_advance a prime_data_2 i (j+1) x factor_data_2 count
    PreH19 hn (pointwise_bounds_Forall__factor_scan_advance a PreH5) PreH16

theorem proof_of_solver_entail_wit_9_1_split_goal_2 : solver_entail_wit_9_1_split_goal_2 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact factor_divide2_to_scan2_next__factor_scan_advance a prime_data_2 i j x factor_data_2 PreH19 PreH21 PreH1

theorem proof_of_solver_entail_wit_9_1_split_goal_3 : solver_entail_wit_9_1_split_goal_3 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact FactorScanState2_implies_FactorScanState _ _ _ _ _ _ (factor_divide2_to_scan2_next__factor_scan_advance a prime_data_2 i j x factor_data_2 PreH19 PreH21 PreH1)

theorem proof_of_solver_entail_wit_9_1_split_goal_4 : solver_entail_wit_9_1_split_goal_4 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact PreH5

theorem proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1 := by
  unfold solver_entail_wit_9_1
  right
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_9_1_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    | exact proof_of_solver_entail_wit_9_1_split_goal_2 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    | exact proof_of_solver_entail_wit_9_1_split_goal_3 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    | exact proof_of_solver_entail_wit_9_1_split_goal_4 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_9_2_split_goal_1 : solver_entail_wit_9_2_split_goal_1 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hn := factor_scan2_to_scan2_next__factor_scan_advance a prime_data_2 i j x factor_data_2 PreH21 PreH23 ⟨by omega,by omega⟩ PreH1
  exact factor_scan2_capacity_next__factor_scan_advance a prime_data_2 i (j+1) x factor_data_2 count
    PreH21 hn (pointwise_bounds_Forall__factor_scan_advance a PreH7) PreH18

theorem proof_of_solver_entail_wit_9_2_split_goal_2 : solver_entail_wit_9_2_split_goal_2 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact factor_scan2_to_scan2_next__factor_scan_advance a prime_data_2 i j x factor_data_2 PreH21 PreH23 ⟨by omega,by omega⟩ PreH1

theorem proof_of_solver_entail_wit_9_2_split_goal_3 : solver_entail_wit_9_2_split_goal_3 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact FactorScanState2_implies_FactorScanState _ _ _ _ _ _ (factor_scan2_to_scan2_next__factor_scan_advance a prime_data_2 i j x factor_data_2 PreH21 PreH23 ⟨by omega,by omega⟩ PreH1)

theorem proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2 := by
  unfold solver_entail_wit_9_2
  right
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_9_2_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_9_2_split_goal_2 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_9_2_split_goal_3 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply factor_scan2_residual_complete__factor_item_finish a prime_data_2 i j x factor_data_2 PreH22
  obtain ⟨done,picked,hf,hbag,hi,hj,hb,hd,hnd,hprime,hpicked,hex,hcover⟩ := PreH22
  exact residual_prime_exhausted__factor_item_finish prime_data_2 j x PreH20
    ⟨by omega,by omega⟩ hex ⟨by omega,by omega⟩ (by omega)

theorem proof_of_solver_entail_wit_10_1_split_goal_2 : solver_entail_wit_10_1_split_goal_2 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  rw [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_solver_entail_wit_10_1_split_goal_3 : solver_entail_wit_10_1_split_goal_3 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact PreH6

theorem proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1 := by
  unfold solver_entail_wit_10_1
  right
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_10_1_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    | exact proof_of_solver_entail_wit_10_1_split_goal_2 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    | exact proof_of_solver_entail_wit_10_1_split_goal_3 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  apply factor_scan2_residual_complete__factor_item_finish a prime_data_2 i j x factor_data_2 PreH23
  obtain ⟨done,picked,hf,hbag,hi,hj,hb,hd,hnd,hprime,hpicked,hex,hcover⟩ := PreH23
  exact residual_prime_square_cutoff__factor_item_finish prime_data_2 j x PreH21
    ⟨by omega,by omega⟩ hex ⟨by omega,by omega⟩ PreH2

theorem proof_of_solver_entail_wit_10_2_split_goal_2 : solver_entail_wit_10_2_split_goal_2 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  rw [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem proof_of_solver_entail_wit_10_2_split_goal_3 : solver_entail_wit_10_2_split_goal_3 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact PreH7

theorem proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2 := by
  unfold solver_entail_wit_10_2
  right
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_10_2_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_10_2_split_goal_2 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_10_2_split_goal_3 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_entail_wit_10_3_split_goal_1 : solver_entail_wit_10_3_split_goal_1 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact factor_scan2_unit_complete__factor_item_finish a prime_data_2 i j x factor_data_2 PreH22 (by omega)

theorem proof_of_solver_entail_wit_10_3_split_goal_2 : solver_entail_wit_10_3_split_goal_2 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact PreH6

theorem proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3 := by
  unfold solver_entail_wit_10_3
  right
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_10_3_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    | exact proof_of_solver_entail_wit_10_3_split_goal_2 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_solver_entail_wit_10_4_split_goal_1 : solver_entail_wit_10_4_split_goal_1 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact factor_scan2_unit_complete__factor_item_finish a prime_data_2 i j x factor_data_2 PreH23 (by omega)

theorem proof_of_solver_entail_wit_10_4_split_goal_2 : solver_entail_wit_10_4_split_goal_2 := by
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  exact PreH7

theorem proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4 := by
  unfold solver_entail_wit_10_4
  right
  intro n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_10_4_split_goal_1 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_10_4_split_goal_2 n_pre a factor_data_2 count composite_data_2 prime_data_2 x pc j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_proof_manual
