import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_goal
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private theorem rem_signed (x : Int) (hx : 0≤x) : signed_last_nbits (Z.rem x 10) 32=Z.rem x 10 := by
  have hh:=signed_decimal_remainder_bounds__step_transitions x hx
  apply signed_last_nbits_eq _ _ (by omega)
  change -2147483648≤Z.rem x 10 ∧ Z.rem x 10<2147483648
  omega

theorem proof_of_step_entail_wit_1_split_goal_1 : step_entail_wit_1_split_goal_1 := by
  intro x_pre PreH1 PreH2
  exact digit_scan_state_initial__step_initialization x_pre PreH1

theorem proof_of_step_entail_wit_1 : step_entail_wit_1 := by
  right
  intro x_pre PreH1 PreH2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_step_entail_wit_1_split_goal_1 x_pre PreH1 PreH2

theorem proof_of_step_entail_wit_2_1_split_goal_1 : step_entail_wit_2_1_split_goal_1 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hsigned:=rem_signed x PreH5
  simp only [hsigned] at PreH1 PreH2 ⊢
  have hh:=digit_scan_state_advance__step_transitions x_pre x mn mx PreH11 PreH5 PreH12
  simpa only [min_eq_right (by omega : Z.rem x 10≤mn), max_eq_right (by omega : mx≤Z.rem x 10)] using hh

theorem proof_of_step_entail_wit_2_1_split_goal_2 : step_entail_wit_2_1_split_goal_2 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  change Int.tdiv x 10≤x_pre
  rw [Int.tdiv_eq_ediv_of_nonneg PreH5]
  omega

theorem proof_of_step_entail_wit_2_1_split_goal_3 : step_entail_wit_2_1_split_goal_3 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  change 0≤Int.tdiv x 10
  rw [Int.tdiv_eq_ediv_of_nonneg PreH5]
  omega

theorem proof_of_step_entail_wit_2_1 : step_entail_wit_2_1 := by
  right
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_step_entail_wit_2_1_split_goal_1 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_step_entail_wit_2_1_split_goal_2 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_step_entail_wit_2_1_split_goal_3 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_step_entail_wit_2_2_split_goal_1 : step_entail_wit_2_2_split_goal_1 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hsigned:=rem_signed x PreH5
  simp only [hsigned] at PreH1 PreH2 ⊢
  have hh:=digit_scan_state_advance__step_transitions x_pre x mn mx PreH11 PreH5 PreH12
  simpa only [min_eq_left (by omega : mn≤Z.rem x 10), max_eq_right (by omega : mx≤Z.rem x 10)] using hh

theorem proof_of_step_entail_wit_2_2_split_goal_2 : step_entail_wit_2_2_split_goal_2 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hh:=signed_decimal_remainder_bounds__step_transitions x PreH5
  rw [rem_signed x PreH5]
  omega

theorem proof_of_step_entail_wit_2_2_split_goal_3 : step_entail_wit_2_2_split_goal_3 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  change Int.tdiv x 10≤x_pre
  rw [Int.tdiv_eq_ediv_of_nonneg PreH5]
  omega

theorem proof_of_step_entail_wit_2_2_split_goal_4 : step_entail_wit_2_2_split_goal_4 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  change 0≤Int.tdiv x 10
  rw [Int.tdiv_eq_ediv_of_nonneg PreH5]
  omega

theorem proof_of_step_entail_wit_2_2 : step_entail_wit_2_2 := by
  right
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_step_entail_wit_2_2_split_goal_1 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_step_entail_wit_2_2_split_goal_2 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_step_entail_wit_2_2_split_goal_3 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_step_entail_wit_2_2_split_goal_4 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_step_entail_wit_2_3_split_goal_1 : step_entail_wit_2_3_split_goal_1 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hsigned:=rem_signed x PreH5
  simp only [hsigned] at PreH1 PreH2 ⊢
  have hh:=digit_scan_state_advance__step_transitions x_pre x mn mx PreH11 PreH5 PreH12
  simpa only [min_eq_right (by omega : Z.rem x 10≤mn), max_eq_left (by omega : Z.rem x 10≤mx)] using hh

theorem proof_of_step_entail_wit_2_3_split_goal_2 : step_entail_wit_2_3_split_goal_2 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hh:=signed_decimal_remainder_bounds__step_transitions x PreH5
  rw [rem_signed x PreH5]
  omega

theorem proof_of_step_entail_wit_2_3_split_goal_3 : step_entail_wit_2_3_split_goal_3 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  change Int.tdiv x 10≤x_pre
  rw [Int.tdiv_eq_ediv_of_nonneg PreH5]
  omega

theorem proof_of_step_entail_wit_2_3_split_goal_4 : step_entail_wit_2_3_split_goal_4 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  change 0≤Int.tdiv x 10
  rw [Int.tdiv_eq_ediv_of_nonneg PreH5]
  omega

theorem proof_of_step_entail_wit_2_3 : step_entail_wit_2_3 := by
  right
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_step_entail_wit_2_3_split_goal_1 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_step_entail_wit_2_3_split_goal_2 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_step_entail_wit_2_3_split_goal_3 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_step_entail_wit_2_3_split_goal_4 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_step_entail_wit_2_4_split_goal_1 : step_entail_wit_2_4_split_goal_1 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hsigned:=rem_signed x PreH5
  simp only [hsigned] at PreH1 PreH2 ⊢
  have hh:=digit_scan_state_advance__step_transitions x_pre x mn mx PreH11 PreH5 PreH12
  simpa only [min_eq_left (by omega : mn≤Z.rem x 10), max_eq_left (by omega : Z.rem x 10≤mx)] using hh

theorem proof_of_step_entail_wit_2_4_split_goal_2 : step_entail_wit_2_4_split_goal_2 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  change Int.tdiv x 10≤x_pre
  rw [Int.tdiv_eq_ediv_of_nonneg PreH5]
  omega

theorem proof_of_step_entail_wit_2_4_split_goal_3 : step_entail_wit_2_4_split_goal_3 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  change 0≤Int.tdiv x 10
  rw [Int.tdiv_eq_ediv_of_nonneg PreH5]
  omega

theorem proof_of_step_entail_wit_2_4 : step_entail_wit_2_4 := by
  right
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_step_entail_wit_2_4_split_goal_1 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_step_entail_wit_2_4_split_goal_2 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_step_entail_wit_2_4_split_goal_3 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_step_return_wit_1_split_goal_1 : step_return_wit_1_split_goal_1 := by
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rw [PreH10] at PreH9
  exact digit_scan_state_complete__step_finalization x_pre mn mx PreH9

theorem proof_of_step_return_wit_1 : step_return_wit_1 := by
  right
  intro x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_step_return_wit_1_split_goal_1 x_pre mx mn x PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro k_pre a_pre a1 PreH1 PreH2 PreH3 PreH4 PreH5
  exact sequence_prefix_base__solver_prefix a_pre

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro k_pre a_pre a1 PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 k_pre a_pre a1 PreH1 PreH2 PreH3 PreH4 PreH5

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro k_pre a_pre a1 a i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  rw [PreH6]
  rw [PreH1,Int.add_zero] at PreH4
  exact sequence_fixed_point_spec__solver_results a1 i k_pre a PreH11 PreH12 PreH16 PreH4

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  right
  intro k_pre a_pre a1 a i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 k_pre a_pre a1 a i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro k_pre a_pre a1 a i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  rw [PreH6]
  exact sequence_prefix_extend__solver_prefix a1 i a (a+retval) PreH11 PreH16 PreH4

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  right
  intro k_pre a_pre a1 a i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_3_split_goal_1 k_pre a_pre a1 a i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro k_pre a_pre a1 a i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  rw [PreH2,show k_pre=i by omega]
  exact sequence_prefix_index_spec__solver_results a1 i a PreH12

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro k_pre a_pre a1 a i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_1_split_goal_1 k_pre a_pre a1 a i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_proof_manual
