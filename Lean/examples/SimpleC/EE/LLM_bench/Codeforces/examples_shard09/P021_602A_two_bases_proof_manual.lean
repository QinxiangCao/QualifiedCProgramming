import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P021_602A_two_bases_goal P021_602A_two_bases_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_numeral_value_safety_wit_4_split_goal_1 : numeral_value_safety_wit_4_split_goal_1 := by
  intro b_pre n_pre d_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have hd := PreH7 i ⟨PreH8, PreH1⟩
  have hn := pow40_successor_bound__numeral_arithmetic i v b_pre (Znth i digits 0) PreH8 ⟨PreH11, PreH12⟩ ⟨PreH4, PreH5⟩ hd
  have hm := pow40_int64_bound__numeral_arithmetic i ⟨PreH8, by omega⟩
  omega

theorem proof_of_numeral_value_safety_wit_4_split_goal_2 : numeral_value_safety_wit_4_split_goal_2 := by
  intro b_pre n_pre d_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have hd := PreH7 i ⟨PreH8, PreH1⟩
  have hm := mul_nonneg PreH11 (show 0 ≤ b_pre by omega)
  omega

theorem proof_of_numeral_value_safety_wit_4 : numeral_value_safety_wit_4 := by
  unfold numeral_value_safety_wit_4
  left
  intro b_pre n_pre d_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pures
  · exact proof_of_numeral_value_safety_wit_4_split_goal_1 b_pre n_pre d_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_numeral_value_safety_wit_4_split_goal_2 b_pre n_pre d_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_numeral_value_safety_wit_5_split_goal_1 : numeral_value_safety_wit_5_split_goal_1 := by
  intro b_pre n_pre d_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have hn := pow40_successor_bound__numeral_arithmetic i v b_pre (0) PreH8 ⟨PreH11, PreH12⟩ ⟨PreH4, PreH5⟩ ⟨by omega, by omega⟩
  have hm := pow40_int64_bound__numeral_arithmetic i ⟨PreH8, by omega⟩
  omega

theorem proof_of_numeral_value_safety_wit_5_split_goal_2 : numeral_value_safety_wit_5_split_goal_2 := by
  intro b_pre n_pre d_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  dump_pre_spatial
  have hm := mul_nonneg PreH11 (show 0 ≤ b_pre by omega)
  omega

theorem proof_of_numeral_value_safety_wit_5 : numeral_value_safety_wit_5 := by
  unfold numeral_value_safety_wit_5
  left
  intro b_pre n_pre d_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pures
  · exact proof_of_numeral_value_safety_wit_5_split_goal_1 b_pre n_pre d_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  · exact proof_of_numeral_value_safety_wit_5_split_goal_2 b_pre n_pre d_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_numeral_value_entail_wit_1_split_goal_1 : numeral_value_entail_wit_1_split_goal_1 := by
  intro b_pre n_pre digits PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  decide

theorem proof_of_numeral_value_entail_wit_1_split_goal_2 : numeral_value_entail_wit_1_split_goal_2 := by
  intro b_pre n_pre digits PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  rfl

theorem proof_of_numeral_value_entail_wit_1_split_goal_3 : numeral_value_entail_wit_1_split_goal_3 := by
  intro b_pre n_pre digits PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  exact PreH6

theorem proof_of_numeral_value_entail_wit_1 : numeral_value_entail_wit_1 := by
  unfold numeral_value_entail_wit_1
  right
  intro b_pre n_pre digits PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact proof_of_numeral_value_entail_wit_1_split_goal_3 b_pre n_pre digits PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    · exact proof_of_numeral_value_entail_wit_1_split_goal_1 b_pre n_pre digits PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    · exact proof_of_numeral_value_entail_wit_1_split_goal_2 b_pre n_pre digits PreH1 PreH2 PreH3 PreH4 PreH5 PreH6

theorem proof_of_numeral_value_entail_wit_2_split_goal_1 : numeral_value_entail_wit_2_split_goal_1 := by
  intro b_pre n_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact pow40_successor_bound__numeral_arithmetic i v b_pre (Znth i digits 0) PreH8 ⟨PreH11, PreH12⟩ ⟨PreH4, PreH5⟩ (PreH7 i ⟨PreH8, PreH1⟩)

theorem proof_of_numeral_value_entail_wit_2_split_goal_2 : numeral_value_entail_wit_2_split_goal_2 := by
  intro b_pre n_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  rw [numeral_sublist_succ__numeral_arithmetic b_pre i digits ⟨PreH8, by omega⟩, ← PreH10]

theorem proof_of_numeral_value_entail_wit_2 : numeral_value_entail_wit_2 := by
  unfold numeral_value_entail_wit_2
  right
  intro b_pre n_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact proof_of_numeral_value_entail_wit_2_split_goal_1 b_pre n_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    · exact proof_of_numeral_value_entail_wit_2_split_goal_2 b_pre n_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_numeral_value_return_wit_1_split_goal_1 : numeral_value_return_wit_1_split_goal_1 := by
  intro b_pre n_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hi : i = Zlength digits := by omega
  rw [hi, numeral_sublist_full__numeral_endpoints] at PreH10
  exact PreH10

theorem proof_of_numeral_value_return_wit_1 : numeral_value_return_wit_1 := by
  unfold numeral_value_return_wit_1
  right
  intro b_pre n_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_numeral_value_return_wit_1_split_goal_1 b_pre n_pre digits v i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro m_pre n_pre basey_pre bx_pre y_digits x_digits retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  unfold Spec
  left
  exact ⟨rfl, by omega⟩

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro m_pre n_pre basey_pre bx_pre y_digits x_digits retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_1_split_goal_1 m_pre n_pre basey_pre bx_pre y_digits x_digits retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  intro m_pre n_pre basey_pre bx_pre y_digits x_digits retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  unfold Spec
  right; left
  exact ⟨rfl, by omega⟩

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro m_pre n_pre basey_pre bx_pre y_digits x_digits retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_2_split_goal_1 m_pre n_pre basey_pre bx_pre y_digits x_digits retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1 := by
  intro m_pre n_pre basey_pre bx_pre y_digits x_digits retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  unfold Spec
  right; right
  exact ⟨rfl, by omega⟩

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  unfold solver_return_wit_3
  right
  intro m_pre n_pre basey_pre bx_pre y_digits x_digits retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_return_wit_3_split_goal_1 m_pre n_pre basey_pre bx_pre y_digits x_digits retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_partial_solve_wit_1_pure_split_goal_1 : solver_partial_solve_wit_1_pure_split_goal_1 := by
  intro m_pre y_pre n_pre x_pre basey_pre bx_pre y_digits x_digits PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  dump_pre_spatial
  exact PreH17

theorem proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure := by
  unfold solver_partial_solve_wit_1_pure
  right
  exact proof_of_solver_partial_solve_wit_1_pure_split_goal_1

theorem proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1 := by
  intro m_pre y_pre n_pre x_pre basey_pre bx_pre y_digits x_digits retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  dump_pre_spatial
  exact PreH21

theorem proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure := by
  unfold solver_partial_solve_wit_2_pure
  right
  exact proof_of_solver_partial_solve_wit_2_pure_split_goal_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_proof_manual
