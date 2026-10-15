import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  left
  intro k_pre n_pre d_pre digits PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  Exists digits
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact greedy_progress_initial__initialization _ _ PreH3
      | exact GreedySelectionReady_universal _ _ _

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  left
  intro k_pre n_pre d_pre digits i cur_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  Exists cur_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact first_maximum_prefix_singleton__selection_scan _ _ ⟨by omega, by omega⟩

theorem proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1 := by
  unfold solver_entail_wit_3_1
  left
  intro k_pre n_pre d_pre digits best j i cur_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hm := first_maximum_prefix_extend_strict_app_zero__selection_scan cur_2 i j best PreH21 (by omega) PreH1
  Exists cur_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2 := by
  unfold solver_entail_wit_3_2
  left
  intro k_pre n_pre d_pre digits best j i cur_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hm := first_maximum_prefix_extend_nonstrict_app_zero__selection_scan cur_2 i j best PreH21 (by omega) PreH1
  Exists cur_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1 := by
  unfold solver_entail_wit_4_1
  left
  intro k_pre n_pre d_pre digits best j i cur_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hj : j = n_pre := by omega
  have hm : ReachableFirstMaximum cur_2 i k best := by
    unfold ReachableFirstMaximum
    rw [PreH8, min_eq_left (by omega : n_pre ≤ i + k + 1), ← hj]
    exact PreH19
  have hc := GreedySelectionReady_specialize _ _ _ _ PreH21 hm
  have hs := move_left_same__selection_exchange cur_2 best ⟨by omega, by omega⟩
  Exists cur_2 cur_2 k
  rw [hs]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2 := by
  unfold solver_entail_wit_4_2
  left
  intro k_pre n_pre d_pre digits best j i cur_2 k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hj : j = i + k + 1 := by omega
  have hm : ReachableFirstMaximum cur_2 i k best := by
    unfold ReachableFirstMaximum
    rw [PreH9, min_eq_right (by omega : i + k + 1 ≤ n_pre), ← hj]
    exact PreH20
  have hc := GreedySelectionReady_specialize _ _ _ _ PreH22 hm
  have hs := move_left_same__selection_exchange cur_2 best ⟨by omega, by omega⟩
  Exists cur_2 cur_2 k
  rw [hs]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  unfold solver_entail_wit_5
  left
  intro k_pre n_pre d_pre digits k best j i cur_2 before_2 start_k_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  subst cur_2
  have hstep := move_left_step_padded__bubble_transition before_2 best j ⟨by omega, by omega, by omega⟩
  have hlen := move_left_Zlength__bubble_transition before_2 best (j - 1) ⟨by omega, by omega, by omega⟩
  have hrange : ∀ p, (0 ≤ p ∧ p < n_pre) →
      48 ≤ Znth p (move_left before_2 best (j - 1)) 0 ∧ Znth p (move_left before_2 best (j - 1)) 0 ≤ 57 := by
    intro p hp
    exact move_left_preserves_range__bubble_transition _ _ _ ⟨by omega, by omega, by omega⟩
      (by intro q hq; exact PreH12 q ⟨hq.1, by omega⟩) p ⟨hp.1, by omega⟩
  Exists (move_left before_2 best (j - 1)) before_2 start_k_2
  rw [hstep]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | exact True.intro

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  left
  intro k_pre n_pre d_pre digits k best j i cur_2 before start_k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hj : j = i := by omega
  subst j
  subst cur_2
  have hreach_before := PreH24.2.2.2.1
  have hreach_after := swap_reach_move_left_after__bubble_transition digits before (k_pre - start_k)
    best i ⟨by omega, by omega, by omega⟩ hreach_before
  have hprogress : GreedyProgress digits k_pre (move_left before best i) (i + 1) k := by
    rw [PreH20]
    apply GreedyExchangeClosure_preserves_progress _ _ _ _ _ _ PreH23 PreH24 PreH26
    · exact move_left_Zlength__bubble_transition _ _ _ ⟨by omega, by omega, by omega⟩
    · convert hreach_after using 1 <;> omega
  Exists (move_left before best i)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | exact GreedySelectionReady_universal _ _ _

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  left
  intro k_pre n_pre d_pre digits i cur k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  Exists cur
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact greedy_progress_terminal_spec__final_result _ _ _ i k PreH14 (Or.inl (by omega))

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  left
  intro k_pre n_pre d_pre digits i cur k PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  Exists cur
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact greedy_progress_terminal_spec__final_result _ _ _ i k PreH15 (Or.inr (by omega))

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_proof_manual
