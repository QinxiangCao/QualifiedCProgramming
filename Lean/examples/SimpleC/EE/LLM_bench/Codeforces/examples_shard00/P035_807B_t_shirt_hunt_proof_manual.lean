import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P035_807B_t_shirt_hunt_goal P035_807B_t_shirt_hunt_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem quot_div (a b : Int) (ha : 0≤a) (hb : 0<b) : Z.quot a b=Z.div a b := by
  exact (Int.fdiv_eq_tdiv_of_nonneg ha (by omega)).symm

private theorem seed (s : Int) (hs : 0≤s) : Z.rem (Z.quot s 50) 475=Z.modulo (Z.div s 50) 475 := by
  rw [quot_div s 50 hs (by omega)]
  exact AUXLib.rem_eq_mod _ _ (Int.fdiv_nonneg hs (by omega)) (by omega)

theorem proof_of_wins_safety_wit_13_split_goal_1 : wins_safety_wit_13_split_goal_1 := by
  unfold wins_safety_wit_13_split_goal_1
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dump_pre_spatial
  have hr := AUXLib.rem_nonneg_bounds (z*96+42) 475 (by omega) (by omega)
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_wins_safety_wit_13_split_goal_2 : wins_safety_wit_13_split_goal_2 := by
  unfold wins_safety_wit_13_split_goal_2
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dump_pre_spatial
  have hr := AUXLib.rem_nonneg_bounds (z*96+42) 475 (by omega) (by omega)
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_wins_safety_wit_13 : wins_safety_wit_13 := by
  unfold wins_safety_wit_13
  right
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  · exact proof_of_wins_safety_wit_13_split_goal_1 score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  · exact proof_of_wins_safety_wit_13_split_goal_2 score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_wins_entail_wit_1_split_goal_1 : wins_entail_wit_1_split_goal_1 := by
  unfold wins_entail_wit_1_split_goal_1
  intro score_pre place_pre PreH1 PreH2 PreH3 PreH4
  rw [seed score_pre PreH3]
  rcases shirt_trace_exists__wins_scan score_pre with ⟨v,hv⟩
  refine ⟨v,hv,⟨by omega,by omega⟩,hv.2.1.symm,?_⟩
  intro j hj; omega

theorem proof_of_wins_entail_wit_1_split_goal_2 : wins_entail_wit_1_split_goal_2 := by
  unfold wins_entail_wit_1_split_goal_2
  intro score_pre place_pre PreH1 PreH2 PreH3 PreH4
  have hq : 0≤Z.quot score_pre 50 := Int.tdiv_nonneg PreH3 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (Z.quot score_pre 50) 475 hq (by omega)
  exact hr.2

theorem proof_of_wins_entail_wit_1_split_goal_3 : wins_entail_wit_1_split_goal_3 := by
  unfold wins_entail_wit_1_split_goal_3
  intro score_pre place_pre PreH1 PreH2 PreH3 PreH4
  have hq : 0≤Z.quot score_pre 50 := Int.tdiv_nonneg PreH3 (by omega)
  have hr := AUXLib.rem_nonneg_bounds (Z.quot score_pre 50) 475 hq (by omega)
  exact hr.1

theorem proof_of_wins_entail_wit_1 : wins_entail_wit_1 := by
  unfold wins_entail_wit_1
  right
  intro score_pre place_pre PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_wins_entail_wit_1_split_goal_1 score_pre place_pre PreH1 PreH2 PreH3 PreH4)
      | exact (proof_of_wins_entail_wit_1_split_goal_2 score_pre place_pre PreH1 PreH2 PreH3 PreH4)
      | exact (proof_of_wins_entail_wit_1_split_goal_3 score_pre place_pre PreH1 PreH2 PreH3 PreH4)

theorem proof_of_wins_entail_wit_2_split_goal_1 : wins_entail_wit_2_split_goal_1 := by
  unfold wins_entail_wit_2_split_goal_1
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have he := AUXLib.rem_eq_mod (z*96+42) 475 (by omega) (by omega)
  rw [he] at PreH1 ⊢
  exact shirt_scan_state_step__wins_scan score_pre place_pre i z PreH2 PreH11 (by omega)

theorem proof_of_wins_entail_wit_2_split_goal_2 : wins_entail_wit_2_split_goal_2 := by
  unfold wins_entail_wit_2_split_goal_2
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hr := AUXLib.rem_nonneg_bounds (z*96+42) 475 (by omega) (by omega)
  exact hr.2

theorem proof_of_wins_entail_wit_2_split_goal_3 : wins_entail_wit_2_split_goal_3 := by
  unfold wins_entail_wit_2_split_goal_3
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hr := AUXLib.rem_nonneg_bounds (z*96+42) 475 (by omega) (by omega)
  exact hr.1

theorem proof_of_wins_entail_wit_2 : wins_entail_wit_2 := by
  unfold wins_entail_wit_2
  right
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_wins_entail_wit_2_split_goal_1 score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
      | exact (proof_of_wins_entail_wit_2_split_goal_2 score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
      | exact (proof_of_wins_entail_wit_2_split_goal_3 score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)

theorem proof_of_wins_return_wit_1_split_goal_1 : wins_return_wit_1_split_goal_1 := by
  unfold wins_return_wit_1_split_goal_1
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  rintro ⟨v₂,hl,hseed,hstep,j,hj,hp⟩
  rcases PreH10 with ⟨v₁,ht,hb,hz,hm⟩
  apply hm j ⟨hj.1,by omega⟩
  rw [shirt_trace_unique_prefix__wins_scan score_pre v₁ v₂ ht ⟨hl,hseed,hstep⟩ j ⟨by omega,hj.2⟩]
  exact hp

theorem proof_of_wins_return_wit_1 : wins_return_wit_1 := by
  unfold wins_return_wit_1
  right
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_wins_return_wit_1_split_goal_1 score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_wins_return_wit_2_split_goal_1 : wins_return_wit_2_split_goal_1 := by
  unfold wins_return_wit_2_split_goal_1
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  rw [AUXLib.rem_eq_mod (z*96+42) 475 (by omega) (by omega)]
  rcases PreH11 with ⟨v,ht,hb,hz,hm⟩
  refine ⟨v,ht.1,ht.2.1,ht.2.2,i+1,⟨by omega,by omega⟩,?_⟩
  rw [ht.2.2 i ⟨hb.1,PreH2⟩,← hz]
  omega

theorem proof_of_wins_return_wit_2 : wins_return_wit_2 := by
  unfold wins_return_wit_2
  right
  intro score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_wins_return_wit_2_split_goal_1 score_pre place_pre z i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  unfold solver_entail_wit_1_split_goal_1
  intro y_pre x_pre p_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  refine ⟨le_refl _,?_⟩
  intro c hc; omega

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro y_pre x_pre p_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_1_split_goal_1 y_pre x_pre p_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6)

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  unfold solver_entail_wit_2_split_goal_1
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact alignment_search_extend__alignment_search x_pre y_pre score PreH10 PreH1

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  unfold solver_entail_wit_2_split_goal_2
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hh := alignment_search_full_window__alignment_search x_pre y_pre score PreH5 ⟨PreH8,PreH9⟩ PreH10 PreH1
  omega

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_2_split_goal_1 y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | exact (proof_of_solver_entail_wit_2_split_goal_2 y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  unfold solver_entail_wit_3_split_goal_1
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact alignment_to_candidate_search__alignment_search p_pre x_pre y_pre score PreH1 PreH10

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_3_split_goal_1 y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  unfold solver_entail_wit_4_split_goal_1
  intro y_pre x_pre p_pre score retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact candidate_search_room__candidate_capacity p_pre x_pre y_pre score PreH9 PreH3 PreH12 PreH11

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro y_pre x_pre p_pre score retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_4_split_goal_1 y_pre x_pre p_pre score retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)

theorem proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1 := by
  unfold solver_entail_wit_5_split_goal_1
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact candidate_search_step__candidate_transitions p_pre x_pre y_pre score PreH10 PreH11

theorem proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2 := by
  unfold solver_entail_wit_5_split_goal_2
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  apply aligned_gap_at_least_fifty__candidate_transitions x_pre score (x_pre+50*475) PreH10.2.1 _ PreH8
  rw [show x_pre+50*475-x_pre=50*475 by omega]
  decide

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  unfold solver_entail_wit_5
  right
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_5_split_goal_1 y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)
      | exact (proof_of_solver_entail_wit_5_split_goal_2 y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11)

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  unfold solver_entail_wit_6_split_goal_1
  intro y_pre x_pre p_pre score retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact ⟨PreH12,PreH3⟩

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro y_pre x_pre p_pre score retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_6_split_goal_1 y_pre x_pre p_pre score retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  unfold solver_return_wit_1_split_goal_1
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact zero_success_is_spec__final_result p_pre x_pre y_pre score PreH1 PreH7 PreH9

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_return_wit_1_split_goal_1 y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  unfold solver_return_wit_2_split_goal_1
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rw [quot_div (score-x_pre+99) 100 (by omega) (by omega)]
  exact first_winning_is_spec__final_result p_pre x_pre y_pre score PreH1 PreH9

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_return_wit_2_split_goal_1 y_pre x_pre p_pre score PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_proof_manual
