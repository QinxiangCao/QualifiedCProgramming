import SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_goal
import SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open rmq_goal rmq_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray



theorem proof_of_build_safety_wit_12 : build_safety_wit_12 := by
  right
  intro st_pre K_pre n_pre arr_pre l st_l i len half j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hp := worker_Power2_nonneg j
  have hb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_build_safety_wit_28 : build_safety_wit_28 := by
  right
  intro st_pre K_pre n_pre arr_pre l st_l i len half j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hp := worker_Power2_nonneg j
  have hb := worker_Power2_bound_lt_30 j K_pre (by omega) (by omega)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_build_entail_wit_3 : build_entail_wit_3 := by
  right
  intro K_pre n_pre l st_l_2 idx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro q hq
    omega

theorem proof_of_build_entail_wit_4 : build_entail_wit_4 := by
  right
  intro K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    nlinarith

theorem proof_of_build_entail_wit_6 : build_entail_wit_6 := by
  right
  intro K_pre n_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact worker_STBasePrefix_complete_level1 l st_l_2 K_pre n_pre i PreH1 PreH8 PreH9 | rfl

theorem proof_of_build_entail_wit_7 : build_entail_wit_7 := by
  right
  intro K_pre n_pre l st_l_2 len half j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    intro q hq
    omega

theorem proof_of_build_entail_wit_8 : build_entail_wit_8 := by
  right
  intro K_pre n_pre l st_l_2 i len half j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals nlinarith

theorem proof_of_build_entail_wit_10 : build_entail_wit_10 := by
  right
  intro K_pre n_pre l st_l_2 i len half j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hb := STLevelPrefix_exit_to_built_step l st_l_2 K_pre n_pre j i len PreH13 PreH14 PreH10 PreH1
  have hd := Power2_step j (by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (simpa only [Int.add_sub_cancel] using PreH10) | omega

theorem proof_of_build_return_wit_1 : build_return_wit_1 := by
  right
  intro K_pre n_pre l st_l_2 len half j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have he : j = K_pre := by omega
  subst j
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact PreH11

theorem proof_of_query_entail_wit_1 : query_entail_wit_1 := by
  right
  intro right_pre left_pre K_pre n_pre st_l l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    rfl

theorem proof_of_query_entail_wit_2 : query_entail_wit_2 := by
  right
  intro right_pre left_pre K_pre n_pre st_l l pow k len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have he : pow*2 = Power2 (k+1) := by rw [PreH13]; exact Power2_step k PreH11
  have hk : k+1 < K_pre := by
    by_contra h
    have heq : k+1 = K_pre := by omega
    rw [heq] at he
    omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_query_entail_wit_3 : query_entail_wit_3 := by
  right
  intro right_pre left_pre K_pre n_pre st_l l pow k len PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals nlinarith

theorem proof_of_build_entail_wit_5 : build_entail_wit_5 := by
  left
  intro st_pre K_pre n_pre arr_pre l st_l_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  prop_apply (intArray.full_Zlength arr_pre n_pre l)
  Intros_p hl
  prop_apply (intArray.full_Zlength st_pre (n_pre*K_pre) (replace_Znth (i*K_pre) (Znth i l 0) st_l_2))
  Intros_p hs
  simp only [Zlength_replace_Znth] at hs
  have hb := worker_STBasePrefix_write_base_step l st_l_2 K_pre n_pre i hl hs
    (by omega) PreH6 PreH7 PreH8 PreH9 PreH10
  Exists (replace_Znth (i*K_pre) (Znth i l 0) st_l_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_build_entail_wit_9_1 : build_entail_wit_9_1 := by
  left
  intro st_pre K_pre n_pre arr_pre l st_l_2 j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  prop_apply (intArray.full_Zlength st_pre (n_pre*K_pre) (replace_Znth (i*K_pre+j) (Znth (i*K_pre+j-1) st_l_2 0) st_l_2))
  Intros_p hs
  simp only [Zlength_replace_Znth] at hs
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  have hleft := PreH19 i (j-1) (by constructor <;> first | omega | (repeat' constructor <;> omega))
  have hright := PreH19 (i+half) (j-1) (by constructor <;> first | omega | (repeat' constructor <;> omega))
  have hnext := STLevelPrefix_extend_by_left_max l st_l_2 K_pre n_pre j i half (Znth (i*K_pre+j-1) st_l_2 0) (Znth ((i+half)*K_pre+j-1) st_l_2 0)
    PreH7 PreH8 PreH9 ⟨PreH17,by omega⟩
    (by congr 1 <;> omega) (by congr 1 <;> omega) PreH1 PreH20 hleft hright
  have hbuilt : STBuiltBeforeLevel l (replace_Znth (i*K_pre+j) (Znth (i*K_pre+j-1) st_l_2 0) st_l_2) K_pre n_pre j := by
    apply STBuiltBeforeLevel_replace_level_cell l st_l_2 K_pre n_pre j i
    · exact PreH19
    · exact PreH8
    · exact ⟨PreH17,by omega⟩
    · intro row col hc
      have hp := Power2_pos col hc.2.1
      constructor <;> nlinarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  Exists (replace_Znth (i*K_pre+j) (Znth (i*K_pre+j-1) st_l_2 0) st_l_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_build_entail_wit_9_2 : build_entail_wit_9_2 := by
  left
  intro st_pre K_pre n_pre arr_pre l st_l_2 j half len i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  prop_apply (intArray.full_Zlength st_pre (n_pre*K_pre) (replace_Znth (i*K_pre+j) (Znth ((i+half)*K_pre+j-1) st_l_2 0) st_l_2))
  Intros_p hs
  simp only [Zlength_replace_Znth] at hs
  have hp := Power2_pos j (by omega)
  have hh := Power2_pos (j-1) (by omega)
  have hd := Power2_sub1_double j (by omega)
  have hleft := PreH19 i (j-1) (by constructor <;> first | omega | (repeat' constructor <;> omega))
  have hright := PreH19 (i+half) (j-1) (by constructor <;> first | omega | (repeat' constructor <;> omega))
  have hnext := STLevelPrefix_extend_by_right_max l st_l_2 K_pre n_pre j i half (Znth (i*K_pre+j-1) st_l_2 0) (Znth ((i+half)*K_pre+j-1) st_l_2 0)
    PreH7 PreH8 PreH9 ⟨PreH17,by omega⟩
    (by congr 1 <;> omega) (by congr 1 <;> omega) PreH1 PreH20 hleft hright
  have hbuilt : STBuiltBeforeLevel l (replace_Znth (i*K_pre+j) (Znth ((i+half)*K_pre+j-1) st_l_2 0) st_l_2) K_pre n_pre j := by
    apply STBuiltBeforeLevel_replace_level_cell l st_l_2 K_pre n_pre j i
    · exact PreH19
    · exact PreH8
    · exact ⟨PreH17,by omega⟩
    · intro row col hc
      have hp := Power2_pos col hc.2.1
      constructor <;> nlinarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  Exists (replace_Znth (i*K_pre+j) (Znth ((i+half)*K_pre+j-1) st_l_2 0) st_l_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_query_return_wit_1 : query_return_wit_1 := by
  right
  intro right_pre left_pre K_pre n_pre st_l l len k pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hfinal : QueryLogFinalState len k pow := by
    refine ⟨⟨PreH11,PreH13,by omega⟩,?_⟩
    rw [Power2_step_query k PreH11, ← PreH13]
    exact PreH16
  have hleft := PreH21 left_pre k ⟨PreH7,PreH11,PreH12,by omega⟩
  have hright := PreH21 (right_pre-pow+1) k ⟨by omega,PreH11,PreH12,by omega⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact RangeMaxValue_sparse_query_right l st_l K_pre n_pre len left_pre right_pre k pow
      (Znth (left_pre*K_pre+k) st_l 0) (Znth ((right_pre-pow+1)*K_pre+k) st_l 0)
      PreH10 rfl rfl hfinal hleft hright PreH1

theorem proof_of_query_return_wit_2 : query_return_wit_2 := by
  right
  intro right_pre left_pre K_pre n_pre st_l l len k pow PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hfinal : QueryLogFinalState len k pow := by
    refine ⟨⟨PreH11,PreH13,by omega⟩,?_⟩
    rw [Power2_step_query k PreH11, ← PreH13]
    exact PreH16
  have hleft := PreH21 left_pre k ⟨PreH7,PreH11,PreH12,by omega⟩
  have hright := PreH21 (right_pre-pow+1) k ⟨by omega,PreH11,PreH12,by omega⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact RangeMaxValue_sparse_query_left l st_l K_pre n_pre len left_pre right_pre k pow
      (Znth (left_pre*K_pre+k) st_l 0) (Znth ((right_pre-pow+1)*K_pre+k) st_l 0)
      PreH10 rfl rfl hfinal hleft hright PreH1

end SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_proof_manual
