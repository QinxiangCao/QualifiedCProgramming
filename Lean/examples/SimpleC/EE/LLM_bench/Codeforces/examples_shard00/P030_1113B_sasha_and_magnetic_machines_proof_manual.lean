import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P030_1113B_sasha_and_magnetic_machines_goal P030_1113B_sasha_and_magnetic_machines_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem quot_div (a b : Int) (ha : 0≤a) (hb : 0<b) : Z.quot a b=Z.div a b := by
  exact (Int.fdiv_eq_tdiv_of_nonneg ha (by omega)).symm

private theorem quot_bounds (a b : Int) (ha : 0≤a) (hb : 0<b) : 0≤Z.quot a b ∧ Z.quot a b≤a := by
  rw [quot_div a b ha hb]
  exact ⟨Int.fdiv_nonneg ha (by omega),Int.fdiv_le_self b ha⟩

theorem proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1 := by
  unfold solver_safety_wit_10_split_goal_1
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have hv := PreH4 i ⟨by omega,by omega⟩
  have hd := quot_bounds (Znth i values 0) x (by omega) (by omega)
  have hm := Int.mul_le_mul_of_nonneg_left (show x≤100 by omega) (show 0≤mn by omega)
  have hn := Int.mul_nonneg (show 0≤mn by omega) (show 0≤x by omega)
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2 := by
  unfold solver_safety_wit_10_split_goal_2
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have hv := PreH4 i ⟨by omega,by omega⟩
  have hd := quot_bounds (Znth i values 0) x (by omega) (by omega)
  have hm := Int.mul_le_mul_of_nonneg_left (show x≤100 by omega) (show 0≤mn by omega)
  have hn := Int.mul_nonneg (show 0≤mn by omega) (show 0≤x by omega)
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_10 : solver_safety_wit_10 := by
  unfold solver_safety_wit_10
  right
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pures
  · exact proof_of_solver_safety_wit_10_split_goal_1 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  · exact proof_of_solver_safety_wit_10_split_goal_2 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1 := by
  unfold solver_safety_wit_11_split_goal_1
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have hv := PreH4 i ⟨by omega,by omega⟩
  have hm := Int.mul_le_mul_of_nonneg_left (show x≤100 by omega) (show 0≤mn by omega)
  have hn := Int.mul_nonneg (show 0≤mn by omega) (show 0≤x by omega)
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2 := by
  unfold solver_safety_wit_11_split_goal_2
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have hv := PreH4 i ⟨by omega,by omega⟩
  have hm := Int.mul_le_mul_of_nonneg_left (show x≤100 by omega) (show 0≤mn by omega)
  have hn := Int.mul_nonneg (show 0≤mn by omega) (show 0≤x by omega)
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_11 : solver_safety_wit_11 := by
  unfold solver_safety_wit_11
  right
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pures
  · exact proof_of_solver_safety_wit_11_split_goal_1 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  · exact proof_of_solver_safety_wit_11_split_goal_2 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1 := by
  unfold solver_safety_wit_12_split_goal_1
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have hv := PreH4 i ⟨by omega,by omega⟩
  have hd := quot_bounds (Znth i values 0) x (by omega) (by omega)
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2 := by
  unfold solver_safety_wit_12_split_goal_2
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have hv := PreH4 i ⟨by omega,by omega⟩
  have hd := quot_bounds (Znth i values 0) x (by omega) (by omega)
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_12 : solver_safety_wit_12 := by
  unfold solver_safety_wit_12
  right
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pures
  · exact proof_of_solver_safety_wit_12_split_goal_1 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  · exact proof_of_solver_safety_wit_12_split_goal_2 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_solver_safety_wit_16_split_goal_1 : solver_safety_wit_16_split_goal_1 := by
  unfold solver_safety_wit_16_split_goal_1
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  have hv := PreH5 i ⟨by omega,by omega⟩
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_16_split_goal_2 : solver_safety_wit_16_split_goal_2 := by
  unfold solver_safety_wit_16_split_goal_2
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  have hv := PreH5 i ⟨by omega,by omega⟩
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_16 : solver_safety_wit_16 := by
  unfold solver_safety_wit_16
  right
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pures
  · exact proof_of_solver_safety_wit_16_split_goal_1 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  · exact proof_of_solver_safety_wit_16_split_goal_2 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1 := by
  unfold solver_safety_wit_17_split_goal_1
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  have hv := PreH5 i ⟨by omega,by omega⟩
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2 := by
  unfold solver_safety_wit_17_split_goal_2
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  have hv := PreH5 i ⟨by omega,by omega⟩
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_17 : solver_safety_wit_17 := by
  unfold solver_safety_wit_17
  right
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pures
  · exact proof_of_solver_safety_wit_17_split_goal_1 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  · exact proof_of_solver_safety_wit_17_split_goal_2 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_solver_safety_wit_18_split_goal_1 : solver_safety_wit_18_split_goal_1 := by
  unfold solver_safety_wit_18_split_goal_1
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have hv := PreH4 i ⟨by omega,by omega⟩
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_18_split_goal_2 : solver_safety_wit_18_split_goal_2 := by
  unfold solver_safety_wit_18_split_goal_2
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have hv := PreH4 i ⟨by omega,by omega⟩
  norm_num only [INT_MIN,INT_MAX]
  omega

theorem proof_of_solver_safety_wit_18 : solver_safety_wit_18 := by
  unfold solver_safety_wit_18
  right
  intro n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pures
  · exact proof_of_solver_safety_wit_18_split_goal_1 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  · exact proof_of_solver_safety_wit_18_split_goal_2 n_pre a_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  unfold solver_entail_wit_1_split_goal_1
  intro n_pre values PreH1 PreH2 PreH3 PreH4
  refine ⟨⟨by omega,by omega⟩,?_,Or.inl ⟨rfl,rfl⟩⟩
  rfl

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  unfold solver_entail_wit_1_split_goal_2
  intro n_pre values PreH1 PreH2 PreH3 PreH4
  exact PreH3

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n_pre values PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_1_split_goal_1 n_pre values PreH1 PreH2 PreH3 PreH4)
      | exact (proof_of_solver_entail_wit_1_split_goal_2 n_pre values PreH1 PreH2 PreH3 PreH4)

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  unfold solver_entail_wit_2_1_split_goal_1
  intro n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact prefix_summary_step_lt__prefix_summary values i sum mn ⟨by omega,by omega⟩ PreH13 PreH1

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  unfold solver_entail_wit_2_1
  right
  intro n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_2_1_split_goal_1 n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  unfold solver_entail_wit_2_2_split_goal_1
  intro n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hp : 0<i := by
    rcases PreH13.2.2 with ⟨he,hm⟩ | ⟨hi,_⟩
    · have hv := PreH5 i ⟨by omega,by omega⟩
      omega
    · exact hi
  exact prefix_summary_step_ge__prefix_summary values i sum mn ⟨hp,by omega⟩ PreH13 PreH1

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  unfold solver_entail_wit_2_2
  right
  intro n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_2_2_split_goal_1 n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  unfold solver_entail_wit_3_split_goal_1
  intro n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  refine ⟨sum,⟨Or.inl rfl,?_⟩,rfl⟩
  intro cost hc
  rcases hc with he | ⟨s,f,hs,hf,hd,hseen,hcost⟩
  · dsimp only; omega
  · rcases hseen with h | ⟨he,h⟩ <;> omega

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  unfold solver_entail_wit_3_split_goal_2
  intro n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  rcases PreH12.2.2 with ⟨he,_⟩ | ⟨_,j,hj,hv,hm⟩
  · omega
  · have hh := PreH4 j ⟨hj.1,by omega⟩
    omega

theorem proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3 := by
  unfold solver_entail_wit_3_split_goal_3
  intro n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : i=n_pre := by omega
  rw [← he]
  exact PreH12

theorem proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4 := by
  unfold solver_entail_wit_3_split_goal_4
  intro n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH4

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_3_split_goal_1 n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_solver_entail_wit_3_split_goal_2 n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_solver_entail_wit_3_split_goal_3 n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | exact (proof_of_solver_entail_wit_3_split_goal_4 n_pre values mn sum i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  unfold solver_entail_wit_4_split_goal_1
  intro n_pre values answer i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  exact PreH4

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro n_pre values answer i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_4_split_goal_1 n_pre values answer i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)

theorem proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1 := by
  unfold solver_entail_wit_5_1_split_goal_1
  intro n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hv := PreH5 i ⟨by omega,by omega⟩
  have he := quot_div (Znth i values 0) x (by omega) (by omega)
  rw [he] at PreH1
  rw [he]
  exact search_minimum_extend_factor_lower__search_transitions values sum mn i x answer ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH19 PreH1 PreH18

theorem proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2 := by
  unfold solver_entail_wit_5_1_split_goal_2
  intro n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hv := PreH5 i ⟨by omega,by omega⟩
  rw [quot_div (Znth i values 0) x (by omega) (by omega)]
  apply enumerated_candidate_nonnegative__search_transitions values sum mn i x PreH3 ⟨by omega,by omega⟩ PreH14
  · intro k hk; exact (PreH5 k hk).1
  · rw [← PreH6]; exact PreH7

theorem proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1 := by
  unfold solver_entail_wit_5_1
  right
  intro n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_5_1_split_goal_1 n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | exact (proof_of_solver_entail_wit_5_1_split_goal_2 n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)

theorem proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1 := by
  unfold solver_entail_wit_5_2_split_goal_1
  intro n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hv := PreH5 i ⟨by omega,by omega⟩
  have he := quot_div (Znth i values 0) x (by omega) (by omega)
  rw [he] at PreH1
  exact search_minimum_extend_factor_upper__search_transitions values sum mn i x answer ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH19 PreH1 PreH18

theorem proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2 := by
  unfold solver_entail_wit_5_2
  right
  intro n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_5_2_split_goal_1 n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)

theorem proof_of_solver_entail_wit_5_3_split_goal_1 : solver_entail_wit_5_3_split_goal_1 := by
  unfold solver_entail_wit_5_3_split_goal_1
  intro n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  exact search_minimum_skip_nondivisor__search_transitions values sum mn i x answer ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH18 PreH17

theorem proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3 := by
  unfold solver_entail_wit_5_3
  right
  intro n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_5_3_split_goal_1 n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  unfold solver_entail_wit_6_split_goal_1
  intro n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact search_minimum_advance_source__search_transitions values sum mn i x answer ⟨by omega,by omega⟩ PreH13 ⟨by omega,by omega⟩ PreH17

theorem proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2 := by
  unfold solver_entail_wit_6_split_goal_2
  intro n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH4

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_entail_wit_6_split_goal_1 n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)
      | exact (proof_of_solver_entail_wit_6_split_goal_2 n_pre values answer x i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17)

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  unfold solver_return_wit_1_split_goal_1
  intro n_pre values answer i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  subst n_pre
  have hi : i=Zlength values := by omega
  rw [hi] at PreH15
  rcases PreH6 with ⟨_,hs,⟨he,_⟩ | ⟨_,j,hj,hv,hm⟩⟩
  · omega
  · rw [sublist_full__search_transitions] at hs
    have hp : ∀k,(0≤k ∧ k<Zlength values)→1≤Znth k values 0 := fun k hk => (PreH4 k hk).1
    rcases PreH15 with ⟨chosen,⟨hc,hmin⟩,he⟩
    change chosen=answer at he
    subst chosen
    rcases enumerated_cost_realizable_or_no_better__final_spec values sum mn answer j hs hj hv hc with ⟨best,hbest,hupper⟩
    have hbound : ∀ other,OneMagneticTransfer values other → answer≤TotalPower other := by
      intro other ho
      rcases magnetic_transfer_dominated_by_enumeration__final_spec values sum mn j other hs hj hv hp hm ho with ⟨c,hc,hupper⟩
      have hh := hmin c hc
      change answer≤c at hh
      omega
    refine ⟨best,⟨hbest,?_⟩,?_⟩
    · intro other ho
      have hh := hbound other ho
      omega
    · have hh := hbound best hbest
      omega

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro n_pre values answer i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact (proof_of_solver_return_wit_1_split_goal_1 n_pre values answer i sum mn PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_proof_manual
