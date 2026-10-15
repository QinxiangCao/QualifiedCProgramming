import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_proof_auto

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P020_433A_kitahara_harukis_gift_goal P020_433A_kitahara_harukis_gift_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private abbrev zeros : List Int := List.replicate 205 0
private theorem zeros_length : Zlength zeros=205 := by rfl
private theorem zeros_nth (k : Int) : Znth k zeros 0=0 := Znth_repeat 0 205 k
private theorem quot_half (n : Int) (hn : 0≤n) : Z.quot n 2=n/2 := Int.tdiv_eq_ediv_of_nonneg hn
private theorem div_half (n : Int) : Z.div n 2=n/2 := Int.fdiv_eq_ediv_of_nonneg n (by omega)
private theorem rem_half (n : Int) (hn : 0≤n) : Z.rem n 2=n%2 := by
  rw [rem_eq_mod n 2 hn (by omega)]
  exact Int.fmod_eq_emod_of_nonneg n (by omega)

private theorem initial_reach (weights : List Int) (total : Int) (ht : total≤200) :
    ReachTable weights 0 total (replace_Znth 0 1 zeros) := by
  refine ⟨?_,?_,?_⟩
  · rw [Zlength_replace_Znth__inner_dp_transitions,zeros_length]
  · intro k hk
    by_cases hz : k=0
    · subst k
      rw [Znth_replace_Znth_Same 0 zeros 0 1 (by rw [zeros_length];omega)]
      exact Or.inr rfl
    · rw [Znth_replace_Znth_Diff 0 zeros 0 k 1 (by rw [zeros_length];omega) (by rw [zeros_length];omega) (Ne.symm hz),zeros_nth]
      exact Or.inl rfl
  · intro k hk
    rw [Zsublist_nil weights 0 0 (by omega)]
    by_cases hz : k=0
    · subst k
      rw [Znth_replace_Znth_Same 0 zeros 0 1 (by rw [zeros_length];omega)]
      exact ⟨fun _ => ⟨[],rfl,Forall.nil,rfl⟩,fun _ => by omega⟩
    · rw [Znth_replace_Znth_Diff 0 zeros 0 k 1 (by rw [zeros_length];omega) (by rw [zeros_length];omega) (Ne.symm hz),zeros_nth]
      constructor
      · intro h;exact False.elim (h rfl)
      · rintro ⟨chosen,hlen,hbits,hsum⟩
        simp only [List.zip_nil_right,List.map_nil,List.foldr_nil] at hsum
        exact False.elim (hz hsum)

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n_pre weights PreH1 PreH2 PreH3 PreH4
  unfold PrefixUnitTotal
  rw [show sublist 0 0 weights=[] from Zsublist_nil weights 0 0 (by omega)]
  exact ⟨⟨by omega,by omega⟩,rfl⟩

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n_pre weights PreH1 PreH2 PreH3 PreH4
  exact PreH3

theorem proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1 := by
  intro n_pre w_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hw := weight_values_of_explicit_require weights n_pre PreH3 PreH2
  have hh := hw i (by omega)
  dump_pre_spatial
  rw [unit_weight_quot__inner_dp_transitions _ hh]
  have hu := pre_unit_weight_bounds__reach_initialization weights i hw (by omega)
  change total+UnitWeight (Znth i weights 0)≤2147483647
  omega

theorem proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2 := by
  intro n_pre w_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hw := weight_values_of_explicit_require weights n_pre PreH3 PreH2
  have hh := hw i (by omega)
  dump_pre_spatial
  rw [unit_weight_quot__inner_dp_transitions _ hh]
  have hu := pre_unit_weight_bounds__reach_initialization weights i hw (by omega)
  change -2147483648≤total+UnitWeight (Znth i weights 0)
  omega

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hw := weight_values_of_explicit_require weights n_pre PreH3 PreH2
  have hh := hw i (by omega)
  rw [unit_weight_quot__inner_dp_transitions _ hh]
  exact prefix_unit_total_step__prefix_scan weights i total (by omega) PreH10

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hw := weight_values_of_explicit_require weights n_pre PreH3 PreH2
  have hh := hw i (by omega)
  rw [unit_weight_quot__inner_dp_transitions _ hh]
  have hu := pre_unit_weight_bounds__reach_initialization weights i hw (by omega)
  omega

theorem proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3 := by
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hw := weight_values_of_explicit_require weights n_pre PreH3 PreH2
  have hh := hw i (by omega)
  rw [unit_weight_quot__inner_dp_transitions _ hh]
  have hu := pre_unit_weight_bounds__reach_initialization weights i hw (by omega)
  omega

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact Or.inr ⟨rfl,rfl⟩

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  refine Or.inr ⟨rfl,?_⟩
  rintro ⟨chosen,hlen,hbits,hgrams⟩
  have hi : i=n_pre := by omega
  subst i
  have htotal := PreH10.2
  rw [sublist_self weights n_pre PreH3] at htotal
  have hw := weight_values_of_explicit_require weights n_pre PreH3 PreH2
  have hu := (fair_split_unit_balance__final_result weights chosen hw hlen hbits).mp hgrams
  rw [rem_half total PreH8] at PreH11
  omega

theorem proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3 := by
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hi : i=n_pre := by omega
  simpa only [hi] using PreH10

theorem proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4 := by
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH2

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  have hi : i=n_pre := by omega
  simpa only [hi] using PreH10

theorem proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2 := by
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  exact PreH2

theorem proof_of_solver_entail_wit_4_split_goal_spatial : solver_entail_wit_4_split_goal_spatial := by
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simp only [Int.zero_mul,Int.add_zero,show sizeof(CHAR)=(1:Int) from rfl,Int.one_mul]
  cancel

theorem proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1 := by
  intro n_pre weights total retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  exact PreH2

theorem proof_of_solver_entail_wit_5_split_goal_spatial : solver_entail_wit_5_split_goal_spatial := by
  intro n_pre weights total retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simp only [Int.zero_mul,Int.add_zero,show sizeof(CHAR)=(1:Int) from rfl,Int.one_mul]
  cancel

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  intro n_pre weights total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact initial_reach weights total PreH7

theorem proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2 := by
  intro n_pre weights total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact PreH2

theorem proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1 := by
  intro n_pre weights reach_l_2 total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  assumption

theorem proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact reach_table_to_inner_at_total__reach_initialization weights i total reach_l_2 PreH13

theorem proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hw := weight_values_of_explicit_require weights n_pre PreH4 PreH3
  rw [unit_weight_quot__inner_dp_transitions _ (hw i (by omega))]
  have hu := pre_unit_weight_bounds__reach_initialization weights i hw (by omega)
  have htotal := PreH10.2
  rw [sublist_self weights n_pre PreH4] at htotal
  have hs := pre_unit_sum_lower_bound__reach_initialization weights hw
  omega

theorem proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hw := weight_values_of_explicit_require weights n_pre PreH4 PreH3
  rw [unit_weight_quot__inner_dp_transitions _ (hw i (by omega))]
  have hu := pre_unit_weight_bounds__reach_initialization weights i hw (by omega)
  omega

theorem proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hw := weight_values_of_explicit_require weights n_pre PreH4 PreH3
  rw [unit_weight_quot__inner_dp_transitions _ (hw i (by omega))]
  have hu := pre_unit_weight_bounds__reach_initialization weights i hw (by omega)
  omega

theorem proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact PreH3

theorem proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1 := by
  intro n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hw := weight_values_of_explicit_require weights n_pre PreH3 PreH2
  exact reach_inner_finish__inner_dp_transitions weights i s u total reach_l_2 hw (by omega)
    PreH12 PreH13 PreH1 PreH15 PreH17

theorem proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2 := by
  intro n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH2

theorem proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1 := by
  intro n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hw := weight_values_of_explicit_require weights n_pre PreH4 PreH3
  exact reach_inner_mark_step__inner_dp_transitions weights i s u total reach_l_2 hw (by omega)
    PreH13 PreH14 PreH2 PreH17 PreH8 PreH18 PreH19

theorem proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1 := by
  intro n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hw := weight_values_of_explicit_require weights n_pre PreH3 PreH2
  exact reach_inner_skip_step__inner_dp_transitions weights i s u total reach_l_2 hw (by omega)
    PreH12 PreH13 PreH1 PreH17 PreH18

theorem proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1 := by
  intro n_pre weights reach_l_2 total i u PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  assumption

theorem proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  rw [quot_half total PreH6]
  exact solver_return_bridge_of_bit__final_result _ (PreH12.2.1 (total/2) (by omega))

theorem proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  rw [quot_half total PreH6]
  have hi : i=n_pre := by omega
  subst i
  have htotal := PreH9.2
  rw [sublist_self weights n_pre PreH3] at htotal
  have hr := PreH12.2.2 (total/2) (by omega)
  rw [sublist_self weights n_pre PreH3] at hr
  have hw := weight_values_of_explicit_require weights n_pre PreH3 PreH2
  have hf := fair_split_iff_half_selectable__final_result weights total hw htotal
    ((rem_eq_mod total 2 PreH6 (by omega)).symm.trans PreH8)
  rw [div_half] at hf
  rcases PreH12.2.1 (total/2) (by omega) with hz|ho
  · exact Or.inr ⟨hz,fun hfair => ((hr.mpr (hf.mp hfair))) hz⟩
  · exact Or.inl ⟨ho,hf.mpr (hr.mp (by omega))⟩

theorem proof_of_solver_entail_wit_12_split_goal_3 : solver_entail_wit_12_split_goal_3 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hi : i=n_pre := by omega
  simpa only [hi] using PreH12

theorem proof_of_solver_entail_wit_12_split_goal_4 : solver_entail_wit_12_split_goal_4 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  rw [quot_half total PreH6]
  omega

theorem proof_of_solver_entail_wit_12_split_goal_5 : solver_entail_wit_12_split_goal_5 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  rw [quot_half total PreH6]
  omega

theorem proof_of_solver_entail_wit_12_split_goal_6 : solver_entail_wit_12_split_goal_6 := by
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH2

theorem proof_of_solver_safety_wit_4 : solver_safety_wit_4 := by
  unfold solver_safety_wit_4
  right
  intro n_pre w_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  · exact proof_of_solver_safety_wit_4_split_goal_1 n_pre w_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  · exact proof_of_solver_safety_wit_4_split_goal_2 n_pre w_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n_pre weights PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n_pre weights PreH1 PreH2 PreH3 PreH4
      | exact proof_of_solver_entail_wit_1_split_goal_2 n_pre weights PreH1 PreH2 PreH3 PreH4

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_solver_entail_wit_2_split_goal_2 n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      | exact proof_of_solver_entail_wit_2_split_goal_3 n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_3_split_goal_1 n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_solver_entail_wit_3_split_goal_2 n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_solver_entail_wit_3_split_goal_3 n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_solver_entail_wit_3_split_goal_4 n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · exact proof_of_solver_entail_wit_4_split_goal_spatial n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  · split_pures
    · exact proof_of_solver_entail_wit_4_split_goal_1 n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    · exact proof_of_solver_entail_wit_4_split_goal_2 n_pre weights total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  unfold solver_entail_wit_5
  right
  intro n_pre weights total retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · exact proof_of_solver_entail_wit_5_split_goal_spatial n_pre weights total retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  · exact proof_of_solver_entail_wit_5_split_goal_1 n_pre weights total retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro n_pre weights total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_6_split_goal_1 n_pre weights total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
      | exact proof_of_solver_entail_wit_6_split_goal_2 n_pre weights total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_7 : solver_entail_wit_7 := by
  unfold solver_entail_wit_7
  right
  intro n_pre weights reach_l_2 total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_7_split_goal_1 n_pre weights reach_l_2 total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_8 : solver_entail_wit_8 := by
  unfold solver_entail_wit_8
  right
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_8_split_goal_1 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_solver_entail_wit_8_split_goal_2 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_solver_entail_wit_8_split_goal_3 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_solver_entail_wit_8_split_goal_4 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_solver_entail_wit_8_split_goal_5 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_entail_wit_9 : solver_entail_wit_9 := by
  unfold solver_entail_wit_9
  right
  intro n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_9_split_goal_1 n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
      | exact proof_of_solver_entail_wit_9_split_goal_2 n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1 := by
  unfold solver_entail_wit_10_1
  right
  intro n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_10_1_split_goal_1 n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2 := by
  unfold solver_entail_wit_10_2
  right
  intro n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_10_2_split_goal_1 n_pre weights reach_l_2 s u i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_solver_entail_wit_11 : solver_entail_wit_11 := by
  unfold solver_entail_wit_11
  right
  intro n_pre weights reach_l_2 total i u PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact proof_of_solver_entail_wit_11_split_goal_1 n_pre weights reach_l_2 total i u PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_12 : solver_entail_wit_12 := by
  unfold solver_entail_wit_12
  right
  intro n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_12_split_goal_1 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_12_split_goal_2 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_12_split_goal_3 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_12_split_goal_4 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_12_split_goal_5 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_12_split_goal_6 n_pre weights reach_l_2 i total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro n_pre weights reach_l total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  Exists (Znth (Z.quot total 2) reach_l 0)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro n_pre weights total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  Exists (0 : Int)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_proof_manual
