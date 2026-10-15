import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_goal
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1 := by
  intro oj_pre oi_pre n_pre t_pre s_pre target source counts i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  have hc := PreH5 i (by omega)
  have hb := counted_prefix_counter_bound__count_invariants source target counts i (Znth i source 0-97) PreH9 (by omega) (by omega) (by omega) PreH11
  omega

theorem proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2 := by
  intro oj_pre oi_pre n_pre t_pre s_pre target source counts i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  have hc := PreH5 i (by omega)
  have hb := counted_prefix_counter_bound__count_invariants source target counts i (Znth i source 0-97) PreH9 (by omega) (by omega) (by omega) PreH11
  omega

theorem proof_of_solver_safety_wit_4 : solver_safety_wit_4 := by
  right
  intro oj_pre oi_pre n_pre t_pre s_pre target source counts i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_4_split_goal_1 oj_pre oi_pre n_pre t_pre s_pre target source counts i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_solver_safety_wit_4_split_goal_2 oj_pre oi_pre n_pre t_pre s_pre target source counts i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1 := by
  intro oj_pre oi_pre n_pre t_pre s_pre target source counts i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  have hs := PreH5 i (by omega)
  have ht := PreH6 i (by omega)
  have hb := counted_prefix_counter_bound__count_invariants source target counts i (Znth i target 0-97) PreH9 (by omega) (by omega) (by omega) PreH11
  have hbs := counted_prefix_counter_bound__count_invariants source target counts i (Znth i source 0-97) PreH9 (by omega) (by omega) (by omega) PreH11
  have hl := PreH11.1
  by_cases he : Znth i source 0-97=Znth i target 0-97
  · rw [he,Znth_replace_Znth_Same 0 counts _ _ (by omega)]
    omega
  · rw [Znth_replace_Znth_Diff 0 counts _ _ _ (by omega) (by omega) he]
    omega

theorem proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2 := by
  intro oj_pre oi_pre n_pre t_pre s_pre target source counts i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  simp only [INT_MAX,INT_MIN]
  have hs := PreH5 i (by omega)
  have ht := PreH6 i (by omega)
  have hb := counted_prefix_counter_bound__count_invariants source target counts i (Znth i target 0-97) PreH9 (by omega) (by omega) (by omega) PreH11
  have hbs := counted_prefix_counter_bound__count_invariants source target counts i (Znth i source 0-97) PreH9 (by omega) (by omega) (by omega) PreH11
  have hl := PreH11.1
  by_cases he : Znth i source 0-97=Znth i target 0-97
  · rw [he,Znth_replace_Znth_Same 0 counts _ _ (by omega)]
    omega
  · rw [Znth_replace_Znth_Diff 0 counts _ _ _ (by omega) (by omega) he]
    omega

theorem proof_of_solver_safety_wit_7 : solver_safety_wit_7 := by
  right
  intro oj_pre oi_pre n_pre t_pre s_pre target source counts i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_7_split_goal_1 oj_pre oi_pre n_pre t_pre s_pre target source counts i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_solver_safety_wit_7_split_goal_2 oj_pre oi_pre n_pre t_pre s_pre target source counts i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n_pre target source PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  constructor
  · rfl
  · intro c hc
    simp only [sublist,Int.toNat_zero,List.drop_zero,List.take_zero,List.nil_append,List.count_nil,Int.natCast_zero]
    exact Znth_repeat 0 26 c

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n_pre target source PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact PreH5

theorem proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3 := by
  intro n_pre target source PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  exact PreH4

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro n_pre target source PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n_pre target source PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
      | exact proof_of_solver_entail_wit_1_split_goal_2 n_pre target source PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
      | exact proof_of_solver_entail_wit_1_split_goal_3 n_pre target source PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  apply counted_prefix_step__count_invariants source target counts_2 i
  · omega
  · omega
  · exact PreH5 i (by omega)
  · exact PreH6 i (by omega)
  · exact PreH11

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  right
  intro n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_split_goal_1 n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  intro c hc;omega

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  intro n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have he : i=n_pre := by omega
  simpa only [he] using PreH11

theorem proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3 := by
  intro n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH6

theorem proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4 := by
  intro n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact PreH5

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  right
  intro n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_3_split_goal_1 n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_solver_entail_wit_3_split_goal_2 n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_solver_entail_wit_3_split_goal_3 n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      | exact proof_of_solver_entail_wit_3_split_goal_4 n_pre target source counts_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  intro n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact (combined_parity_from_full_counts__parity_scan source target n_pre counts_2 PreH7 PreH8 PreH11).2 c (by omega) PreH13

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  right
  intro n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_4_split_goal_1 n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1 := by
  intro n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  apply (combined_parity_from_full_counts__parity_scan source target n_pre counts_2 PreH7 PreH8 PreH11).1
  intro k hk
  exact PreH12 k (by omega)

theorem proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2 := by
  intro n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH6

theorem proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3 := by
  intro n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact PreH5

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  right
  intro n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_5_split_goal_1 n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_5_split_goal_2 n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
      | exact proof_of_solver_entail_wit_5_split_goal_3 n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  intro n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  apply counts_even_before_succ__parity_scan counts_2 c PreH9
  · rw [counted_prefix_full_count__parity_scan source target n_pre counts_2 c PreH7 PreH8 PreH11 (by omega)]
    omega
  · exact PreH12
  · exact PreH13

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  right
  intro n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_6_split_goal_1 n_pre target source counts_2 c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_entail_wit_7 : solver_entail_wit_7 := by
  right
  intro n_pre target source counts_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  Exists ([] : List (Int×Int))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | skip
    · exact repair_state_initial__repair_control source target PreH9
    · exact operation_lists_empty__repair_control
    · rfl

theorem proof_of_solver_entail_wit_8 : solver_entail_wit_8 := by
  right
  intro n_pre target source is_2 js_2 ops_2 m i tt_2 ss_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  Exists ops_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | skip
    exact no_value_range_empty__repair_control _ _ _

theorem proof_of_solver_entail_wit_9 : solver_entail_wit_9 := by
  right
  intro n_pre target source is_2 js_2 ops_2 m j i tt_2 ss_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  Exists ops_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | skip
    exact no_value_range_extend__repair_control _ _ _ _ PreH15 PreH1

theorem proof_of_solver_entail_wit_10 : solver_entail_wit_10 := by
  right
  intro n_pre target source is_2 js_2 ops_2 m j i tt_2 ss_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  Exists ops_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | skip
    · exact no_value_range_empty__repair_control _ _ _
    · have he : Zlength source=j := by omega
      simpa only [he] using PreH15

theorem proof_of_solver_entail_wit_11 : solver_entail_wit_11 := by
  right
  intro n_pre target source is_2 js_2 ops_2 m j i tt_2 ss_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  Exists ops_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | skip
    exact no_value_range_extend__repair_control _ _ _ _ PreH16 PreH1

theorem proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1 := by
  right
  intro n_pre target source is_2 js_2 ops_2 m j i tt_2 ss_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hs := PreH22.1
  have ht := PreH22.2.1
  have hsb1 := replace_znth_preserves_char_bounds__repair_transitions ss_2 j (Znth j tt_2 0) n_pre (by omega) (by omega) (PreH8 j (by omega)) PreH7
  have htb1 := replace_znth_preserves_char_bounds__repair_transitions tt_2 j (Znth j ss_2 0) n_pre (by omega) (by omega) (PreH7 j (by omega)) PreH8
  have hsb2 := replace_znth_preserves_char_bounds__repair_transitions (replace_Znth j (Znth j tt_2 0) ss_2) j (Znth i (replace_Znth j (Znth j ss_2 0) tt_2) 0) n_pre (by rw [Zlength_replace_Znth];omega) (by omega) (htb1 i (by omega)) hsb1
  have htb2 := replace_znth_preserves_char_bounds__repair_transitions (replace_Znth j (Znth j ss_2 0) tt_2) i (Znth j (replace_Znth j (Znth j tt_2 0) ss_2) 0) n_pre (by rw [Zlength_replace_Znth];omega) (by omega) (hsb1 j (by omega)) htb1
  Exists ((ops_2++[(j,j)])++[(j,i)])
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | skip
    · exact repair_state_two_cross_swaps__repair_transitions _ _ _ _ i ops_2 j PreH22 (by omega) (by omega) (by omega) PreH2
    · exact operation_lists_append__repair_transitions _ _ _ j i (operation_lists_append__repair_transitions _ _ _ j j PreH21)
    · simp only [Zlength_app,Zlength_cons,Zlength_nil];omega
    · simpa only [PreH9] using hsb2
    · simpa only [PreH9] using htb2

theorem proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2 := by
  right
  intro n_pre target source is_2 js_2 ops_2 m i tt_2 ss_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hs := PreH16.1
  Exists ops_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | skip
    exact repair_state_advance_equal__repair_transitions source target ss_2 tt_2 i ops_2 PreH16 (by omega) PreH1

theorem proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3 := by
  right
  intro n_pre target source is_2 js_2 ops_2 m j i tt_2 ss_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hs := PreH21.1
  have ht := PreH21.2.1
  have hsb := replace_znth_preserves_char_bounds__repair_transitions ss_2 j (Znth i tt_2 0) n_pre (by omega) (by omega) (PreH8 i (by omega)) PreH7
  have htb := replace_znth_preserves_char_bounds__repair_transitions tt_2 i (Znth j ss_2 0) n_pre (by omega) (by omega) (PreH7 j (by omega)) PreH8
  Exists (ops_2++[(j,i)])
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | skip
    · exact repair_state_one_cross_swap__repair_transitions _ _ _ _ i ops_2 j PreH21 (by omega) (by omega) (by omega) PreH2
    · exact operation_lists_append__repair_transitions _ _ _ j i PreH20
    · simp only [Zlength_app,Zlength_cons,Zlength_nil];omega
    · simpa only [PreH9] using hsb
    · simpa only [PreH9] using htb

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro oj_pre oi_pre n_pre t_pre s_pre target source is_2 js_2 ops_2 m i tt ss __default__Prod_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hw := repair_state_success_swaps_work__final_results source target ss tt i ops_2 PreH2 (by omega) (by omega) PreH15
  have hb := hw.1
  have hspec : Spec source target (some ops_2) := Or.inr ⟨ops_2,rfl,hw⟩
  rcases PreH14 with ⟨his,hjs,hops⟩
  have hd : ∀ q, (0≤q ∧ q<Zlength ops_2) → Znth q is_2 0=(Znth q ops_2 __default__Prod_Z_Z).1+1 ∧ Znth q js_2 0=(Znth q ops_2 __default__Prod_Z_Z).2+1 := by
    intro q hq
    rw [Znth_indep ops_2 q __default__Prod_Z_Z (0,0) hq]
    exact hops q hq
  Exists js_2 is_2 ops_2
  split_pure_spatial
  · sep_apply charArray.full_to_full_shape s_pre n_pre ss
    sep_apply charArray.full_to_full_shape t_pre n_pre tt
    rw [PreH13]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | skip

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  right
  intro oj_pre oi_pre n_pre t_pre s_pre target source is_2 js_2 ops_2 m j i tt ss PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  rcases PreH21 with ⟨hs,ht,hprefix,hperm,heven,htrace,hops⟩
  have hv := PreH6 i (by omega)
  exfalso
  exact no_match_contradicts_combined_even__final_results ss tt i (Znth i ss 0) (by omega) (by omega) hv hprefix rfl (Ne.symm PreH14) (by
    have he : Zlength ss=n_pre := by omega
    simpa only [he] using PreH15) (by
    have he : Zlength tt=j := by omega
    simpa only [he] using PreH16) heven

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  right
  intro oj_pre oi_pre n_pre t_pre s_pre target source counts c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hn : ¬∃ ops,SwapsWork source target ops := by
    rintro ⟨ops,hw⟩
    exact combined_odd_forbids_swaps_work__final_results source target c ops PreH9 hw
  have hspec : Spec source target none := Or.inl ⟨rfl,hn⟩
  Exists (List.replicate (2*n_pre).toNat (none : Option Int)) (List.replicate (2*n_pre).toNat (none : Option Int))
  split_pure_spatial
  · sep_apply charArray.full_to_full_shape s_pre n_pre source
    sep_apply charArray.full_to_full_shape t_pre n_pre target
    sep_apply intArray.undef_full_to_mixed_full oi_pre (2*n_pre)
    sep_apply intArray.undef_full_to_mixed_full oj_pre (2*n_pre)
    cancel
  · dump_pre_spatial
    exact hspec

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_proof_manual
