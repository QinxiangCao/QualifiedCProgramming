import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_manual_scan

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_proof_manual
open AUXLib MaxMinLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1 := by
  unfold solver_entail_wit_12_1
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished_2 before_2 ks_2 ns_2 ws_2 ts_2 e c1 c0 top cs_2 u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst e
  have hfront := component_scan_done__scan_and_component_closure _ _ _ _ _ _ _ _ _ _ PreH37
  Exists (finished_2 ++ [u]) before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2 := by
  unfold solver_entail_wit_12_2
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished_2 before_2 ks_2 ns_2 ws_2 ts_2 e c1 c0 top cs_2 u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst e
  have hfront := component_scan_done__scan_and_component_closure _ _ _ _ _ _ _ _ _ _ PreH37
  Exists (finished_2 ++ [u]) before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solver_entail_wit_13 : solver_entail_wit_13 := by
  unfold solver_entail_wit_13
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 finished cs_2 before_2 ks_2 c1 c0 top total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  subst top
  rw [Zsublist_nil ks_2 0 0 (by omega)] at PreH29
  have hcomplete := component_frontier_complete__scan_and_component_closure _ _ _ _ _ _ _ _ _ _ _ _ PreH5 PreH30 PreH31 PreH23 PreH24 PreH29
  Exists finished before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  intro v hv
  have hn := PreH28.1.1.2.1
  simp only [List.append_nil] at hn
  by_cases he : v = s
  · subst v
    exact PreH27
  · have hb := PreH25 v ⟨hv.1,by omega⟩
    have hvb : 1 ≤ v ∧ v ≤ n_pre := ⟨hv.1,by omega⟩
    have hm : v ∉ vertices := fun hm => hb ((hn.2.2.1 v hvb).mp hm).1
    rwa [hn.2.2.2 v hvb hm]

theorem proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hh := PreH28.1.2.2.2 total PreH24
  simpa only [max_eq_left (by omega : c1 ≤ c0)] using hh

theorem proof_of_solver_entail_wit_14_1_split_goal_3 : solver_entail_wit_14_1_split_goal_3 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact PreH28.1.2.2.1

theorem proof_of_solver_entail_wit_14_1_split_goal_4 : solver_entail_wit_14_1_split_goal_4 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact PreH28.1.2.1

theorem proof_of_solver_entail_wit_14_1_split_goal_5 : solver_entail_wit_14_1_split_goal_5 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact PreH28.1.1.1

theorem proof_of_solver_entail_wit_14_1_split_goal_6 : solver_entail_wit_14_1_split_goal_6 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact MaxImpostersOn_upper_bound__outer_loop_component_commit _ _ _ _
    (proof_of_solver_entail_wit_14_1_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)

theorem proof_of_solver_entail_wit_14_1_split_goal_7 : solver_entail_wit_14_1_split_goal_7 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact PreH10

theorem proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1 := by
  unfold solver_entail_wit_14_1
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_14_1_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_1_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_1_split_goal_3 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_1_split_goal_4 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_1_split_goal_5 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_1_split_goal_6 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_1_split_goal_7 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

theorem proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  intro v hv
  have hn := PreH28.1.1.2.1
  simp only [List.append_nil] at hn
  by_cases he : v = s
  · subst v
    exact PreH27
  · have hb := PreH25 v ⟨hv.1,by omega⟩
    have hvb : 1 ≤ v ∧ v ≤ n_pre := ⟨hv.1,by omega⟩
    have hm : v ∉ vertices := fun hm => hb ((hn.2.2.1 v hvb).mp hm).1
    rwa [hn.2.2.2 v hvb hm]

theorem proof_of_solver_entail_wit_14_2_split_goal_2 : solver_entail_wit_14_2_split_goal_2 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hh := PreH28.1.2.2.2 total PreH24
  simpa only [max_eq_right (by omega : c0 ≤ c1)] using hh

theorem proof_of_solver_entail_wit_14_2_split_goal_3 : solver_entail_wit_14_2_split_goal_3 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact PreH28.1.2.2.1

theorem proof_of_solver_entail_wit_14_2_split_goal_4 : solver_entail_wit_14_2_split_goal_4 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact PreH28.1.2.1

theorem proof_of_solver_entail_wit_14_2_split_goal_5 : solver_entail_wit_14_2_split_goal_5 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact PreH28.1.1.1

theorem proof_of_solver_entail_wit_14_2_split_goal_6 : solver_entail_wit_14_2_split_goal_6 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact MaxImpostersOn_upper_bound__outer_loop_component_commit _ _ _ _
    (proof_of_solver_entail_wit_14_2_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)

theorem proof_of_solver_entail_wit_14_2_split_goal_7 : solver_entail_wit_14_2_split_goal_7 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact PreH10

theorem proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2 := by
  unfold solver_entail_wit_14_2
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_14_2_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_2_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_2_split_goal_3 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_2_split_goal_4 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_2_split_goal_5 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_2_split_goal_6 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
    | exact proof_of_solver_entail_wit_14_2_split_goal_7 m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 ns_2 ts_2 ws_2 before cs_2 ks_2 vertices s total top c0 c1 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_proof_manual
