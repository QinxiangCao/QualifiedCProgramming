import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_manual_forward_star

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

theorem proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro v hv
  omega

theorem proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have he : i = m_pre := by omega
  rwa [he] at PreH15

theorem proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have he : i = m_pre := by omega
  rwa [he] at PreH14

theorem proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH10

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  unfold solver_entail_wit_5
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_5_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_5_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_5_split_goal_3 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_5_split_goal_4 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro x hx
  by_cases he : v = x
  · subst x
    exact Znth_replace_Znth_Same 0 cs_2 v (-1) ⟨by omega,by omega⟩
  · rw [Znth_replace_Znth_Diff 0 cs_2 v x (-1) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ he]
    exact PreH17 x ⟨by omega,by omega⟩

theorem proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simpa only [Zlength_replace_Znth] using PreH15

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_6_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_6_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro v hv
  omega

theorem proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply max_imposters_on_empty__outer_loop_entry n_pre comments cs_2 (by omega) PreH15
  · intro v hv
    exact PreH17 v ⟨hv.1,by omega⟩
  · exact comment_bounds_from_forward_star__scan_and_component_closure _ _ _ _ _ _ _ PreH6 PreH13 PreH14

theorem proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro i hi
  rcases hq : comment_at comments i with ⟨⟨u,v⟩,w⟩
  dsimp
  have hb := comment_bounds_from_forward_star__scan_and_component_closure _ _ _ _ _ _ _ PreH6 PreH13 PreH14 i hi
  rw [hq] at hb
  have hu := PreH17 u ⟨hb.1.1,by omega⟩
  have hv := PreH17 v ⟨hb.2.1,by omega⟩
  rw [hu,hv]

theorem proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  intro i hi
  rcases hq : comment_at comments i with ⟨⟨u,v⟩,w⟩
  dsimp
  have hb := comment_bounds_from_forward_star__scan_and_component_closure _ _ _ _ _ _ _ PreH6 PreH13 PreH14 i hi
  rw [hq] at hb
  have hu := PreH17 u ⟨hb.1.1,by omega⟩
  have hv := PreH17 v ⟨hb.2.1,by omega⟩
  intro hc _
  exact False.elim (hc hu)

theorem proof_of_solver_entail_wit_7_split_goal_5 : solver_entail_wit_7_split_goal_5 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  refine ⟨PreH15,?_⟩
  intro v hv
  exact Or.inl (PreH17 v ⟨hv.1,by omega⟩)

theorem proof_of_solver_entail_wit_7_split_goal_6 : solver_entail_wit_7_split_goal_6 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH10

theorem proof_of_solver_entail_wit_7 : solver_entail_wit_7 := by
  unfold solver_entail_wit_7
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_7_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_7_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_7_split_goal_3 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_7_split_goal_4 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_7_split_goal_5 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_7_split_goal_6 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 v_2 __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_proof_manual
