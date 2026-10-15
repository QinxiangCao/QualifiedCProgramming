import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_manual_commit

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

theorem proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  apply max_imposters_on_total_implies_spec__final_specification n_pre comments cs_2 total PreH13 _ _ PreH20
  · intro v hv
    exact PreH21 v ⟨hv.1,by omega⟩
  · intro i hi
    rcases hq : comment_at comments i with ⟨⟨u,v⟩,w⟩
    dsimp
    have hb := comment_bounds_from_forward_star__scan_and_component_closure _ _ _ _ _ _ _ PreH6 PreH15 PreH16 i hi
    rw [hq] at hb
    have he : 0 ≤ 2*i ∧ 2*i < 2*m_pre := by omega
    have hw := (PreH16.2 (2*i) he).2.2
    have hobs := (PreH15.2.2.2.2.2.2.1 (2*i) he).2
    have hwt := (edge_forward__scan_and_component_closure comments i u v w hq).2.2
    rw [hobs,hwt] at hw
    exact ⟨hb.1,hb.2,hw⟩

theorem proof_of_solver_entail_wit_15 : solver_entail_wit_15 := by
  unfold solver_entail_wit_15
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_15_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22

theorem proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial := by
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs ns ts ws cs ks total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  sep_apply (intArray.full_to_full_shape comment_u_pre (m_pre) comment_sources)
  sep_apply (intArray.full_to_full_shape comment_v_pre (m_pre) comment_targets)
  sep_apply (intArray.full_to_full_shape comment_diff_pre (m_pre) comment_kinds)
  sep_apply (intArray.full_to_full_shape head_pre (n_pre+1) hs)
  sep_apply (intArray.full_to_full_shape nxt_pre (2*m_pre) ns)
  sep_apply (intArray.full_to_full_shape to_pre (2*m_pre) ts)
  sep_apply (intArray.full_to_full_shape wt_pre (2*m_pre) ws)
  sep_apply (intArray.full_to_full_shape color_pre (n_pre+1) cs)
  sep_apply (intArray.full_to_full_shape stack__pre (n_pre+1) ks)
  cancel

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs ns ts ws cs ks total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  exact proof_of_solver_return_wit_1_split_goal_spatial stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs ns ts ws cs ks total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8

theorem proof_of_solver_return_wit_2_split_goal_spatial : solver_return_wit_2_split_goal_spatial := by
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs ns ts ws cs ks s total top c0 c1 e u v want PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  sep_apply (intArray.full_to_full_shape comment_u_pre (m_pre) comment_sources)
  sep_apply (intArray.full_to_full_shape comment_v_pre (m_pre) comment_targets)
  sep_apply (intArray.full_to_full_shape comment_diff_pre (m_pre) comment_kinds)
  sep_apply (intArray.full_to_full_shape head_pre (n_pre+1) hs)
  sep_apply (intArray.full_to_full_shape nxt_pre (2*m_pre) ns)
  sep_apply (intArray.full_to_full_shape to_pre (2*m_pre) ts)
  sep_apply (intArray.full_to_full_shape wt_pre (2*m_pre) ws)
  sep_apply (intArray.full_to_full_shape color_pre (n_pre+1) cs)
  sep_apply (intArray.full_to_full_shape stack__pre (n_pre+1) ks)
  cancel

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs ns ts ws cs ks s total top c0 c1 e u v want PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  exact proof_of_solver_return_wit_2_split_goal_spatial stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs ns ts ws cs ks s total top c0 c1 e u v want PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_proof_manual
