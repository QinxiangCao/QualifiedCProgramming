import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_manual_colours

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

theorem proof_of_solver_entail_wit_8 : solver_entail_wit_8 := by
  unfold solver_entail_wit_8
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hlen := PreH18.1
  have hbefore : Znth s cs_2 0 = -1 := by have hh := PreH18.2 s ⟨PreH12,PreH2⟩; omega
  have hks : Zlength (replace_Znth 0 s ks_2) = n_pre+1 := by simpa only [Zlength_replace_Znth] using PreH23
  have hafter : Znth s (replace_Znth s 0 cs_2) 0 ≠ -1 := by
    rw [Znth_replace_Znth_Same 0 cs_2 s 0 ⟨by omega,by omega⟩]
    omega
  have hstack : ∀ j, (0 ≤ j ∧ j < 1) → 1 ≤ Znth j (replace_Znth 0 s ks_2) 0 ∧ Znth j (replace_Znth 0 s ks_2) 0 ≤ n_pre := by
    intro j hj
    have he : j = 0 := by omega
    subst j
    rw [Znth_replace_Znth_Same 0 ks_2 0 s ⟨by omega,by omega⟩]
    exact ⟨PreH12,PreH2⟩
  have hfront := singleton_component_frontier_strong__outer_loop_entry n_pre comments cs_2 ks_2 s PreH3 ⟨PreH12,PreH2⟩ hlen PreH23 PreH18 PreH1
  Exists ([] : List Int) cs_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1 := by
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs ns_2 ts_2 ws_2 finished_2 cs_2 before_2 ks c1 c0 top total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hu := PreH20 (top-1) ⟨by omega,by omega⟩
  have hbit := PreH1
  obtain ⟨hscan,hsum⟩ := component_frontier_pop_to_scan__frontier_pop_to_scan n_pre comments before_2 cs_2 finished_2 ks c0 c1 0 top hs ns_2 ts_2 ws_2 m_pre
    (by omega) PreH22 ⟨PreH15,PreH16⟩ PreH33 (by decide) hbit PreH30 PreH6 PreH31
  simp only [ite_true,show ¬ ((1:Int)=0) by decide,show ¬ ((0:Int)=1) by decide,↓reduceIte] at hscan
  have hhead := PreH32.1 _ hu
  have hedge : Znth (Znth (top-1) ks 0) hs 0 ≠ -1 →
      (((1 ≤ Znth (Znth (Znth (top-1) ks 0) hs 0) ts_2 0 ∧ Znth (Znth (Znth (top-1) ks 0) hs 0) ts_2 0 ≤ n_pre) ∧
       (Znth (Znth (Znth (top-1) ks 0) hs 0) ws_2 0 = 0 ∨ Znth (Znth (Znth (top-1) ks 0) hs 0) ws_2 0 = 1)) ∧
       -1 ≤ Znth (Znth (Znth (top-1) ks 0) hs 0) ns_2 0) ∧ Znth (Znth (Znth (top-1) ks 0) hs 0) ns_2 0 < 2*m_pre := by
    intro he
    obtain ⟨hn,ht,hw⟩ := PreH32.2 (Znth (Znth (top-1) ks 0) hs 0) ⟨by omega,by omega⟩
    exact ⟨⟨⟨ht,hw⟩,hn.1⟩,hn.2⟩
  have hpending : ∀ j, (0 ≤ j ∧ j < top-1) → 1 ≤ Znth j ks 0 ∧ Znth j ks 0 ≤ n_pre := by
    intro j hj
    exact PreH20 j ⟨hj.1,by omega⟩
  Left
  Exists hs finished_2 before_2 ks ns_2 ws_2 ts_2 cs_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2 := by
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs ns_2 ts_2 ws_2 finished_2 cs_2 before_2 ks c1 c0 top total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hu := PreH20 (top-1) ⟨by omega,by omega⟩
  have hp := sublist_pop_permutation__frontier_pop_to_scan ks top ⟨by omega,by omega⟩
  have hum : Znth (top-1) ks 0 ∈ sublist 0 top ks := hp.mem_iff.mpr (by simp)
  have hc := ((PreH30.1.2.1.2.2.1 _ hu).mp (List.mem_append.mpr (Or.inr hum))).2
  have hbit : Znth (Znth (top-1) ks 0) cs_2 0 = 1 := by
    have hh := PreH30.1.1.2 _ hu
    omega
  obtain ⟨hscan,hsum⟩ := component_frontier_pop_to_scan__frontier_pop_to_scan n_pre comments before_2 cs_2 finished_2 ks c0 c1 1 top hs ns_2 ts_2 ws_2 m_pre
    (by omega) PreH22 ⟨PreH15,PreH16⟩ PreH33 (by decide) hbit PreH30 PreH6 PreH31
  simp only [ite_true,show ¬ ((1:Int)=0) by decide,show ¬ ((0:Int)=1) by decide,↓reduceIte] at hscan
  have hhead := PreH32.1 _ hu
  have hedge : Znth (Znth (top-1) ks 0) hs 0 ≠ -1 →
      (((1 ≤ Znth (Znth (Znth (top-1) ks 0) hs 0) ts_2 0 ∧ Znth (Znth (Znth (top-1) ks 0) hs 0) ts_2 0 ≤ n_pre) ∧
       (Znth (Znth (Znth (top-1) ks 0) hs 0) ws_2 0 = 0 ∨ Znth (Znth (Znth (top-1) ks 0) hs 0) ws_2 0 = 1)) ∧
       -1 ≤ Znth (Znth (Znth (top-1) ks 0) hs 0) ns_2 0) ∧ Znth (Znth (Znth (top-1) ks 0) hs 0) ns_2 0 < 2*m_pre := by
    intro he
    obtain ⟨hn,ht,hw⟩ := PreH32.2 (Znth (Znth (top-1) ks 0) hs 0) ⟨by omega,by omega⟩
    exact ⟨⟨⟨ht,hw⟩,hn.1⟩,hn.2⟩
  have hpending : ∀ j, (0 ≤ j ∧ j < top-1) → 1 ≤ Znth j ks 0 ∧ Znth j ks 0 ≤ n_pre := by
    intro j hj
    exact PreH20 j ⟨hj.1,by omega⟩
  Right
  Exists hs finished_2 before_2 ks ns_2 ws_2 ts_2 cs_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_proof_manual
