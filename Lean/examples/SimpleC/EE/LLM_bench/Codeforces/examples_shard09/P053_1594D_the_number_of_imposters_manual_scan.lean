import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_manual_conflict

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

private theorem p053_next_edge_meta (n cap : Int) (hs ns ts ws : List Int) (e : Int)
    (he : -1 ≤ e ∧ e < 2*cap) (hr : ForwardStarRanges n cap hs ns ts ws) :
    e ≠ -1 → (((1 ≤ Znth e ts 0 ∧ Znth e ts 0 ≤ n) ∧ (Znth e ws 0 = 0 ∨ Znth e ws 0 = 1)) ∧
      -1 ≤ Znth e ns 0) ∧ Znth e ns 0 < 2*cap := by
  intro hne
  obtain ⟨hn,ht,hw⟩ := hr.2 e ⟨by omega,he.2⟩
  exact ⟨⟨⟨ht,hw⟩,hn.1⟩,hn.2⟩

theorem proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1 := by
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished_2 before_2 ks_2 ns_2 ws_2 ts_2 e c1 c0 top cs_2 u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have htop := PreH27 ⟨PreH2,PreH1⟩
  obtain ⟨⟨⟨hv,hw⟩,hnlo⟩,hnhi⟩ := PreH26 PreH2
  have hlen := PreH38.1.1.1
  have hpost := component_scan_advance_new_stack__scan_edge_transitions n_pre m_pre comments hs_2 ns_2 ts_2 ws_2 before_2 cs_2 finished_2 ks_2 u e c0 c1 top
    PreH7 ⟨by omega,PreH25⟩ ⟨PreH16,PreH17⟩ PreH1 ⟨PreH19,by omega⟩ PreH39 PreH40 PreH38
  have hks : Zlength (replace_Znth top (Znth e ts_2 0) ks_2) = n_pre+1 := by simpa only [Zlength_replace_Znth] using PreH30
  have hpostlt := component_scan_pending_top_lt__scan_edge_transitions n_pre comments ns_2 before_2
    (replace_Znth (Znth e ts_2 0) (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2) finished_2
    (replace_Znth top (Znth e ts_2 0) ks_2) u (Znth e ns_2 0) c0 c1 (top+1)
    (by omega) (by omega) (by omega) hks hpost
  have hedge := p053_next_edge_meta _ _ _ _ _ _ _ ⟨hnlo,hnhi⟩ PreH40
  have hfresh : Znth (Znth e ts_2 0) cs_2 0 = -1 := by have hh := PreH38.1.1.2 _ hv; omega
  have hune : Znth e ts_2 0 ≠ u := by intro hh; rw [hh,PreH18] at PreH1; omega
  have hsameu : Znth u (replace_Znth (Znth e ts_2 0) (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2) 0 = 0 := by
    rw [Znth_replace_Znth_Diff 0 cs_2 _ u _ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hune]
    exact PreH18
  have hsne : Znth e ts_2 0 ≠ s := by intro hh; rw [hh] at hfresh; exact PreH37 hfresh
  have hscol : Znth s (replace_Znth (Znth e ts_2 0) (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2) 0 ≠ -1 := by
    rw [Znth_replace_Znth_Diff 0 cs_2 _ s _ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hsne]
    exact PreH37
  have hstack : ∀ j, (0 ≤ j ∧ j < top+1) → 1 ≤ Znth j (replace_Znth top (Znth e ts_2 0) ks_2) 0 ∧ Znth j (replace_Znth top (Znth e ts_2 0) ks_2) 0 ≤ n_pre := by
    intro j hj
    by_cases he : top = j
    · subst j
      rw [Znth_replace_Znth_Same 0 ks_2 top _ ⟨by omega,by omega⟩]
      exact hv
    · rw [Znth_replace_Znth_Diff 0 ks_2 top j _ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ he]
      exact PreH28 j ⟨hj.1,by omega⟩
  Left
  Exists hs_2 finished_2 before_2 (replace_Znth top (Znth e ts_2 0) ks_2) ns_2 ws_2 ts_2
    (replace_Znth (Znth e ts_2 0) (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (intro hh; exact hpostlt)

theorem proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2 := by
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished_2 before_2 ks_2 ns_2 ws_2 ts_2 e c1 c0 top cs_2 u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have htop := PreH27 ⟨PreH2,PreH1⟩
  obtain ⟨⟨⟨hv,hw⟩,hnlo⟩,hnhi⟩ := PreH26 PreH2
  have hlen := PreH38.1.1.1
  have hpost := component_scan_advance_new_stack__scan_edge_transitions n_pre m_pre comments hs_2 ns_2 ts_2 ws_2 before_2 cs_2 finished_2 ks_2 u e c0 c1 top
    PreH7 ⟨by omega,PreH25⟩ ⟨PreH16,PreH17⟩ PreH1 ⟨PreH19,by omega⟩ PreH39 PreH40 PreH38
  have hks : Zlength (replace_Znth top (Znth e ts_2 0) ks_2) = n_pre+1 := by simpa only [Zlength_replace_Znth] using PreH30
  have hpostlt := component_scan_pending_top_lt__scan_edge_transitions n_pre comments ns_2 before_2
    (replace_Znth (Znth e ts_2 0) (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2) finished_2
    (replace_Znth top (Znth e ts_2 0) ks_2) u (Znth e ns_2 0) c0 c1 (top+1)
    (by omega) (by omega) (by omega) hks hpost
  have hedge := p053_next_edge_meta _ _ _ _ _ _ _ ⟨hnlo,hnhi⟩ PreH40
  have hfresh : Znth (Znth e ts_2 0) cs_2 0 = -1 := by have hh := PreH38.1.1.2 _ hv; omega
  have hune : Znth e ts_2 0 ≠ u := by intro hh; rw [hh,PreH18] at PreH1; omega
  have hsameu : Znth u (replace_Znth (Znth e ts_2 0) (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2) 0 = 1 := by
    rw [Znth_replace_Znth_Diff 0 cs_2 _ u _ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hune]
    exact PreH18
  have hsne : Znth e ts_2 0 ≠ s := by intro hh; rw [hh] at hfresh; exact PreH37 hfresh
  have hscol : Znth s (replace_Znth (Znth e ts_2 0) (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2) 0 ≠ -1 := by
    rw [Znth_replace_Znth_Diff 0 cs_2 _ s _ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hsne]
    exact PreH37
  have hstack : ∀ j, (0 ≤ j ∧ j < top+1) → 1 ≤ Znth j (replace_Znth top (Znth e ts_2 0) ks_2) 0 ∧ Znth j (replace_Znth top (Znth e ts_2 0) ks_2) 0 ≤ n_pre := by
    intro j hj
    by_cases he : top = j
    · subst j
      rw [Znth_replace_Znth_Same 0 ks_2 top _ ⟨by omega,by omega⟩]
      exact hv
    · rw [Znth_replace_Znth_Diff 0 ks_2 top j _ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ he]
      exact PreH28 j ⟨hj.1,by omega⟩
  Right
  Exists hs_2 finished_2 before_2 (replace_Znth top (Znth e ts_2 0) ks_2) ns_2 ws_2 ts_2
    (replace_Znth (Znth e ts_2 0) (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (intro hh; exact hpostlt)

theorem proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3 := by
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished_2 before_2 ks_2 ns_2 ws_2 ts_2 e c1 c0 top cs_2 u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  obtain ⟨⟨⟨hv,hw⟩,hnlo⟩,hnhi⟩ := PreH27 PreH3
  have hedge := p053_next_edge_meta _ _ _ _ _ _ _ ⟨hnlo,hnhi⟩ PreH41
  have htop := component_scan_pending_top_lt__scan_edge_transitions _ _ _ _ _ _ _ _ _ _ _ _
    (by omega) PreH20 PreH21 PreH31 PreH39
  have hobs := PreH40.2.2.2.2.2.2.1 e ⟨by omega,PreH26⟩
  have hpost := component_scan_advance_existing__scan_edge_transitions n_pre comments ns_2 before_2 cs_2 finished_2 (sublist 0 top ks_2) u e c0 c1 ts_2 ws_2
    PreH3 ⟨by omega,by omega⟩ hobs.1 hobs.2 PreH2 PreH1 PreH39
  Left
  Exists hs_2 finished_2 before_2 ks_2 ns_2 ws_2 ts_2 cs_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (intro hh; exact htop)

theorem proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4 := by
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre comment_diff_pre comment_v_pre comment_u_pre m_pre n_pre comment_kinds comment_targets comment_sources comments hs_2 finished_2 before_2 ks_2 ns_2 ws_2 ts_2 e c1 c0 top cs_2 u total s __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  obtain ⟨⟨⟨hv,hw⟩,hnlo⟩,hnhi⟩ := PreH27 PreH3
  have hedge := p053_next_edge_meta _ _ _ _ _ _ _ ⟨hnlo,hnhi⟩ PreH41
  have htop := component_scan_pending_top_lt__scan_edge_transitions _ _ _ _ _ _ _ _ _ _ _ _
    (by omega) PreH20 PreH21 PreH31 PreH39
  have hobs := PreH40.2.2.2.2.2.2.1 e ⟨by omega,PreH26⟩
  have hpost := component_scan_advance_existing__scan_edge_transitions n_pre comments ns_2 before_2 cs_2 finished_2 (sublist 0 top ks_2) u e c0 c1 ts_2 ws_2
    PreH3 ⟨by omega,by omega⟩ hobs.1 hobs.2 PreH2 PreH1 PreH39
  Right
  Exists hs_2 finished_2 before_2 ks_2 ns_2 ws_2 ts_2 cs_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (intro hh; exact htop)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_proof_manual
