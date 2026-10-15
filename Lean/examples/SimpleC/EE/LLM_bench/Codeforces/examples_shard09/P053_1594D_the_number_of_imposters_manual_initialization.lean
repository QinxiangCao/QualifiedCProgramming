import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_goal

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

private theorem shape_rec (storeA : Int → Int → Int → SacContext.rules.expr)
    (k : Nat) (x lo hi : Int) :
    store_undef_array_rec SacContext.rules (fun x lo => EX a : Int, storeA x lo a) x lo hi k |--
      EX l : List Int, store_array_rec SacContext.rules storeA x lo hi l := by
  induction k generalizing lo with
  | zero =>
    simp only [store_undef_array_rec]
    Intros_p he
    Exists ([] : List Int)
    simp only [store_array_rec]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals solve | assumption | rfl | trivial
  | succ k ih =>
    simp only [store_undef_array_rec]
    Intros a
    sep_apply (ih (lo+1))
    Intros l
    Exists (a::l)
    simp only [store_array_rec]
    cancel

private theorem shape_full (x n : Int) :
    intArray.full_shape x n |-- EX l : List Int, intArray.full x n l := by
  apply shape_rec

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro stack__pre color_pre wt_pre to_pre nxt_pre head_pre m_pre n_pre comment_kinds comment_targets comment_sources comments __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  sep_apply (shape_full head_pre (n_pre+1))
  Intros hs
  prop_apply (intArray.full_Zlength head_pre (n_pre+1) hs)
  Intros_p hlen_hs
  sep_apply (shape_full nxt_pre (2*m_pre))
  Intros ns
  prop_apply (intArray.full_Zlength nxt_pre (2*m_pre) ns)
  Intros_p hlen_ns
  sep_apply (shape_full to_pre (2*m_pre))
  Intros ts
  prop_apply (intArray.full_Zlength to_pre (2*m_pre) ts)
  Intros_p hlen_ts
  sep_apply (shape_full wt_pre (2*m_pre))
  Intros ws
  prop_apply (intArray.full_Zlength wt_pre (2*m_pre) ws)
  Intros_p hlen_ws
  sep_apply (shape_full color_pre (n_pre+1))
  Intros cs
  prop_apply (intArray.full_Zlength color_pre (n_pre+1) cs)
  Intros_p hlen_cs
  sep_apply (shape_full stack__pre (n_pre+1))
  Intros ks
  prop_apply (intArray.full_Zlength stack__pre (n_pre+1) ks)
  Intros_p hlen_ks
  have hm := Zlength_nonneg comments
  Exists ks cs ws ts ns hs
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (unfold HeadsInitialised; intro v hv; omega) | skip
    intro i hi
    have hb := PreH4 i hi
    have hm := PreH9 i hi
    exact ⟨⟨⟨hb,hm.1.1⟩,hm.1.2⟩,hm.2⟩

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  intro i hi
  by_cases he : v = i
  · subst i
    exact Znth_replace_Znth_Same 0 hs_2 v (-1) ⟨by omega,by omega⟩
  · rw [Znth_replace_Znth_Diff 0 hs_2 v i (-1) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ he]
    exact PreH19 i ⟨by omega,by omega⟩

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  simpa only [Zlength_replace_Znth] using PreH13

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_2_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_solver_entail_wit_2_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  constructor
  · intro u hu
    rw [PreH19 u ⟨by omega,by omega⟩]
    omega
  · intro e he
    omega

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  refine ⟨PreH13,PreH14,PreH15,PreH16,⟨by omega,by omega⟩,by omega,?_,?_⟩
  · intro e he
    omega
  · intro u hu
    refine ⟨[],?_,by simp,?_⟩
    · rw [PreH19 u ⟨by omega,by omega⟩]
      exact adj_end
    · intro e
      simp only [List.not_mem_nil]
      constructor
      · intro hh
        exact False.elim hh
      · intro hh
        omega

theorem proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  intro q hq
  have hm := PreH10 q hq
  obtain ⟨⟨⟨hb,hs⟩,ht⟩,hk⟩ := hm
  rw [hs,ht,hk]
  exact ⟨⟨⟨hb,rfl⟩,rfl⟩,rfl⟩

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_3_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_solver_entail_wit_3_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_solver_entail_wit_3_split_goal_3 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 ws_2 ts_2 ns_2 hs_2 v __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_proof_manual
