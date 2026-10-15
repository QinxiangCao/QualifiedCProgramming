import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_manual_initialization

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

private def p053_hs (i u v : Int) (hs : List Int) := replace_Znth v (2*i+1) (replace_Znth u (2*i) hs)
private def p053_ns (i u v : Int) (hs ns : List Int) := replace_Znth (2*i+1) (Znth v (replace_Znth u (2*i) hs) 0) (replace_Znth (2*i) (Znth u hs 0) ns)
private def p053_ts (i u v : Int) (ts : List Int) := replace_Znth (2*i+1) u (replace_Znth (2*i) v ts)
private def p053_ws (i w : Int) (ws : List Int) := replace_Znth (2*i+1) w (replace_Znth (2*i) w ws)

private theorem p053_pair_get (xs : List Int) (i j a b q : Int)
    (hi : 0 ≤ i ∧ i < Zlength xs) (hj : 0 ≤ j ∧ j < Zlength xs)
    (hq : 0 ≤ q ∧ q < Zlength xs) :
    Znth q (replace_Znth j b (replace_Znth i a xs)) 0 =
      if q = j then b else if q = i then a else Znth q xs 0 := by
  have hl := Zlength_replace_Znth xs i a
  by_cases he : q = j
  · subst q
    rw [Znth_replace_Znth_Same 0 _ _ _ ⟨by omega,by omega⟩]
    simp
  · rw [Znth_replace_Znth_Diff 0 _ j q b ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (Ne.symm he)]
    simp only [he,↓reduceIte]
    by_cases hqi : q = i
    · subst q
      rw [Znth_replace_Znth_Same 0 xs i a hi]
      simp
    · rw [Znth_replace_Znth_Diff 0 xs i q a hi hq (Ne.symm hqi)]
      simp [hqi]

private theorem p053_build_step (n cap i : Int) (comments : List Comment)
    (hs ns ts ws : List Int) (u v w : Int) (hcap : cap = Zlength comments)
    (hi : 0 ≤ i ∧ i < cap) (hu : 1 ≤ u ∧ u ≤ n) (hv : 1 ≤ v ∧ v ≤ n)
    (hne : u ≠ v) (hw : w = 0 ∨ w = 1) (hq : comment_at comments i = ((u,v),w))
    (hf : ForwardStar n cap i hs ns ts ws comments) (hr : ForwardStarRanges n i hs ns ts ws) :
    ForwardStarRanges n (i+1) (p053_hs i u v hs) (p053_ns i u v hs ns) (p053_ts i u v ts) (p053_ws i w ws) ∧
    ForwardStar n cap (i+1) (p053_hs i u v hs) (p053_ns i u v hs ns) (p053_ts i u v ts) (p053_ws i w ws) comments := by
  have hhs := hf.1
  have hns := hf.2.1
  have hts := hf.2.2.1
  have hws := hf.2.2.2.1
  have headv : Znth v (replace_Znth u (2*i) hs) 0 = Znth v hs 0 :=
    Znth_replace_Znth_Diff 0 hs u v (2*i) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hne
  have hhget (q : Int) (hq : 1 ≤ q ∧ q ≤ n) :
      Znth q (p053_hs i u v hs) 0 = if q = v then 2*i+1 else if q = u then 2*i else Znth q hs 0 :=
    p053_pair_get hs u v (2*i) (2*i+1) q ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hnget (e : Int) (he : 0 ≤ e ∧ e < 2*cap) :
      Znth e (p053_ns i u v hs ns) 0 = if e = 2*i+1 then Znth v hs 0 else if e = 2*i then Znth u hs 0 else Znth e ns 0 := by
    unfold p053_ns
    rw [headv]
    exact p053_pair_get ns (2*i) (2*i+1) _ _ e ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have htget (e : Int) (he : 0 ≤ e ∧ e < 2*cap) :
      Znth e (p053_ts i u v ts) 0 = if e = 2*i+1 then u else if e = 2*i then v else Znth e ts 0 :=
    p053_pair_get ts (2*i) (2*i+1) v u e ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hwget (e : Int) (he : 0 ≤ e ∧ e < 2*cap) :
      Znth e (p053_ws i w ws) 0 = if e = 2*i+1 then w else if e = 2*i then w else Znth e ws 0 :=
    p053_pair_get ws (2*i) (2*i+1) w w e ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  obtain ⟨hse,hde,hwe⟩ := edge_forward__scan_and_component_closure comments i u v w hq
  obtain ⟨hso,hdo,hwo⟩ := edge_reverse__scan_and_component_closure comments i u v w hq
  constructor
  · constructor
    · intro q hq
      rw [hhget q hq]
      have hold := hr.1 q hq
      split <;> (try split) <;> omega
    · intro e he
      have hecap : 0 ≤ e ∧ e < 2*cap := by omega
      rw [hnget e hecap,htget e hecap,hwget e hecap]
      by_cases heo : e = 2*i+1
      · simp only [heo,ite_true]
        have hold := hr.1 v hv
        exact ⟨⟨by omega,by omega⟩,hu,hw⟩
      · by_cases hee : e = 2*i
        · simp only [heo,hee,show 2*i ≠ 2*i+1 by omega,↓reduceIte]
          have hold := hr.1 u hu
          exact ⟨⟨by omega,by omega⟩,hv,hw⟩
        · simp only [heo,hee,show 2*i ≠ 2*i+1 by omega,↓reduceIte]
          obtain ⟨hn,ht,hw⟩ := hr.2 e ⟨by omega,by omega⟩
          exact ⟨⟨hn.1,by omega⟩,ht,hw⟩
  · refine ⟨?_,?_,?_,?_,⟨by omega,by omega⟩,by omega,?_,?_⟩
    · simpa only [p053_hs,Zlength_replace_Znth] using hhs
    · simpa only [p053_ns,Zlength_replace_Znth] using hns
    · simpa only [p053_ts,Zlength_replace_Znth] using hts
    · simpa only [p053_ws,Zlength_replace_Znth] using hws
    · intro e he
      have hecap : 0 ≤ e ∧ e < 2*cap := by omega
      rw [htget e hecap,hwget e hecap]
      by_cases heo : e = 2*i+1
      · subst e
        simp only [ite_true,hdo,hwo]
        constructor <;> trivial
      · by_cases hee : e = 2*i
        · subst e
          simp only [heo,↓reduceIte,hde,hwe]
          constructor <;> trivial
        · simp only [heo,hee,show 2*i ≠ 2*i+1 by omega,↓reduceIte]
          exact hf.2.2.2.2.2.2.1 e ⟨by omega,by omega⟩
    · intro q hqb
      obtain ⟨es,hchain,hnd,hmem⟩ := hf.2.2.2.2.2.2.2 q hqb
      have hchain' : AdjChain (p053_ns i u v hs ns) (Znth q hs 0) es := by
        apply AdjChain_ext__forward_star_build_step _ _ _ _ hchain
        intro e he
        have hb := (hmem e).mp he
        rw [hnget e ⟨by omega,by omega⟩]
        simp only [show e ≠ 2*i+1 by omega,show e ≠ 2*i by omega,↓reduceIte]
      have hnew_e : 2*i ∉ es := by intro hm; have hh := (hmem _).mp hm; omega
      have hnew_o : 2*i+1 ∉ es := by intro hm; have hh := (hmem _).mp hm; omega
      by_cases hqu : q = u
      · subst q
        refine ⟨2*i :: es,?_,List.nodup_cons.mpr ⟨hnew_e,hnd⟩,?_⟩
        · rw [hhget u hu]
          simp only [hne,↓reduceIte]
          apply adj_cons _ _ (by omega)
          rw [hnget (2*i) ⟨by omega,by omega⟩]
          simpa only [show 2*i ≠ 2*i+1 by omega,↓reduceIte] using hchain'
        · intro e
          simp only [List.mem_cons]
          constructor
          · rintro (he | hm)
            · subst e
              exact ⟨⟨by omega,by omega⟩,hse⟩
            · obtain ⟨he,hs⟩ := (hmem e).mp hm
              exact ⟨⟨by omega,by omega⟩,hs⟩
          · rintro ⟨he,hs⟩
            by_cases hee : e = 2*i
            · exact Or.inl hee
            · right
              have heo : e ≠ 2*i+1 := by intro heq; rw [heq,hso] at hs; exact hne hs.symm
              exact (hmem e).mpr ⟨⟨by omega,by omega⟩,hs⟩
      · by_cases hqv : q = v
        · subst q
          refine ⟨(2*i+1) :: es,?_,List.nodup_cons.mpr ⟨hnew_o,hnd⟩,?_⟩
          · rw [hhget v hv]
            simp only [ite_true]
            apply adj_cons _ _ (by omega)
            rw [hnget (2*i+1) ⟨by omega,by omega⟩]
            simpa only [ite_true] using hchain'
          · intro e
            simp only [List.mem_cons]
            constructor
            · rintro (he | hm)
              · subst e
                exact ⟨⟨by omega,by omega⟩,hso⟩
              · obtain ⟨he,hs⟩ := (hmem e).mp hm
                exact ⟨⟨by omega,by omega⟩,hs⟩
            · rintro ⟨he,hs⟩
              by_cases heo : e = 2*i+1
              · exact Or.inl heo
              · right
                have hee : e ≠ 2*i := by intro heq; rw [heq,hse] at hs; exact hne hs
                exact (hmem e).mpr ⟨⟨by omega,by omega⟩,hs⟩
        · refine ⟨es,?_,hnd,?_⟩
          · rw [hhget q hqb]
            simpa only [hqu,hqv,↓reduceIte] using hchain'
          · intro e
            constructor
            · intro hm
              obtain ⟨he,hs⟩ := (hmem e).mp hm
              exact ⟨⟨by omega,by omega⟩,hs⟩
            · rintro ⟨he,hs⟩
              have heo : e ≠ 2*i+1 := by intro heq; rw [heq,hso] at hs; exact hqv hs.symm
              have hee : e ≠ 2*i := by intro heq; rw [heq,hse] at hs; exact hqu hs.symm
              exact (hmem e).mpr ⟨⟨by omega,by omega⟩,hs⟩

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hm := PreH10 i ⟨PreH11,PreH1⟩
  obtain ⟨⟨⟨hb,hsmeta⟩,htmeta⟩,hwmeta⟩ := hm
  obtain ⟨⟨⟨⟨⟨hs1,hs2⟩,ht1⟩,ht2⟩,hne⟩,hw⟩ := hb
  have hcat : comment_at comments i = ((Znth i comment_sources 0,Znth i comment_targets 0),Znth i comment_kinds 0) := by
    unfold comment_at
    rw [Znth_indep comments i ((0,0),0) __default__Prod__Prod_Z_Z_Z ⟨by omega,by omega⟩]
    rw [hsmeta,htmeta,hwmeta]
  have hh := p053_build_step n_pre m_pre i comments hs_2 ns_2 ts_2 ws_2
    (Znth i comment_sources 0) (Znth i comment_targets 0) (Znth i comment_kinds 0)
    PreH6 ⟨PreH11,PreH1⟩ ⟨hs1,hs2⟩ ⟨ht1,ht2⟩ hne hw hcat PreH14 PreH15
  exact hh.1

theorem proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2 := by
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hm := PreH10 i ⟨PreH11,PreH1⟩
  obtain ⟨⟨⟨hb,hsmeta⟩,htmeta⟩,hwmeta⟩ := hm
  obtain ⟨⟨⟨⟨⟨hs1,hs2⟩,ht1⟩,ht2⟩,hne⟩,hw⟩ := hb
  have hcat : comment_at comments i = ((Znth i comment_sources 0,Znth i comment_targets 0),Znth i comment_kinds 0) := by
    unfold comment_at
    rw [Znth_indep comments i ((0,0),0) __default__Prod__Prod_Z_Z_Z ⟨by omega,by omega⟩]
    rw [hsmeta,htmeta,hwmeta]
  have hh := p053_build_step n_pre m_pre i comments hs_2 ns_2 ts_2 ws_2
    (Znth i comment_sources 0) (Znth i comment_targets 0) (Znth i comment_kinds 0)
    PreH6 ⟨PreH11,PreH1⟩ ⟨hs1,hs2⟩ ⟨ht1,ht2⟩ hne hw hcat PreH14 PreH15
  exact hh.2

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_4_split_goal_1 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_4_split_goal_2 m_pre n_pre comment_kinds comment_targets comment_sources comments ks_2 cs_2 hs_2 ns_2 ts_2 ws_2 i __default__Prod__Prod_Z_Z_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_proof_manual
