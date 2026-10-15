import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_parity_edges

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem p053_NewColourSet_perm (n : Int) (before after old new : List Int)
    (hp : old.Perm new) (hn : NewColourSet n before after old) : NewColourSet n before after new := by
  rcases hn with ⟨hnd, hall, hiff, hsame⟩
  refine ⟨hp.nodup_iff.mp hnd, ?_, ?_, ?_⟩
  · apply Forall.iff_forall_mem.mpr
    intro v hv
    exact Forall.iff_forall_mem.mp hall v (hp.mem_iff.mpr hv)
  · intro v hv
    exact hp.mem_iff.symm.trans (hiff v hv)
  · intro v hv hn
    exact hsame v hv (fun hm => hn (hp.mem_iff.mp hm))

theorem p053_ComponentTwoChoices_perm (n : Int) (comments : List Comment) (cs old new : List Int)
    (hp : old.Perm new) (hc : ComponentTwoChoices n comments cs old) : ComponentTwoChoices n comments cs new := by
  intro roles hr
  obtain ⟨flip, hf, he⟩ := hc roles hr
  exact ⟨flip, hf, by intro v hv; exact he v (hp.mem_iff.mpr hv)⟩

theorem p053_ComponentTwoChoicesLocal_perm (n : Int) (comments : List Comment) (cs old new : List Int)
    (hp : old.Perm new) (hc : ComponentTwoChoicesLocal n comments cs old) :
    ComponentTwoChoicesLocal n comments cs new := by
  intro roles hr
  have hr' : RolesConsistentOnVertices n comments old roles := by
    rcases hr with ⟨hl, hb, he⟩
    refine ⟨hl, by intro v hv; exact hb v (hp.mem_iff.mp hv), ?_⟩
    intro i hi
    dsimp
    intro hu hv
    exact he i hi (hp.mem_iff.mp hu) (hp.mem_iff.mp hv)
  obtain ⟨flip, hf, he⟩ := hc roles hr'
  exact ⟨flip, hf, by intro v hv; exact he v (hp.mem_iff.mpr hv)⟩

theorem component_frontier_pop_to_scan__frontier_pop_to_scan (n : Int) (comments : List Comment)
    (before after finished ks : List Int) (c0 c1 bit top : Int) (hs ns ts ws : List Int) (cap : Int)
    (hn : 0 ≤ n) (hks : Zlength ks = n + 1) (htop : 0 ≤ top ∧ top ≤ n) (hne : top ≠ 0)
    (hbit : bit = 0 ∨ bit = 1) (hcolor : Znth (Znth (top - 1) ks 0) after 0 = bit)
    (hstrong : ComponentFrontierStrong n comments before after finished (sublist 0 top ks) c0 c1)
    (hcap : cap = Zlength comments) (hfs : ForwardStar n cap cap hs ns ts ws comments) :
    ComponentScanStrong n comments ns before after finished (sublist 0 (top - 1) ks)
      (Znth (top - 1) ks 0) (Znth (Znth (top - 1) ks 0) hs 0)
      (if bit = 0 then c0 + 1 else c0) (if bit = 1 then c1 + 1 else c1) ∧ c0 + 1 + c1 ≤ n := by
  let u := Znth (top - 1) ks 0
  let pending := sublist 0 (top - 1) ks
  have hp : (finished ++ sublist 0 top ks).Perm (finished ++ u :: pending) :=
    (sublist_pop_permutation__frontier_pop_to_scan ks top ⟨by omega, by omega⟩).append_left finished
  rcases hstrong with ⟨⟨hcv, hnew, htwo, hscanned, hc0, hc1⟩, hlocal⟩
  have hnew' := p053_NewColourSet_perm _ _ _ _ _ hp hnew
  have htwo' := p053_ComponentTwoChoices_perm _ _ _ _ _ hp htwo
  have hlocal' := p053_ComponentTwoChoicesLocal_perm _ _ _ _ _ hp hlocal
  have hu : u ∈ finished ++ u :: pending := by simp
  have hub := Forall.iff_forall_mem.mp hnew'.2.1 u hu
  obtain ⟨es, hadj, hnd, hes⟩ := hfs.2.2.2.2.2.2.2 u hub
  have hscan : ScanAt comments ns after u (Znth u hs 0) := by
    refine ⟨es, hadj, ?_⟩
    intro e he hsrc hnot
    exact False.elim (hnot ((hes e).mpr ⟨⟨he.1, by omega⟩, hsrc⟩))
  have howned : ScanAtOwned comments ns after u (Znth u hs 0) :=
    ⟨hscan, es, hadj, by intro e he; exact ((hes e).mp he).2⟩
  have hcount0 : ColourCount after (finished ++ [u]) 0 (if bit = 0 then c0 + 1 else c0) := by
    unfold ColourCount at hc0 ⊢
    simp only [List.map_append, List.map_cons, List.map_nil, List.count_append, List.count_cons,
      List.count_nil, Nat.cast_add, Nat.cast_zero]
    change Znth u after 0 = bit at hcolor
    rw [hcolor]
    rcases hbit with rfl | rfl
    all_goals simp only [show ((0 : Int) = 1) ↔ False by decide,
      show ((1 : Int) = 0) ↔ False by decide, beq_self_eq_true,
      show ((0 : Int) == 1) = false by decide, show ((1 : Int) == 0) = false by decide,
      Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Nat.cast_zero, zero_add]
    all_goals omega
  have hcount1 : ColourCount after (finished ++ [u]) 1 (if bit = 1 then c1 + 1 else c1) := by
    unfold ColourCount at hc1 ⊢
    simp only [List.map_append, List.map_cons, List.map_nil, List.count_append, List.count_cons,
      List.count_nil, Nat.cast_add, Nat.cast_zero]
    change Znth u after 0 = bit at hcolor
    rw [hcolor]
    rcases hbit with rfl | rfl
    all_goals simp only [show ((0 : Int) = 1) ↔ False by decide,
      show ((1 : Int) = 0) ↔ False by decide, beq_self_eq_true,
      show ((0 : Int) == 1) = false by decide, show ((1 : Int) == 0) = false by decide,
      Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Nat.cast_zero, zero_add]
    all_goals omega
  refine ⟨⟨⟨hcv, hnew', htwo', hscanned, hscan, hcount0, hcount1⟩, howned, hlocal'⟩, ?_⟩
  have hfb : Forall (fun v => 1 ≤ v ∧ v ≤ n) (finished ++ [u]) := by
    apply Forall.iff_forall_mem.mpr
    intro v hv
    apply Forall.iff_forall_mem.mp hnew'.2.1 v
    rcases List.mem_append.mp hv with hv | hv
    · exact List.mem_append.mpr (Or.inl hv)
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl (by simpa using hv))))
  have hfnd := nodup_app_keep_head__frontier_pop_to_scan finished pending u hnew'.1
  have hlen := nodup_bounded_Zlength__frontier_pop_to_scan _ n hn hfnd hfb
  have hfinishb : Forall (fun v => 1 ≤ v ∧ v ≤ n) finished := by
    apply Forall.iff_forall_mem.mpr
    intro v hv
    exact Forall.iff_forall_mem.mp hfb v (List.mem_append.mpr (Or.inl hv))
  have hfinishc : ∀ v, v ∈ finished → Znth v after 0 ≠ -1 := by
    intro v hv
    have hb := Forall.iff_forall_mem.mp hfinishb v hv
    exact ((hnew'.2.2.1 v hb).mp (List.mem_append.mpr (Or.inl hv))).2
  have hcover := colour_counts_cover__frontier_pop_to_scan n after finished hcv hfinishb hfinishc
  unfold ColourCount at hc0 hc1
  simp only [Zlength, List.length_append, List.length_cons, List.length_nil, Int.ofNat_eq_coe] at hlen
  omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
