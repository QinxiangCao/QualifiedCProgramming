import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_choices_extend

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem component_scan_advance_new__scan_edge_transitions (n cap : Int) (comments : List Comment)
    (hs ns ts ws before cs finished pending : List Int) (u e c0 c1 : Int)
    (hcap : cap = Zlength comments) (he : 0 ≤ e ∧ e < 2 * cap) (hu : 1 ≤ u ∧ u ≤ n)
    (hneg : Znth (Znth e ts 0) cs 0 < 0) (hfs : ForwardStar n cap cap hs ns ts ws comments)
    (hfr : ForwardStarRanges n cap hs ns ts ws)
    (hstrong : ComponentScanStrong n comments ns before cs finished pending u e c0 c1) :
    ComponentScanStrong n comments ns before
      (replace_Znth (Znth e ts 0) (Z.lxor (Znth u cs 0) (Znth e ws 0)) cs)
      finished (pending ++ [Znth e ts 0]) u (Znth e ns 0) c0 c1 := by
  let v := Znth e ts 0
  let w := Znth e ws 0
  let x := Z.lxor (Znth u cs 0) w
  let oldvs := finished ++ u :: pending
  have hec : 0 ≤ e ∧ e < 2 * Zlength comments := by omega
  obtain ⟨hdst, hwt⟩ := hfs.2.2.2.2.2.2.1 e he
  obtain ⟨hnext, hv, hw⟩ := hfr.2 e he
  change 1 ≤ v ∧ v ≤ n at hv
  change w = 0 ∨ w = 1 at hw
  rcases hstrong with ⟨⟨hcv, hnew, htwo, hfull, hscan, hc0, hc1⟩, howned, hlocal⟩
  have hcslen := hcv.1
  change Znth v cs 0 < 0 at hneg
  have hvm : Znth v cs 0 = -1 := by have := hcv.2 v hv; omega
  have huold : u ∈ oldvs := by simp [oldvs]
  have hsrc : edge_src comments e = u := by
    obtain ⟨remaining, hchain, hsources⟩ := howned.2
    have hm : e ∈ remaining := by
      cases hchain with
      | adj_end => omega
      | adj_cons e rest hp ht => simp
    exact hsources e hm
  have hdr : ∀ e0, (0 ≤ e0 ∧ e0 < 2 * Zlength comments) →
      0 ≤ edge_dst comments e0 ∧ edge_dst comments e0 < Zlength cs := by
    intro e0 he0
    have hecap : 0 ≤ e0 ∧ e0 < 2 * cap := by omega
    have hb := (hfr.2 e0 hecap).2.1
    have hd := (hfs.2.2.2.2.2.2.1 e0 hecap).1
    rw [← hd]
    omega
  have hor : ∀ z, z ∈ oldvs → 0 ≤ z ∧ z < Zlength cs := by
    intro z hz
    have hb := Forall.iff_forall_mem.mp hnew.2.1 z hz
    omega
  have huc : Znth u cs 0 ≠ -1 := ((hnew.2.2.1 u hu).mp huold).2
  have huv : u ≠ v := by intro heq; rw [heq, hvm] at huc; contradiction
  have hubit : Znth u cs 0 = 0 ∨ Znth u cs 0 = 1 := by have := hcv.2 u hu; omega
  have hxbit : x = 0 ∨ x = 1 := lxor_bit__scan_and_component_closure _ _ hubit hw
  have hfresh : v ∉ oldvs := by intro hm; exact ((hnew.2.2.1 v hv).mp hm).2 hvm
  have hglobal : ∀ roles, RolesConsistent n comments roles →
      Znth (v - 1) roles 0 = Z.lxor (Znth (u - 1) roles 0) w := by
    intro roles hr
    have hh := roles_consistent_edge__scan_edge_transitions n comments roles e hec
      (by rwa [hsrc]) (by rwa [← hdst]) (by rwa [← hwt]) hr
    rwa [hsrc, ← hdst, ← hwt] at hh
  have hlocaledge : ∀ roles, RolesConsistentOnVertices n comments (oldvs ++ [v]) roles →
      Znth (v - 1) roles 0 = Z.lxor (Znth (u - 1) roles 0) w := by
    intro roles hr
    have hs : edge_src comments e ∈ oldvs ++ [v] := by rw [hsrc]; exact List.mem_append.mpr (Or.inl huold)
    have hd : edge_dst comments e ∈ oldvs ++ [v] := by rw [← hdst]; exact List.mem_append.mpr (Or.inr (by simp [v]))
    have hh := roles_consistent_local_edge__scan_edge_transitions n comments (oldvs ++ [v]) roles e hec hs hd
      (by rwa [← hwt]) hr
    rwa [hsrc, ← hdst, ← hwt] at hh
  have hcv' := colour_values_replace__scan_edge_transitions n cs v x hv hxbit hcv
  have hnew' := new_colour_set_extend__scan_edge_transitions n before cs oldvs v x hv hxbit hneg hcv hnew
  have htwo' := component_two_choices_extend__scan_edge_transitions n comments before cs oldvs u v w x
    hcv hnew htwo huold hv hneg hw rfl hglobal
  have hlocal' := component_two_choices_local_extend__scan_edge_transitions n comments before cs oldvs u v w x
    hcv hnew hlocal huold hv hneg hw rfl hlocaledge
  have hfinished : finished ⊆ oldvs := by intro z hz; exact List.mem_append.mpr (Or.inl hz)
  have hfull' := fully_scanned_replace_fresh__scan_edge_transitions comments cs finished v x
    ⟨by omega, by omega⟩ hvm (fun hm => hfresh (hfinished hm))
    (by intro z hz; exact hor z (hfinished hz)) hdr hfull
  have howned' := scan_at_owned_advance_new__scan_edge_transitions comments ns cs u e v w x hec
    hdst.symm hwt.symm ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hvm huv hdr hxbit rfl howned
  have hcountsub : finished ++ [u] ⊆ oldvs := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hfinished hz
    · have hez : z = u := by simpa only [List.mem_singleton] using hz
      rwa [hez]
  have hc0' := colour_count_replace_fresh__scan_edge_transitions cs (finished ++ [u]) 0 c0 v x
    ⟨by omega, by omega⟩ (fun hm => hfresh (hcountsub hm)) (by intro z hz; exact hor z (hcountsub hz)) hc0
  have hc1' := colour_count_replace_fresh__scan_edge_transitions cs (finished ++ [u]) 1 c1 v x
    ⟨by omega, by omega⟩ (fun hm => hfresh (hcountsub hm)) (by intro z hz; exact hor z (hcountsub hz)) hc1
  have hshape : oldvs ++ [v] = finished ++ u :: (pending ++ [v]) := by simp only [oldvs, List.append_assoc, List.cons_append]
  rw [hshape] at hnew' htwo' hlocal'
  exact ⟨⟨hcv', hnew', htwo', hfull', howned'.1, hc0', hc1'⟩, howned', hlocal'⟩

theorem component_scan_advance_new_stack__scan_edge_transitions (n cap : Int) (comments : List Comment)
    (hs ns ts ws before cs finished ks : List Int) (u e c0 c1 top : Int)
    (hcap : cap = Zlength comments) (he : 0 ≤ e ∧ e < 2 * cap) (hu : 1 ≤ u ∧ u ≤ n)
    (hv : Znth (Znth e ts 0) cs 0 < 0) (ht : 0 ≤ top ∧ top < Zlength ks)
    (hfs : ForwardStar n cap cap hs ns ts ws comments) (hfr : ForwardStarRanges n cap hs ns ts ws)
    (hc : ComponentScanStrong n comments ns before cs finished (sublist 0 top ks) u e c0 c1) :
    ComponentScanStrong n comments ns before
      (replace_Znth (Znth e ts 0) (Z.lxor (Znth u cs 0) (Znth e ws 0)) cs)
      finished (sublist 0 (top + 1) (replace_Znth top (Znth e ts 0) ks)) u (Znth e ns 0) c0 c1 := by
  rw [sublist_replace_append__scan_edge_transitions _ _ _ ht]
  exact component_scan_advance_new__scan_edge_transitions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcap he hu hv hfs hfr hc

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
