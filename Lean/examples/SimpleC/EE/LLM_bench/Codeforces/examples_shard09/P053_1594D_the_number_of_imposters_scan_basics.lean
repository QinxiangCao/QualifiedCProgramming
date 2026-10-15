import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_conflict
import AUXLib.ListLib.Sequence

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem In_Zseq_iff__scan_edge_transitions (s : Int) (len : Nat) (a : Int) :
    a ∈ Zseq s len ↔ ∃ k : Nat, k < len ∧ a = s + (k : Int) := by
  induction len generalizing s with
  | zero => simp only [Zseq, List.not_mem_nil, Nat.not_lt_zero, false_and, exists_false]
  | succ len ih =>
    simp only [Zseq, List.mem_cons, ih]
    constructor
    · rintro (he | ⟨k, hk, he⟩)
      · exact ⟨0, by omega, by omega⟩
      · exact ⟨k + 1, by omega, by omega⟩
    · rintro ⟨k, hk, he⟩
      cases k with
      | zero => left; omega
      | succ k => right; exact ⟨k, by omega, by omega⟩

theorem sublist_replace_append__scan_edge_transitions (l : List Int) (top v : Int)
    (ht : 0 ≤ top ∧ top < Zlength l) :
    sublist 0 (top + 1) (replace_Znth top v l) = sublist 0 top l ++ [v] := by
  have hl := Zlength_replace_Znth l top v
  rw [sublist_split 0 (top + 1) top (replace_Znth top v l) ⟨by omega, ht.1⟩ ⟨by omega, by omega⟩]
  have hp : sublist 0 top (replace_Znth top v l) = sublist 0 top l := by
    apply (ListLib.list_eq_ext _ _ 0).mpr
    simp only [ListLib.Zlength, ListLib.Znth]
    have hll := p053_Zlength_sublist 0 top (replace_Znth top v l) ⟨by omega, ht.1⟩ (by omega)
    have hlr := p053_Zlength_sublist 0 top l ⟨by omega, ht.1⟩ (by omega)
    refine ⟨hll.trans hlr.symm, ?_⟩
    intro k hk
    rw [Znth_sublist 0 0 k top (replace_Znth top v l) (by omega) ⟨hk.1, by omega⟩,
      Znth_sublist 0 0 k top l (by omega) ⟨hk.1, by omega⟩]
    exact Znth_replace_Znth_Diff 0 l top (k + 0) v ht ⟨by omega, by omega⟩ (by omega)
  rw [hp, sublist_single 0 top (replace_Znth top v l) ⟨ht.1, by omega⟩,
    Znth_replace_Znth_Same 0 l top v ht]

theorem nodup_vertex_range_Zlength__scan_edge_transitions (n : Int) (vertices : List Int)
    (hn : 0 ≤ n) (hnd : vertices.Nodup) (hr : Forall (fun v => 1 ≤ v ∧ v ≤ n) vertices) :
    Zlength vertices ≤ n := nodup_bounded_Zlength__frontier_pop_to_scan vertices n hn hnd hr

theorem component_scan_pending_top_lt__scan_edge_transitions (n : Int) (comments : List Comment)
    (ns before cs finished ks : List Int) (u e c0 c1 top : Int)
    (hn : 0 ≤ n) (ht : 0 ≤ top) (htn : top ≤ n) (hks : Zlength ks = n + 1)
    (hc : ComponentScanStrong n comments ns before cs finished (sublist 0 top ks) u e c0 c1) : top < n := by
  have hnew := hc.1.2.1
  have hl := nodup_vertex_range_Zlength__scan_edge_transitions n _ hn hnew.1 hnew.2.1
  rw [Zlength_app, Zlength_cons, p053_Zlength_sublist 0 top ks ⟨by omega, ht⟩ (by omega)] at hl
  have := Zlength_nonneg finished
  omega

private theorem p053_scan_existing (comments : List Comment) (ns cs : List Int) (u e : Int)
    (he : e ≠ -1) (hd : Znth (edge_dst comments e) cs 0 ≠ -1)
    (hrel : Znth (edge_dst comments e) cs 0 = Z.lxor (Znth u cs 0) (edge_wt comments e))
    (hc : ScanAt comments ns cs u e) : ScanAt comments ns cs u (Znth e ns 0) := by
  rcases hc with ⟨remaining, hchain, hdone⟩
  cases hchain with
  | adj_end => contradiction
  | adj_cons e rest hp ht =>
    refine ⟨rest, ht, ?_⟩
    intro e0 he0 hs hn
    by_cases hh : e0 = e
    · subst e0; exact ⟨hd, hrel⟩
    · exact hdone e0 he0 hs (by simpa only [List.mem_cons, not_or] using And.intro hh hn)

theorem component_scan_advance_existing__scan_edge_transitions (n : Int) (comments : List Comment)
    (ns before cs finished pending : List Int) (u e c0 c1 : Int) (ts ws : List Int)
    (he : e ≠ -1) (her : 0 ≤ e ∧ e < 2 * Zlength comments)
    (hd : Znth e ts 0 = edge_dst comments e) (hw : Znth e ws 0 = edge_wt comments e)
    (hc : 0 ≤ Znth (Znth e ts 0) cs 0)
    (hr : Znth (Znth e ts 0) cs 0 = Z.lxor (Znth u cs 0) (Znth e ws 0))
    (hs : ComponentScanStrong n comments ns before cs finished pending u e c0 c1) :
    ComponentScanStrong n comments ns before cs finished pending u (Znth e ns 0) c0 c1 := by
  rcases hs with ⟨⟨hcv, hnew, htwo, hfull, hscan, hc0, hc1⟩, ⟨hscan', remaining, hchain, hsrc⟩, hlocal⟩
  have hscannew := p053_scan_existing comments ns cs u e he (by rw [← hd]; omega)
    (by rwa [← hd, ← hw]) hscan
  refine ⟨⟨hcv, hnew, htwo, hfull, hscannew, hc0, hc1⟩, ⟨hscannew, ?_⟩, hlocal⟩
  cases hchain with
  | adj_end => contradiction
  | adj_cons e rest hp ht => exact ⟨rest, ht, by intro e0 hm; exact hsrc e0 (List.mem_cons_of_mem _ hm)⟩

theorem colour_values_replace__scan_edge_transitions (n : Int) (cs : List Int) (v x : Int)
    (hv : 1 ≤ v ∧ v ≤ n) (hx : x = 0 ∨ x = 1) (hc : ColourValues n cs) :
    ColourValues n (replace_Znth v x cs) := by
  refine ⟨by rw [Zlength_replace_Znth]; exact hc.1, ?_⟩
  intro z hz
  by_cases he : z = v
  · subst z
    rw [Znth_replace_Znth_Same 0 cs v x ⟨by omega, by rw [hc.1]; omega⟩]
    exact Or.inr hx
  · rw [Znth_replace_Znth_Diff 0 cs v z x ⟨by omega, by rw [hc.1]; omega⟩
      ⟨by omega, by rw [hc.1]; omega⟩ (Ne.symm he)]
    exact hc.2 z hz

theorem fully_scanned_replace_fresh__scan_edge_transitions (comments : List Comment)
    (cs finished : List Int) (v x : Int) (hv : 0 ≤ v ∧ v < Zlength cs) (hvm : Znth v cs 0 = -1)
    (hf : v ∉ finished) (hfr : ∀ z, z ∈ finished → 0 ≤ z ∧ z < Zlength cs)
    (hdr : ∀ e, (0 ≤ e ∧ e < 2 * Zlength comments) → 0 ≤ edge_dst comments e ∧ edge_dst comments e < Zlength cs)
    (hc : FullyScanned comments cs finished) : FullyScanned comments (replace_Znth v x cs) finished := by
  intro e he hm
  obtain ⟨hcol, hrel⟩ := hc e he hm
  have hsne : v ≠ edge_src comments e := by intro hh; exact hf (hh ▸ hm)
  have hdne : v ≠ edge_dst comments e := by intro hh; rw [← hh, hvm] at hcol; contradiction
  rw [Znth_replace_Znth_Diff 0 cs v (edge_dst comments e) x hv (hdr e he) hdne,
    Znth_replace_Znth_Diff 0 cs v (edge_src comments e) x hv (hfr _ hm) hsne]
  exact ⟨hcol, hrel⟩

theorem colour_count_replace_fresh__scan_edge_transitions (cs vertices : List Int) (bit count v x : Int)
    (hv : 0 ≤ v ∧ v < Zlength cs) (hf : v ∉ vertices)
    (hr : ∀ z, z ∈ vertices → 0 ≤ z ∧ z < Zlength cs) (hc : ColourCount cs vertices bit count) :
    ColourCount (replace_Znth v x cs) vertices bit count := by
  have hm : vertices.map (fun z => Znth z (replace_Znth v x cs) 0) = vertices.map (fun z => Znth z cs 0) := by
    apply List.map_congr_left
    intro z hz
    exact Znth_replace_Znth_Diff 0 cs v z x hv (hr z hz) (by intro he; exact hf (he ▸ hz))
  unfold ColourCount at hc ⊢
  rwa [hm]

theorem scan_at_owned_advance_new__scan_edge_transitions (comments : List Comment) (ns cs : List Int)
    (u e v w x : Int) (he : 0 ≤ e ∧ e < 2 * Zlength comments)
    (hd : edge_dst comments e = v) (hw : edge_wt comments e = w)
    (hv : 0 ≤ v ∧ v < Zlength cs) (hu : 0 ≤ u ∧ u < Zlength cs)
    (hvm : Znth v cs 0 = -1) (hne : u ≠ v)
    (hdr : ∀ e0, (0 ≤ e0 ∧ e0 < 2 * Zlength comments) → 0 ≤ edge_dst comments e0 ∧ edge_dst comments e0 < Zlength cs)
    (hx : x = 0 ∨ x = 1) (hxe : x = Z.lxor (Znth u cs 0) w)
    (hc : ScanAtOwned comments ns cs u e) : ScanAtOwned comments ns (replace_Znth v x cs) u (Znth e ns 0) := by
  rcases hc with ⟨⟨remaining0, hchain0, hdone⟩, remaining, hchain, hsources⟩
  have hscan : ScanAt comments ns (replace_Znth v x cs) u (Znth e ns 0) := by
    cases hchain0 with
    | adj_end => omega
    | adj_cons e rest hp ht =>
      refine ⟨rest, ht, ?_⟩
      intro e0 he0 hs hn
      by_cases hh : e0 = e
      · subst e0
        rw [hd, hw, Znth_replace_Znth_Same 0 cs v x hv,
          Znth_replace_Znth_Diff 0 cs v u x hv hu (Ne.symm hne)]
        exact ⟨by omega, hxe⟩
      · have hnold : e0 ∉ e :: rest := by simpa only [List.mem_cons, not_or] using And.intro hh hn
        obtain ⟨hcol, hrel⟩ := hdone e0 he0 hs hnold
        have hdne : v ≠ edge_dst comments e0 := by intro heq; rw [← heq, hvm] at hcol; contradiction
        rw [Znth_replace_Znth_Diff 0 cs v (edge_dst comments e0) x hv (hdr e0 he0) hdne,
          Znth_replace_Znth_Diff 0 cs v u x hv hu (Ne.symm hne)]
        exact ⟨hcol, hrel⟩
  refine ⟨hscan, ?_⟩
  cases hchain with
  | adj_end => omega
  | adj_cons e rest hp ht => exact ⟨rest, ht, by intro e0 hm; exact hsources e0 (List.mem_cons_of_mem _ hm)⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
