import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_scan_extend

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem component_scan_done__scan_and_component_closure (n : Int) (comments : List Comment)
    (ns before after finished pending : List Int) (u c0 c1 : Int)
    (hh : ComponentScanStrong n comments ns before after finished pending u (-1) c0 c1) :
    ComponentFrontierStrong n comments before after (finished ++ [u]) pending c0 c1 := by
  rcases hh with ⟨⟨hcv, hn, ht, hf, hs, h0, h1⟩, ho, hl⟩
  have shape : (finished ++ [u]) ++ pending = finished ++ u :: pending := by simp
  refine ⟨⟨hcv, ?_, ?_, ?_, h0, h1⟩, ?_⟩
  · rwa [shape]
  · rwa [shape]
  · intro e he hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hf e he hm
    · have heu : edge_src comments e = u := by simpa using hm
      obtain ⟨remaining, hc, hd⟩ := hs
      have hempty : remaining = [] := by cases hc with
        | adj_end => rfl
        | adj_cons e rest hp ht => omega
      simpa only [heu] using hd e he heu (by simp [hempty])
  · rwa [shape]

theorem new_component_edge_closed__scan_and_component_closure (n : Int) (comments : List Comment)
    (before after vertices : List Int) (i u v w : Int) (hn : NewColourSet n before after vertices)
    (hb : ColouredClosed comments before) (ha : ColouredClosed comments after)
    (hi : 0 ≤ i ∧ i < Zlength comments) (hq : comment_at comments i = ((u, v), w))
    (hu : 1 ≤ u ∧ u ≤ n) (hv : 1 ≤ v ∧ v ≤ n) : u ∈ vertices ↔ v ∈ vertices := by
  have hbc := hb i hi
  have hac := ha i hi
  rw [hq] at hbc hac
  change (Znth u before 0 ≠ -1 ↔ Znth v before 0 ≠ -1) at hbc
  change (Znth u after 0 ≠ -1 ↔ Znth v after 0 ≠ -1) at hac
  rw [hn.2.2.1 u hu, hn.2.2.1 v hv]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨by by_contra hh; exact hbc.mpr hh h0, hac.mp h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by by_contra hh; exact hbc.mp hh h0, hac.mpr h1⟩

theorem comment_bounds_from_forward_star__scan_and_component_closure (n cap : Int) (comments : List Comment)
    (hs ns ts ws : List Int) (hcap : cap = Zlength comments)
    (hf : ForwardStar n cap cap hs ns ts ws comments) (hr : ForwardStarRanges n cap hs ns ts ws)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength comments) :
    let ((u, v), _) := comment_at comments i; (1 ≤ u ∧ u ≤ n) ∧ (1 ≤ v ∧ v ≤ n) := by
  rcases hq : comment_at comments i with ⟨⟨u,v⟩,w⟩
  obtain ⟨hf0, hf1, hf2⟩ := edge_forward__scan_and_component_closure comments i u v w hq
  obtain ⟨hr0, hr1, hr2⟩ := edge_reverse__scan_and_component_closure comments i u v w hq
  have hif : 0 ≤ 2 * i ∧ 2 * i < 2 * cap := by omega
  have hir : 0 ≤ 2 * i + 1 ∧ 2 * i + 1 < 2 * cap := by omega
  have huf := (hr.2 (2*i) hif).2.1
  have hur := (hr.2 (2*i+1) hir).2.1
  rw [(hf.2.2.2.2.2.2.1 _ hif).1, hf1] at huf
  rw [(hf.2.2.2.2.2.2.1 _ hir).1, hr1] at hur
  exact ⟨hur, huf⟩

theorem frontier_respected_closed__scan_and_component_closure (n cap : Int) (comments : List Comment)
    (hs ns ts ws before after vertices : List Int) (hcap : cap = Zlength comments)
    (hf : ForwardStar n cap cap hs ns ts ws comments) (hr : ForwardStarRanges n cap hs ns ts ws)
    (hp : ParityRespected comments before) (hc : ColouredClosed comments before)
    (hn : NewColourSet n before after vertices) (hscan : FullyScanned comments after vertices) :
    ParityRespected comments after ∧ ColouredClosed comments after := by
  have hbounds := comment_bounds_from_forward_star__scan_and_component_closure n cap comments hs ns ts ws hcap hf hr
  have hsame (v : Int) (hv : 1 ≤ v ∧ v ≤ n) (hb : Znth v before 0 ≠ -1) : Znth v after 0 = Znth v before 0 :=
    hn.2.2.2 v hv (fun hm => hb ((hn.2.2.1 v hv).mp hm).1)
  constructor
  · intro i hi
    rcases hq : comment_at comments i with ⟨⟨u,v⟩,w⟩
    dsimp
    intro hua hva
    have hb := hbounds i hi
    rw [hq] at hb
    obtain ⟨hu,hv⟩ := hb
    by_cases hub : Znth u before 0 = -1
    · have hum := (hn.2.2.1 u hu).mpr ⟨hub,hua⟩
      obtain ⟨hsrc,hdst,hwt⟩ := edge_forward__scan_and_component_closure comments i u v w hq
      have hdone := hscan (2*i) ⟨by omega,by omega⟩ (by rwa [hsrc])
      simpa only [hsrc,hdst,hwt] using hdone.2
    · have hclosed := hc i hi
      rw [hq] at hclosed
      have hvb := hclosed.mp hub
      rw [hsame u hu hub,hsame v hv hvb]
      have hpar := hp i hi
      rw [hq] at hpar
      exact hpar hub hvb
  · intro i hi
    rcases hq : comment_at comments i with ⟨⟨u,v⟩,w⟩
    dsimp
    have hb := hbounds i hi
    rw [hq] at hb
    obtain ⟨hu,hv⟩ := hb
    have hclosed := hc i hi
    rw [hq] at hclosed
    constructor
    · intro hua
      by_cases hub : Znth u before 0 = -1
      · have hum := (hn.2.2.1 u hu).mpr ⟨hub,hua⟩
        obtain ⟨hsrc,hdst,hwt⟩ := edge_forward__scan_and_component_closure comments i u v w hq
        have hdone := hscan (2*i) ⟨by omega,by omega⟩ (by rwa [hsrc])
        simpa only [hdst] using hdone.1
      · have hvb := hclosed.mp hub
        rwa [hsame v hv hvb]
    · intro hva
      by_cases hvb : Znth v before 0 = -1
      · have hvm := (hn.2.2.1 v hv).mpr ⟨hvb,hva⟩
        obtain ⟨hsrc,hdst,hwt⟩ := edge_reverse__scan_and_component_closure comments i u v w hq
        have hdone := hscan (2*i+1) ⟨by omega,by omega⟩ (by rwa [hsrc])
        simpa only [hdst] using hdone.1
      · have hub := hclosed.mpr hvb
        rwa [hsame u hu hub]

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
