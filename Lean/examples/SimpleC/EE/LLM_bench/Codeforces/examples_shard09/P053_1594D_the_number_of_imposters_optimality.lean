import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_consistency

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem component_max_lift__scan_and_component_closure (n : Int) (comments : List Comment)
    (before after vertices : List Int) (c0 c1 : Int)
    (hb : ∀ i, (0 ≤ i ∧ i < Zlength comments) → let ((u,v),_) := comment_at comments i; (1 ≤ u ∧ u ≤ n) ∧ (1 ≤ v ∧ v ≤ n))
    (hn : NewColourSet n before after vertices) (hcb : ColouredClosed comments before)
    (hca : ColouredClosed comments after) (hp : ParityRespected comments after) (hcv : ColourValues n after)
    (h0 : ColourCount after vertices 0 c0) (h1 : ColourCount after vertices 1 c1)
    (hl : ComponentTwoChoicesLocal n comments after vertices)
    (t : Int) (hmax : MaxImpostersOn n comments before t) : MaxImpostersOn n comments after (t + max c0 c1) := by
  have hchoose : ∃ flip : Int, (flip = 0 ∨ flip = 1) ∧ (if flip = 0 then c1 else c0) = max c0 c1 := by
    by_cases hh : c0 ≤ c1
    · exact ⟨0,Or.inl rfl,by simp [max_eq_right hh]⟩
    · exact ⟨1,Or.inr rfl,by simp [max_eq_left (by omega : c1 ≤ c0)]⟩
  obtain ⟨flip,hf,hchoice⟩ := hchoose
  rcases hmax with ⟨best,⟨⟨best_roles,hbest,hbest_sum⟩,hupper⟩,hbest_val⟩
  change best = t at hbest_val
  have hvb := Forall.iff_forall_mem.mp hn.2.1
  have hz : ∀ v, v ∈ vertices → Znth (v-1) best_roles 0 = 0 := by
    intro v hv
    exact hbest.1.2.2 v (hvb v hv) ((hn.2.2.1 v (hvb v hv)).mp hv).1
  have hcol : ∀ v, v ∈ vertices → Znth v after 0 ≠ -1 := fun v hv => ((hn.2.2.1 v (hvb v hv)).mp hv).2
  refine ⟨t + max c0 c1,⟨?_,?_⟩,rfl⟩
  · refine ⟨vertices.foldr (fun v r => replace_Znth (v-1) (Z.lxor (Znth v after 0) flip) r) best_roles,?_,?_⟩
    · exact extend_consistent__scan_and_component_closure _ _ _ _ _ _ _ hb hn hcb hca hp hcv hbest hf
    · rw [fold_replace_sum__scan_and_component_closure _ _ _ _ hbest.1.1 hn.1 hn.2.1 hz,
        component_bit_sum__scan_and_component_closure _ _ _ _ _ _ hcv hn.2.1 hcol h0 h1 hf,hchoice]
      omega
  · intro candidate hh
    obtain ⟨roles,hr,hcandidate⟩ := hh
    have hrestrict := restrict_consistent__scan_and_component_closure _ _ _ _ _ _ hb hn hr
    obtain ⟨rflip,hrflip,hcomponent⟩ := component_roles_sum__scan_and_component_closure _ _ _ _ _ _ _ _ hn hcv h0 h1 hl hr
    have hsum := fold_replace_sum_general__scan_and_component_closure vertices n roles (fun _ => 0) hr.1.1 hn.1 hn.2.1
    rw [sum_map_zero__scan_and_component_closure,hcomponent] at hsum
    dsimp only at hsum
    have hru := hupper _ ⟨_,hrestrict,rfl⟩
    change (vertices.foldr (fun v r => replace_Znth (v-1) 0 r) roles).foldr (·+·) 0 ≤ best at hru
    have hbound : (if rflip = 0 then c1 else c0) ≤ max c0 c1 := by
      split
      · exact le_max_right _ _
      · exact le_max_left _ _
    change candidate ≤ t + max c0 c1
    omega

theorem component_frontier_complete__scan_and_component_closure (n cap : Int) (comments : List Comment)
    (hs ns ts ws before after vertices : List Int) (c0 c1 : Int) (hcap : cap = Zlength comments)
    (hstar : ForwardStar n cap cap hs ns ts ws comments) (hr : ForwardStarRanges n cap hs ns ts ws)
    (hp : ParityRespected comments before) (hc : ColouredClosed comments before)
    (hfront : ComponentFrontierStrong n comments before after vertices [] c0 c1) :
    ComponentCompleteStrong n comments before after vertices c0 c1 := by
  obtain ⟨hf,hl⟩ := hfront
  obtain ⟨hcv,hn,hg,hs,h0,h1⟩ := hf
  simp only [List.append_nil] at hn hg hl
  obtain ⟨hpa,hca⟩ := frontier_respected_closed__scan_and_component_closure _ _ _ _ _ _ _ _ _ _ hcap hstar hr hp hc hn hs
  refine ⟨⟨?_,hpa,hca,?_⟩,hl⟩
  · unfold ComponentFrontier
    simpa only [List.append_nil] using And.intro hcv ⟨hn,hg,hs,h0,h1⟩
  · exact component_max_lift__scan_and_component_closure _ _ _ _ _ _ _
      (comment_bounds_from_forward_star__scan_and_component_closure _ _ _ _ _ _ _ hcap hstar hr)
      hn hc hca hpa hcv h0 h1 hl

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
