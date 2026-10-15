import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_frontier_pop

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem p053_closed_edge (comments : List Comment) (cs : List Int) (e : Int)
    (he : 0 ≤ e ∧ e < 2 * Zlength comments) (hc : ColouredClosed comments cs) :
    Znth (edge_src comments e) cs 0 ≠ -1 ↔ Znth (edge_dst comments e) cs 0 ≠ -1 := by
  have hh := hc (Z.div e 2) (p053_edge_index_range comments e he)
  unfold edge_src edge_dst
  rcases hq : comment_at comments (Z.div e 2) with ⟨⟨a, b⟩, w⟩
  rw [hq] at hh
  cases hv : Z.even e <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact hh.symm
  · exact hh

private theorem p053_xor_flip_cancel (a b w f : Int)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hw : w = 0 ∨ w = 1) (hf : f = 0 ∨ f = 1)
    (he : Z.lxor b f = Z.lxor (Z.lxor a f) w) : b = Z.lxor a w := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hw with rfl | rfl <;>
    rcases hf with rfl | rfl <;> first | rfl |
      (norm_num only [show Z.lxor 0 0 = 0 by rfl, show Z.lxor 0 1 = 1 by rfl,
        show Z.lxor 1 0 = 1 by rfl, show Z.lxor 1 1 = 0 by rfl] at he)

theorem scan_conflict_spec__scan_conflict (n m : Int) (comments : List Comment)
    (hs ns ts ws before cs finished pending : List Int) (u e c0 c1 : Int)
    (hm : m = Zlength comments) (he : 0 ≤ e ∧ e < 2 * m)
    (hd : 1 ≤ Znth e ts 0 ∧ Znth e ts 0 ≤ n) (hw : Znth e ws 0 = 0 ∨ Znth e ws 0 = 1)
    (hcol : Znth (Znth e ts 0) cs 0 ≥ 0)
    (hconflict : Znth (Znth e ts 0) cs 0 ≠ Z.lxor (Znth u cs 0) (Znth e ws 0))
    (hclosed : ColouredClosed comments before)
    (hstrong : ComponentScanStrong n comments ns before cs finished pending u e c0 c1)
    (hstar : ForwardStar n m m hs ns ts ws comments) : Spec n comments (-1) := by
  rcases hstrong with ⟨⟨hcv, hnew, htwo, hfully, hscan, hc0, hc1⟩, ⟨hscan', remaining, hchain, hsource⟩, hlocal⟩
  have hem : e ∈ remaining := by
    cases hchain with
    | adj_end => omega
    | adj_cons e rest hpos ht => simp
  have hsrc := hsource e hem
  have hedge := hstar.2.2.2.2.2.2.1 e he
  rcases hedge with ⟨hdst, hwt⟩
  have hu : u ∈ finished ++ u :: pending := by simp
  have hub := Forall.iff_forall_mem.mp hnew.2.1 u hu
  obtain ⟨hbeforeu, hcsu⟩ := (hnew.2.2.1 u hub).mp hu
  have herange : 0 ≤ e ∧ e < 2 * Zlength comments := by omega
  have hc := p053_closed_edge comments before e herange hclosed
  rw [hsrc, ← hdst] at hc
  have hbeforev : Znth (Znth e ts 0) before 0 = -1 := by
    by_contra hv
    exact hc.mpr hv hbeforeu
  have hcsb : Znth (Znth e ts 0) cs 0 ≠ -1 := by omega
  have hv : Znth e ts 0 ∈ finished ++ u :: pending := (hnew.2.2.1 _ hd).mpr ⟨hbeforev, hcsb⟩
  left
  refine ⟨rfl, ?_⟩
  rintro ⟨roles, hroles⟩
  obtain ⟨flip, hflip, hchoice⟩ := htwo roles hroles
  have hchoiceu := hchoice u hu
  have hchoicev := hchoice (Znth e ts 0) hv
  have hroleedge := roles_consistent_edge__scan_edge_transitions n comments roles e herange
    (by rwa [hsrc]) (by rwa [← hdst]) (by rwa [← hwt]) hroles
  rw [hsrc, ← hdst, ← hwt, hchoiceu, hchoicev] at hroleedge
  have hubit : Znth u cs 0 = 0 ∨ Znth u cs 0 = 1 := by have := hcv.2 u hub; omega
  have hvbit : Znth (Znth e ts 0) cs 0 = 0 ∨ Znth (Znth e ts 0) cs 0 = 1 := by
    have := hcv.2 _ hd; omega
  exact hconflict (p053_xor_flip_cancel _ _ _ _ hubit hvbit hw hflip hroleedge)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
