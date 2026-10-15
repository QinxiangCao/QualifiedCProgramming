import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_exchange

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open AUXLib

theorem first_maximum_prefix_singleton__selection_scan (l : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : FirstMaximumPrefix l i (i + 1) i := by
  refine ⟨⟨hi.1, by omega⟩, by omega, ⟨le_rfl, by omega⟩, ?_, ?_⟩
  · intro p hp
    have he : p = i := by omega
    rw [he]
  · intro p hp; omega

theorem first_maximum_prefix_extend_strict__selection_scan (l : List Int) (lo hi best : Int)
    (hm : FirstMaximumPrefix l lo hi best) (hh : hi < Zlength l)
    (hs : Znth best l 0 < Znth hi l 0) : FirstMaximumPrefix l lo (hi + 1) hi := by
  rcases hm with ⟨hlo, hhi, hb, hmax, hfirst⟩
  refine ⟨⟨hlo.1, by omega⟩, by omega, ⟨by omega, by omega⟩, ?_, ?_⟩
  · intro p hp
    by_cases he : p < hi
    · have := hmax p ⟨hp.1, he⟩; omega
    · have he' : p = hi := by omega
      rw [he']
  · intro p hp; have := hmax p hp; omega

theorem first_maximum_prefix_extend_nonstrict__selection_scan (l : List Int) (lo hi best : Int)
    (hm : FirstMaximumPrefix l lo hi best) (hh : hi < Zlength l)
    (hs : Znth hi l 0 ≤ Znth best l 0) : FirstMaximumPrefix l lo (hi + 1) best := by
  rcases hm with ⟨hlo, hhi, hb, hmax, hfirst⟩
  refine ⟨⟨hlo.1, by omega⟩, by omega, ⟨hb.1, by omega⟩, ?_, hfirst⟩
  intro p hp
  by_cases he : p < hi
  · exact hmax p ⟨hp.1, he⟩
  · have he' : p = hi := by omega
    rwa [he']

theorem first_maximum_prefix_extend_strict_app_zero__selection_scan (l : List Int) (lo hi best : Int)
    (hm : FirstMaximumPrefix l lo hi best) (hh : hi < Zlength l)
    (hs : Znth best (l ++ [0]) 0 < Znth hi (l ++ [0]) 0) : FirstMaximumPrefix l lo (hi + 1) hi := by
  apply first_maximum_prefix_extend_strict__selection_scan l lo hi best hm hh
  rcases hm with ⟨hlo, hhi, hb, hmax, hfirst⟩
  rwa [p039_app_Znth1 l [0] best ⟨by omega, by omega⟩,
    p039_app_Znth1 l [0] hi ⟨by omega, hh⟩] at hs

theorem first_maximum_prefix_extend_nonstrict_app_zero__selection_scan (l : List Int) (lo hi best : Int)
    (hm : FirstMaximumPrefix l lo hi best) (hh : hi < Zlength l)
    (hs : Znth hi (l ++ [0]) 0 ≤ Znth best (l ++ [0]) 0) : FirstMaximumPrefix l lo (hi + 1) best := by
  apply first_maximum_prefix_extend_nonstrict__selection_scan l lo hi best hm hh
  rcases hm with ⟨hlo, hhi, hb, hmax, hfirst⟩
  rwa [p039_app_Znth1 l [0] best ⟨by omega, by omega⟩,
    p039_app_Znth1 l [0] hi ⟨by omega, hh⟩] at hs

theorem move_left_same__selection_exchange (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    move_left l i i = l := by
  unfold move_left
  rw [Zsublist_nil l i i (by omega), List.append_nil,
    ← sublist_single 0 i l hi, ← sublist_split 0 (i + 1) i l ⟨by omega, hi.1⟩ ⟨by omega, by omega⟩,
    ← sublist_split 0 (Zlength l) (i + 1) l ⟨by omega, by omega⟩ ⟨by omega, le_rfl⟩,
    sublist_self l _ rfl]

theorem move_left_same__bubble_transition (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    move_left l i i = l := move_left_same__selection_exchange _ _ hi

theorem p039_decompose_move (l : List Int) (fr dst : Int) (hb : 0 ≤ dst ∧ dst ≤ fr ∧ fr < Zlength l) :
    l = sublist 0 dst l ++ sublist dst fr l ++ [Znth fr l 0] ++ sublist (fr + 1) (Zlength l) l := by
  rw [← sublist_single 0 fr l ⟨by omega, hb.2.2⟩,
    ← sublist_split 0 fr dst l ⟨by omega, hb.1⟩ ⟨hb.2.1, by omega⟩,
    ← sublist_split 0 (fr + 1) fr l ⟨by omega, by omega⟩ ⟨by omega, by omega⟩,
    ← sublist_split 0 (Zlength l) (fr + 1) l ⟨by omega, by omega⟩ ⟨by omega, le_rfl⟩,
    sublist_self l _ rfl]

theorem move_left_permutation__bubble_transition (l : List Int) (fr dst : Int)
    (hb : 0 ≤ dst ∧ dst ≤ fr ∧ fr < Zlength l) : Permutation l (move_left l fr dst) := by
  have hd := p039_decompose_move l fr dst hb
  conv_lhs => rw [hd]
  unfold move_left
  have hh := (List.perm_append_comm : (sublist dst fr l ++ [Znth fr l 0]).Perm ([Znth fr l 0] ++ sublist dst fr l))
  simpa only [List.append_assoc] using (hh.append_right (sublist (fr + 1) (Zlength l) l)).append_left (sublist 0 dst l)

theorem move_left_Zlength__bubble_transition (l : List Int) (fr dst : Int)
    (hb : 0 ≤ dst ∧ dst ≤ fr ∧ fr < Zlength l) : Zlength (move_left l fr dst) = Zlength l := by
  have hl := (move_left_permutation__bubble_transition _ _ _ hb).length_eq
  simp only [Zlength, hl, Int.ofNat_eq_coe]

theorem move_left_preserves_range__bubble_transition (l : List Int) (fr dst : Int)
    (hb : 0 ≤ dst ∧ dst ≤ fr ∧ fr < Zlength l)
    (hr : ∀ p, (0 ≤ p ∧ p < Zlength l) → 48 ≤ Znth p l 0 ∧ Znth p l 0 ≤ 57) :
    ∀ p, (0 ≤ p ∧ p < Zlength l) → 48 ≤ Znth p (move_left l fr dst) 0 ∧ Znth p (move_left l fr dst) 0 ≤ 57 := by
  have hp := move_left_permutation__bubble_transition _ _ _ hb
  have hf : ∀ y ∈ l, 48 ≤ y ∧ y ≤ 57 := by
    intro y hy
    obtain ⟨n, hn, he⟩ := List.getElem_of_mem hy
    have hv : Znth (n : Int) l 0 = y := by simp [Znth, List.getD, List.getElem?_eq_getElem hn, he]
    have hh := hr n ⟨by omega, by simp only [Zlength, Int.ofNat_eq_coe]; omega⟩
    rwa [hv] at hh
  intro p hpos
  have hn : p.toNat < (move_left l fr dst).length := by
    have hl := hp.length_eq
    simp only [Zlength, Int.ofNat_eq_coe] at hpos; omega
  have hm : Znth p (move_left l fr dst) 0 ∈ move_left l fr dst := by
    simp only [Znth, List.getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem hn
  exact hf _ (hp.mem_iff.mpr hm)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
