import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_scan

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open AUXLib

theorem move_left_current_form__bubble_transition (l : List Int) (fr dst : Int)
    (hb : 0 < dst ∧ dst ≤ fr ∧ fr < Zlength l) :
    move_left l fr dst = sublist 0 (dst - 1) l ++ Znth (dst - 1) l 0 :: Znth fr l 0 ::
      (sublist dst fr l ++ sublist (fr + 1) (Zlength l) l) := by
  unfold move_left
  rw [sublist_split 0 dst (dst - 1) l ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  have hs := sublist_single 0 (dst - 1) l ⟨by omega, by omega⟩
  rw [show dst - 1 + 1 = dst by omega] at hs
  rw [hs]
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]

theorem move_left_previous_form__bubble_transition (l : List Int) (fr dst : Int)
    (hb : 0 < dst ∧ dst ≤ fr ∧ fr < Zlength l) :
    move_left l fr (dst - 1) = sublist 0 (dst - 1) l ++ Znth fr l 0 :: Znth (dst - 1) l 0 ::
      (sublist dst fr l ++ sublist (fr + 1) (Zlength l) l) := by
  unfold move_left
  rw [sublist_split (dst - 1) fr dst l ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  have hs := sublist_single 0 (dst - 1) l ⟨by omega, by omega⟩
  rw [show dst - 1 + 1 = dst by omega] at hs
  rw [hs]
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]

theorem adjacent_swap_prefix_standard__bubble_transition (p : List Int) (x y : Int) (s : List Int) :
    replace_Znth (Zlength p + 1) (Znth (Zlength p) (p ++ x :: y :: s) 0)
      (replace_Znth (Zlength p) (Znth (Zlength p + 1) (p ++ x :: y :: s) 0) (p ++ x :: y :: s)) =
    p ++ y :: x :: s := by
  rw [app_Znth2 0 p (x :: y :: s) _ le_rfl, app_Znth2 0 p (x :: y :: s) _ (by omega),
    sub_self, show Zlength p + 1 - Zlength p = 1 by omega]
  change replace_Znth (Zlength p + 1) x (replace_Znth (Zlength p) y (p ++ x :: y :: s)) = _
  exact replace_Znth_adjacent_form _ _ _ _

theorem move_left_step_standard__bubble_transition (l : List Int) (fr dst : Int)
    (hb : 0 < dst ∧ dst ≤ fr ∧ fr < Zlength l) :
    replace_Znth dst (Znth (dst - 1) (move_left l fr dst) 0)
      (replace_Znth (dst - 1) (Znth dst (move_left l fr dst) 0) (move_left l fr dst)) =
    move_left l fr (dst - 1) := by
  rw [move_left_current_form__bubble_transition _ _ _ hb,
    move_left_previous_form__bubble_transition _ _ _ hb]
  have hp : Zlength (sublist 0 (dst - 1) l) = dst - 1 := by
    simpa using p039_Zlength_sublist 0 (dst - 1) l ⟨by omega, by omega⟩ (by omega)
  have hh := adjacent_swap_prefix_standard__bubble_transition (sublist 0 (dst - 1) l)
    (Znth (dst - 1) l 0) (Znth fr l 0) (sublist dst fr l ++ sublist (fr + 1) (Zlength l) l)
  simpa only [hp, show dst - 1 + 1 = dst by omega] using hh

theorem adjacent_swap_prefix_reverse__bubble_transition (p : List Int) (x y : Int) (s : List Int) :
    replace_Znth (Zlength p) (Znth (Zlength p + 1) (p ++ x :: y :: s) 0)
      (replace_Znth (Zlength p + 1) (Znth (Zlength p) (p ++ x :: y :: s) 0) (p ++ x :: y :: s)) =
    p ++ y :: x :: s := by
  rw [app_Znth2 0 p (x :: y :: s) _ le_rfl, app_Znth2 0 p (x :: y :: s) _ (by omega),
    sub_self, show Zlength p + 1 - Zlength p = 1 by omega]
  change replace_Znth (Zlength p) y (replace_Znth (Zlength p + 1) x (p ++ x :: y :: s)) = _
  rw [replace_Znth_app_r _ _ p _ (by omega), replace_Znth_nothing _ p _ (by omega),
    show Zlength p + 1 - Zlength p = 1 by omega]
  change replace_Znth (Zlength p) y (p ++ x :: x :: s) = _
  rw [replace_Znth_app_r _ _ p _ le_rfl, replace_Znth_nothing _ p _ le_rfl, sub_self]
  rfl

theorem move_left_step_standard_reverse__bubble_transition (l : List Int) (fr dst : Int)
    (hb : 0 < dst ∧ dst ≤ fr ∧ fr < Zlength l) :
    replace_Znth (dst - 1) (Znth dst (move_left l fr dst) 0)
      (replace_Znth dst (Znth (dst - 1) (move_left l fr dst) 0) (move_left l fr dst)) =
    move_left l fr (dst - 1) := by
  rw [move_left_current_form__bubble_transition _ _ _ hb,
    move_left_previous_form__bubble_transition _ _ _ hb]
  have hp : Zlength (sublist 0 (dst - 1) l) = dst - 1 := by
    simpa using p039_Zlength_sublist 0 (dst - 1) l ⟨by omega, by omega⟩ (by omega)
  have hh := adjacent_swap_prefix_reverse__bubble_transition (sublist 0 (dst - 1) l)
    (Znth (dst - 1) l 0) (Znth fr l 0) (sublist dst fr l ++ sublist (fr + 1) (Zlength l) l)
  simpa only [hp, show dst - 1 + 1 = dst by omega] using hh

theorem replace_Znth_preserves_Zlength__bubble_transition {A : Type} (l : List A) (n : Int) (v : A) :
    Zlength (replace_Znth n v l) = Zlength l := Zlength_replace_Znth l n v

theorem p039_replace_Znth_app_l {A : Type} (n : Int) (a : A) (l1 l2 : List A)
    (hn : 0 ≤ n) (hl : n < Zlength l1) : replace_Znth n a (l1 ++ l2) = replace_Znth n a l1 ++ l2 :=
  ListLib.replace_Znth_app_l n a l1 l2 hn hl

theorem move_left_step_padded__bubble_transition (l : List Int) (fr dst : Int)
    (hb : 0 < dst ∧ dst ≤ fr ∧ fr < Zlength l) :
    replace_Znth (dst - 1) (Znth dst (move_left l fr dst ++ [0]) 0)
      (replace_Znth dst (Znth (dst - 1) (move_left l fr dst ++ [0]) 0) (move_left l fr dst ++ [0])) =
    move_left l fr (dst - 1) ++ [0] := by
  have hl := move_left_Zlength__bubble_transition l fr dst ⟨by omega, hb.2⟩
  rw [p039_app_Znth1 _ _ dst ⟨by omega, by omega⟩,
    p039_app_Znth1 _ _ (dst - 1) ⟨by omega, by omega⟩,
    p039_replace_Znth_app_l dst _ _ [0] (by omega) (by omega),
    p039_replace_Znth_app_l (dst - 1) _ _ [0] (by omega)
      (by rw [replace_Znth_preserves_Zlength__bubble_transition]; omega),
    move_left_step_standard_reverse__bubble_transition _ _ _ hb]

theorem adjacent_swap_move_left_step__bubble_transition (l : List Int) (fr dst : Int)
    (hb : 0 < dst ∧ dst ≤ fr ∧ fr < Zlength l) :
    AdjacentSwap (move_left l fr dst) (move_left l fr (dst - 1)) := by
  refine ⟨dst - 1, ⟨by omega, ?_⟩, ?_⟩
  · rw [move_left_Zlength__bubble_transition _ _ _ ⟨by omega, hb.2⟩]; omega
  · rw [show dst - 1 + 1 = dst by omega]
    exact (move_left_step_standard__bubble_transition _ _ _ hb).symm

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
