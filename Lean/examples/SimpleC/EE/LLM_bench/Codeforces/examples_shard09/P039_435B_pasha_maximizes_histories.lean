import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_bubble

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open AUXLib

private theorem p039_app_nth {A : Type} (d : A) (pref tail : List A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength pref) : Znth i (pref ++ tail) d = Znth i pref d :=
  ListLib.app_Znth1 d pref tail i hi

theorem extend_swap_history_first__bubble_transition (h : List (List Int)) (b : List Int)
    (hn : h ≠ []) : Znth 0 (h ++ [b]) [] = Znth 0 h [] := by
  cases h with
  | nil => contradiction
  | cons x tail => rfl

theorem extend_swap_history_last__bubble_transition (h : List (List Int)) (b : List Int) :
    Znth (Zlength (h ++ [b]) - 1) (h ++ [b]) [] = b := by
  rw [Zlength_app, Zlength_cons, Zlength_nil,
    show Zlength h + (0 + 1) - 1 = Zlength h by omega,
    app_Znth2 [] h [b] _ le_rfl, sub_self]
  rfl

theorem extend_swap_history_steps__bubble_transition (h : List (List Int)) (b : List Int)
    (hn : h ≠ [])
    (hs : ∀ i, (0 ≤ i ∧ i < Zlength h - 1) → AdjacentSwap (Znth i h []) (Znth (i + 1) h []))
    (ht : AdjacentSwap (Znth (Zlength h - 1) h []) b) :
    ∀ i, (0 ≤ i ∧ i < Zlength (h ++ [b]) - 1) →
      AdjacentSwap (Znth i (h ++ [b]) []) (Znth (i + 1) (h ++ [b]) []) := by
  intro i hi
  simp only [Zlength_app, Zlength_cons, Zlength_nil] at hi
  by_cases hold : i < Zlength h - 1
  · rw [p039_app_nth [] h [b] i ⟨hi.1, by omega⟩,
      p039_app_nth [] h [b] (i + 1) ⟨by omega, by omega⟩]
    exact hs i ⟨hi.1, hold⟩
  · have he : i = Zlength h - 1 := by omega
    have hh : 1 ≤ Zlength h := by
      cases h with
      | nil => contradiction
      | cons x tail => simp only [Zlength_cons]; have := Zlength_nonneg tail; omega
    rw [he, p039_app_nth [] h [b] (Zlength h - 1) ⟨by omega, by omega⟩,
      show Zlength h - 1 + 1 = Zlength h by omega,
      app_Znth2 [] h [b] _ le_rfl, sub_self]
    exact ht

theorem swap_reach_extend__bubble_transition (a b c : List Int) (k : Int)
    (hr : SwapReach a b k) (hs : AdjacentSwap b c) : SwapReach a c (k + 1) := by
  rcases hr with ⟨h, hb, hf, ht, hsteps⟩
  have hn : h ≠ [] := by intro he; subst h; simp only [Zlength_nil] at hb; omega
  refine ⟨h ++ [c], ⟨?_, ?_⟩, ?_, extend_swap_history_last__bubble_transition h c, ?_⟩
  · simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega
  · simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega
  · rw [extend_swap_history_first__bubble_transition h c hn]; exact hf
  · apply extend_swap_history_steps__bubble_transition h c hn hsteps
    rwa [ht]

theorem swap_reach_move_left_after__bubble_transition (input l : List Int) (k fr dst : Int)
    (hb : 0 ≤ dst ∧ dst ≤ fr ∧ fr < Zlength l) (hr : SwapReach input l k) :
    SwapReach input (move_left l fr dst) (k + (fr - dst)) := by
  generalize hn : (fr - dst).toNat = n
  induction n generalizing dst with
  | zero =>
    have he : dst = fr := by omega
    subst dst
    rw [move_left_same__bubble_transition _ _ ⟨by omega, hb.2.2⟩, sub_self, add_zero]
    exact hr
  | succ n ih =>
    have hi := ih (dst + 1) ⟨by omega, by omega, hb.2.2⟩ (by omega)
    have hs := adjacent_swap_move_left_step__bubble_transition l fr (dst + 1) ⟨by omega, by omega, hb.2.2⟩
    rw [show dst + 1 - 1 = dst by omega] at hs
    have hh := swap_reach_extend__bubble_transition _ _ _ _ hi hs
    simpa only [show k + (fr - (dst + 1)) + 1 = k + (fr - dst) by omega] using hh

theorem greedy_progress_terminal_spec__final_result (input : List Int) (budget : Int)
    (current : List Int) (pos remaining : Int)
    (hp : GreedyProgress input budget current pos remaining)
    (ht : pos = Zlength input ∨ remaining = 0) : Spec input budget current := by
  rcases hp with ⟨hcl, hpos, hrem, hr, hmax⟩
  refine ⟨SwapReach_monotone _ _ _ _ hr (by omega), ?_⟩
  intro q hq
  rcases hmax q hq with hlex | ⟨hprefix, hpath⟩
  · exact hlex
  · left
    rcases ht with hposfull | hzero
    · rcases hprefix with ⟨hlen, hp, heq⟩
      apply (ListLib.list_eq_ext q current 0).mpr
      simp only [ListLib.Zlength, ListLib.Znth]
      exact ⟨hlen, by intro j hj; exact heq j ⟨hj.1, by omega⟩⟩
    · rcases hpath with ⟨states, hlen, hf, hl, hs⟩
      have he : Zlength states - 1 = 0 := by omega
      rw [he] at hl
      exact hl.symm.trans hf

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
