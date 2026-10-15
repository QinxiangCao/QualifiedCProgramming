import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_definitions

set_option linter.unusedVariables false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open AUXLib

theorem GreedyExchangeClosure_preserves_smaller (current : List Int) (pos remaining best : Int)
    (q : List Int) (hc : GreedyExchangeClosure current pos remaining best) (hq : LexLe q current) :
    LexLe q (move_left current best pos) := hc.1 q hq

theorem GreedyExchangeClosure_residual_path (current : List Int) (pos remaining best : Int)
    (q : List Int) (hc : GreedyExchangeClosure current pos remaining best)
    (hp : PrefixEq q current pos) (hr : SwapReach current q remaining) :
    LexLe q (move_left current best pos) ∨
      (PrefixEq q (move_left current best pos) (pos + 1) ∧
        SwapReach (move_left current best pos) q (remaining - (best - pos))) := hc.2 q hp hr

theorem GreedyExchangeClosure_preserves_progress (input : List Int) (budget : Int)
    (current : List Int) (pos remaining best : Int)
    (hm : ReachableFirstMaximum current pos remaining best)
    (hp : GreedyProgress input budget current pos remaining)
    (hc : GreedyExchangeClosure current pos remaining best)
    (hl : Zlength (move_left current best pos) = Zlength current)
    (hr : SwapReach input (move_left current best pos) (budget - (remaining - (best - pos)))) :
    GreedyProgress input budget (move_left current best pos) (pos + 1) (remaining - (best - pos)) := by
  rcases hm with ⟨hpos, hhi, hb, hmax, hfirst⟩
  rcases hp with ⟨hlen, hpos', hrem, hreach, hcomp⟩
  refine ⟨hl.trans hlen, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hr, ?_⟩
  intro q hq
  rcases hcomp q hq with hsmall | ⟨hprefix, hpath⟩
  · exact Or.inl (hc.1 q hsmall)
  · exact hc.2 q hprefix hpath

theorem GreedySelectionReady_specialize (current : List Int) (pos remaining best : Int)
    (hr : GreedySelectionReady current pos remaining)
    (hm : ReachableFirstMaximum current pos remaining best) :
    GreedyExchangeClosure current pos remaining best := hr best hm

theorem GreedySelectionReady_scan_stable (current : List Int) (pos remaining scanned best : Int)
    (hr : GreedySelectionReady current pos remaining)
    (hm : FirstMaximumPrefix current pos scanned best) :
    GreedySelectionReady current pos remaining := hr

theorem AdjacentSwapList_symmetric (left right : List Int) (hs : AdjacentSwapList left right) :
    AdjacentSwapList right left := by
  induction hs with
  | ASL_here x y tail => exact ASL_here y x tail
  | ASL_cons h left right hs ih => exact ASL_cons h right left ih

theorem FirstRemove_adjacent_transport (left right : List Int) (hs : AdjacentSwapList left right) :
    ∀ x p rest, FirstRemove x left p rest → ∃ p' rest', FirstRemove x right p' rest' ∧
      ((rest' = rest ∧ p' ≤ p + 1) ∨ (p' = p ∧ AdjacentSwapList rest rest')) := by
  induction hs with
  | ASL_here u v tail =>
    intro x p rest hr
    cases hr with
    | FirstRemove_here =>
      by_cases he : u = v
      · subst v
        exact ⟨0, u :: tail, FirstRemove_here _, Or.inl ⟨rfl, by omega⟩⟩
      · exact ⟨1, v :: tail, FirstRemove_later _ _ _ _ he (FirstRemove_here _),
          Or.inl ⟨rfl, by omega⟩⟩
    | FirstRemove_later y tail' p' rest' hxy ht =>
      cases ht with
      | FirstRemove_here =>
        exact ⟨0, u :: tail, FirstRemove_here _, Or.inl ⟨rfl, by omega⟩⟩
      | FirstRemove_later y' tail' p'' rest'' hxy' ht' =>
        exact ⟨p'' + 1 + 1, v :: u :: rest'',
          FirstRemove_later _ _ _ _ hxy' (FirstRemove_later _ _ _ _ hxy ht'),
          Or.inr ⟨rfl, ASL_here _ _ _⟩⟩
  | ASL_cons h left right hs ih =>
    intro x p rest hr
    cases hr with
    | FirstRemove_here =>
      exact ⟨0, right, FirstRemove_here _, Or.inr ⟨rfl, hs⟩⟩
    | FirstRemove_later y tail p rest hn ht =>
      obtain ⟨p', rest', hr', hh | hh⟩ := ih x p rest ht
      · rcases hh with ⟨he, hb⟩
        subst rest'
        exact ⟨p' + 1, h :: rest, FirstRemove_later _ _ _ _ hn hr',
          Or.inl ⟨rfl, by omega⟩⟩
      · rcases hh with ⟨he, hswap⟩
        subst p'
        exact ⟨p + 1, h :: rest', FirstRemove_later _ _ _ _ hn hr',
          Or.inr ⟨rfl, ASL_cons _ _ _ hswap⟩⟩

theorem CanonicalRemovalCost_refl (values : List Int) : CanonicalRemovalCost values values 0 := by
  induction values with
  | nil => exact ⟨rfl, rfl⟩
  | cons x tail ih => exact ⟨0, tail, 0, FirstRemove_here _, ih, rfl⟩

theorem CanonicalRemovalCost_adjacent_lipschitz (target : List Int) :
    ∀ left right cost, AdjacentSwapList left right → CanonicalRemovalCost left target cost →
      ∃ cost', CanonicalRemovalCost right target cost' ∧ cost' ≤ cost + 1 := by
  induction target with
  | nil =>
    intro left right cost hs hc
    rcases hc with ⟨rfl, hcost⟩
    cases hs
  | cons x target_tail ih =>
    intro left right cost hs hc
    rcases hc with ⟨p, rest, tail_cost, hr, ht, he⟩
    obtain ⟨p', rest', hr', hh | hh⟩ := FirstRemove_adjacent_transport left right hs x p rest hr
    · rcases hh with ⟨he', hb⟩
      subst rest'
      exact ⟨p' + tail_cost, ⟨p', rest, tail_cost, hr', ht, rfl⟩, by omega⟩
    · rcases hh with ⟨he', hs'⟩
      subst p'
      obtain ⟨cost', hc', hb⟩ := ih rest rest' tail_cost hs' ht
      exact ⟨p + cost', ⟨p, rest', cost', hr', hc', rfl⟩, by omega⟩

theorem AdjacentSwapList_context (pref : List Int) (x y : Int) (suffix : List Int) :
    AdjacentSwapList (pref ++ x :: y :: suffix) (pref ++ y :: x :: suffix) := by
  induction pref with
  | nil => exact ASL_here _ _ _
  | cons h pref ih => exact ASL_cons _ _ _ ih

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
