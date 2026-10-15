import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_removal_cost
import ListLib.Base.Positional

set_option linter.unusedVariables false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open AUXLib

theorem replace_Znth_adjacent_form (pref : List Int) (x y : Int) (suffix : List Int) :
    replace_Znth (Zlength pref + 1) x
      (replace_Znth (Zlength pref) y (pref ++ x :: y :: suffix)) = pref ++ y :: x :: suffix := by
  rw [replace_Znth_app_r _ _ pref _ (by omega), replace_Znth_nothing _ pref _ (by omega)]
  simp only [sub_self]
  change replace_Znth (Zlength pref + 1) x (pref ++ y :: y :: suffix) = _
  rw [replace_Znth_app_r _ _ pref _ (by omega), replace_Znth_nothing _ pref _ (by omega)]
  have he : Zlength pref + 1 - Zlength pref = 1 := by omega
  rw [he]
  rfl

private theorem p039_split_two (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i + 1 < Zlength l) :
    ∃ pref suffix, Zlength pref = i ∧ l = pref ++ Znth i l 0 :: Znth (i + 1) l 0 :: suffix := by
  have hnat : i.toNat + 1 < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  refine ⟨l.take i.toNat, l.drop (i.toNat + 2), ?_, ?_⟩
  · simp only [Zlength, List.length_take, Int.ofNat_eq_coe, Nat.min_eq_left (by omega : i.toNat ≤ l.length)]
    omega
  · have hs := ListLib.firstn_skipSn 0 i.toNat l (by omega)
    have hs' := ListLib.firstn_skipSn 0 0 (l.drop (i.toNat + 1)) (by simp only [List.length_drop]; omega)
    simp only [ListLib.firstn, ListLib.skipn, ListLib.nth, firstn, skipn, nth, List.take_zero, List.nil_append,
      List.drop_drop] at hs'
    simp only [ListLib.firstn, ListLib.skipn, ListLib.nth, firstn, skipn, nth] at hs
    rw [hs'] at hs
    simpa only [Znth, List.getD, List.getElem?_drop, Nat.add_zero,
      show (i + 1).toNat = i.toNat + 1 by omega] using hs

theorem AdjacentSwap_to_AdjacentSwapList (left right : List Int) (hs : AdjacentSwap left right) :
    AdjacentSwapList left right := by
  rcases hs with ⟨i, hi, rfl⟩
  obtain ⟨pref, suffix, hp, he⟩ := p039_split_two left i ⟨hi.1, by omega⟩
  have hr : replace_Znth (i + 1) (Znth i left 0)
      (replace_Znth i (Znth (i + 1) left 0) left) =
      pref ++ Znth (i + 1) left 0 :: Znth i left 0 :: suffix := by
    conv_lhs => arg 3; arg 3; rw [he]
    rw [← hp, replace_Znth_adjacent_form]
  rw [hr]
  conv_lhs => rw [he]
  exact AdjacentSwapList_context _ _ _ _

theorem AdjacentSwapChain_canonical_cost (states : List (List Int)) (hc : AdjacentSwapChain states) :
    ∃ cost, CanonicalRemovalCost (states.headD []) (states.getLastD []) cost ∧ cost ≤ states.length - 1 := by
  induction hc with
  | ASC_one state => exact ⟨0, CanonicalRemovalCost_refl _, by simp⟩
  | ASC_cons left right tail hs hc ih =>
    obtain ⟨cost, hcost, hb⟩ := ih
    have hrs := AdjacentSwapList_symmetric _ _ (AdjacentSwap_to_AdjacentSwapList _ _ hs)
    obtain ⟨cost', hc', hb'⟩ := CanonicalRemovalCost_adjacent_lipschitz
      ((right :: tail).getLastD []) right left cost hrs hcost
    exact ⟨cost', by simpa using hc', by simp only [List.length_cons] at hb ⊢; omega⟩

theorem indexed_adjacent_steps_form_chain (states : List (List Int)) :
    1 ≤ Zlength states →
    (∀ i, (0 ≤ i ∧ i < Zlength states - 1) → AdjacentSwap (Znth i states []) (Znth (i + 1) states [])) →
    AdjacentSwapChain states := by
  induction states with
  | nil => intro hl hs; simp only [Zlength_nil] at hl; omega
  | cons a states ih =>
    intro hl hs
    cases states with
    | nil => exact ASC_one a
    | cons b tail =>
      apply ASC_cons a b tail
      · have hh := hs 0 (by simp only [Zlength_cons]; have := Zlength_nonneg tail; omega)
        simpa [Znth] using hh
      · apply ih (by simp only [Zlength_cons]; have := Zlength_nonneg tail; omega)
        intro i hi
        have hh := hs (i + 1) (by simp only [Zlength_cons] at hi ⊢; omega)
        rw [Znth_cons [] (i + 1) a (b :: tail) (by omega),
          Znth_cons [] (i + 1 + 1) a (b :: tail) (by omega)] at hh
        simpa only [show i + 1 - 1 = i by omega, show i + 1 + 1 - 1 = i + 1 by omega] using hh

theorem nth_last_default_local {A : Type} (values : List A) (i : Nat) (d : A)
    (hn : values ≠ []) (hi : i = values.length - 1) : values.getD i d = values.getLastD d := by
  subst i
  induction values with
  | nil => contradiction
  | cons x tail ih =>
    cases tail with
    | nil => rfl
    | cons y tail =>
      simpa using ih (by simp)

theorem SwapReach_canonical_lower_bound (source target : List Int) (budget : Int)
    (hr : SwapReach source target budget) :
    ∃ cost, CanonicalRemovalCost source target cost ∧ (cost : Int) ≤ budget := by
  rcases hr with ⟨states, hl, hfirst, hlast, hs⟩
  have hn : states ≠ [] := by intro he; subst states; simp only [Zlength_nil] at hl; omega
  have hc := indexed_adjacent_steps_form_chain states hl.1 hs
  obtain ⟨cost, hcost, hb⟩ := AdjacentSwapChain_canonical_cost states hc
  have hh : states.headD [] = source := by cases states <;> simpa [Znth] using hfirst
  have ht : states.getLastD [] = target := by
    unfold Znth at hlast
    rw [nth_last_default_local states _ [] hn (by simp only [Zlength, Int.ofNat_eq_coe]; omega)] at hlast
    exact hlast
  refine ⟨cost, ?_, ?_⟩
  · rwa [hh, ht] at hcost
  · simp only [Zlength, Int.ofNat_eq_coe] at hl; omega

theorem AdjacentSwapList_to_AdjacentSwap (left right : List Int) (hs : AdjacentSwapList left right) :
    AdjacentSwap left right := by
  induction hs with
  | ASL_here x y tail =>
    exact ⟨0, ⟨by omega, by simp only [Zlength_cons]; have := Zlength_nonneg tail; omega⟩, rfl⟩
  | ASL_cons h left right hs ih =>
    rcases ih with ⟨i, hi, he⟩
    refine ⟨i + 1, ⟨by omega, by simp only [Zlength_cons]; omega⟩, ?_⟩
    rw [Znth_cons _ _ _ _ (by omega), Znth_cons _ _ _ _ (by omega),
      replace_Znth_cons _ _ _ _ (by omega), replace_Znth_cons _ _ _ _ (by omega)]
    simpa only [show i + 1 - 1 = i by omega, show i + 1 + 1 - 1 = i + 1 by omega] using congrArg (List.cons h) he

theorem CanonicalSwapPath_trans (left middle right : List Int) (n m : Nat)
    (hf : CanonicalSwapPath left middle n) (hs : CanonicalSwapPath middle right m) :
    CanonicalSwapPath left right (n + m) := by
  induction hf with
  | CSP_refl state => simpa using hs
  | CSP_step left middle finish steps hswap hpath ih =>
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      CSP_step left middle right (steps + m) hswap (ih hs)

theorem CanonicalSwapPath_cons (h : Int) (left right : List Int) (steps : Nat)
    (hp : CanonicalSwapPath left right steps) : CanonicalSwapPath (h :: left) (h :: right) steps := by
  induction hp with
  | CSP_refl state => exact CSP_refl _
  | CSP_step left middle right steps hs hp ih => exact CSP_step _ _ _ _ (ASL_cons _ _ _ hs) ih

theorem FirstRemove_construct_path (x : Int) (source : List Int) (position : Nat) (rest : List Int)
    (hr : FirstRemove x source position rest) : CanonicalSwapPath source (x :: rest) position := by
  induction hr with
  | FirstRemove_here tail => exact CSP_refl _
  | FirstRemove_later y tail position rest hn hr ih =>
    exact CanonicalSwapPath_trans _ _ _ position 1 (CanonicalSwapPath_cons y _ _ _ ih)
      (CSP_step _ _ _ 0 (ASL_here _ _ _) (CSP_refl _))

theorem CanonicalRemovalCost_construct_path (target : List Int) :
    ∀ source cost, CanonicalRemovalCost source target cost → CanonicalSwapPath source target cost := by
  induction target with
  | nil => intro source cost hc; rcases hc with ⟨rfl, rfl⟩; exact CSP_refl _
  | cons x target_tail ih =>
    intro source cost hc
    rcases hc with ⟨position, rest, tail_cost, hr, ht, rfl⟩
    exact CanonicalSwapPath_trans _ _ _ _ _ (FirstRemove_construct_path _ _ _ _ hr)
      (CanonicalSwapPath_cons x _ _ _ (ih _ _ ht))

theorem CanonicalSwapPath_states (source target : List Int) (steps : Nat)
    (hp : CanonicalSwapPath source target steps) :
    ∃ states : List (List Int), states.length = steps + 1 ∧ states.headD [] = source ∧
      states.getLastD [] = target ∧ ∀ i, (0 ≤ i ∧ i < (steps : Int)) →
        AdjacentSwap (Znth i states []) (Znth (i + 1) states []) := by
  induction hp with
  | CSP_refl state => exact ⟨[state], rfl, rfl, rfl, by intro i hi; omega⟩
  | CSP_step left middle right steps hs hp ih =>
    obtain ⟨states, hl, hh, ht, hsteps⟩ := ih
    cases states with
    | nil => simp at hl
    | cons head states =>
      refine ⟨left :: head :: states, by simp only [List.length_cons] at hl ⊢; omega, rfl,
        by simpa using ht, ?_⟩
      intro i hi
      by_cases he : i = 0
      · subst i
        change AdjacentSwap left head
        have he : head = middle := hh
        rw [he]
        exact AdjacentSwapList_to_AdjacentSwap _ _ hs
      · have hstep := hsteps (i - 1) (by omega)
        rw [Znth_cons [] i left (head :: states) (by omega),
          Znth_cons [] (i + 1) left (head :: states) (by omega)]
        simpa only [show i - 1 + 1 = i by omega, show i + 1 - 1 = i by omega] using hstep

theorem CanonicalRemovalCost_sound (source target : List Int) (cost : Nat)
    (hc : CanonicalRemovalCost source target cost) : SwapReach source target (cost : Int) := by
  have hp := CanonicalRemovalCost_construct_path _ _ _ hc
  obtain ⟨states, hl, hh, ht, hs⟩ := CanonicalSwapPath_states _ _ _ hp
  have hn : states ≠ [] := by intro he; subst states; simp at hl
  refine ⟨states, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [Zlength, hl, Int.ofNat_eq_coe]; omega
  · simp only [Zlength, hl, Int.ofNat_eq_coe]; omega
  · cases states <;> simpa [Znth] using hh
  · unfold Znth
    rw [nth_last_default_local states _ [] hn (by simp only [Zlength, Int.ofNat_eq_coe]; omega)]
    exact ht
  · intro i hi
    exact hs i (by simp only [Zlength, hl, Int.ofNat_eq_coe] at hi; omega)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
