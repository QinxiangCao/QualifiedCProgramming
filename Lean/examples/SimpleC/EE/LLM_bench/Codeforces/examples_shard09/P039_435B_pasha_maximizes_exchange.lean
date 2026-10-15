import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_selection_decomposition

set_option linter.unusedVariables false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open AUXLib

theorem ReachableFirstMaximum_exchange (current : List Int) (pos remaining best : Int)
    (hm : ReachableFirstMaximum current pos remaining best) :
    GreedyExchangeClosure current pos remaining best := by
  obtain ⟨sp, middle, x, suffix, hcur, hsp, hmid, hsmall, hbudget, hselected, hmoved⟩ :=
    ReachableFirstMaximum_decompose _ _ _ _ hm
  rcases hm with ⟨hpos, hhi, hb, hmax, hfirst⟩
  have hle : LexLe current (move_left current best pos) := by
    rw [hmoved, hcur]
    simp only [List.append_assoc, List.cons_append]
    cases middle with
    | nil => exact Or.inl (by simp)
    | cons head tail =>
      cases hsmall with
      | cons hh ht => exact LexLe_common_prefix_lt _ _ _ _ _ hh
  constructor
  · intro q hq
    exact LexLe_trans _ _ _ hq hle
  · intro q hp hr
    obtain ⟨cost, hc, hcost⟩ := SwapReach_canonical_lower_bound _ _ _ hr
    obtain ⟨pref, qtail, ctail, hq, hcp, hpl, htl⟩ := PrefixEq_decompose _ _ _ hp
    have he : pref = sp ∧ ctail = middle ++ x :: suffix :=
      app_cancel_equal_Zlength pref ctail sp _ (by omega) (by rw [← hcp]; simpa only [List.append_assoc] using hcur)
    rcases he with ⟨hpr, hctr⟩
    subst pref
    subst ctail
    have htc : CanonicalRemovalCost (middle ++ x :: suffix) qtail cost := by
      apply (CanonicalRemovalCost_common_prefix sp _ _ cost).mp
      rw [hcur, hq] at hc
      simpa only [List.append_assoc] using hc
    cases qtail with
    | nil =>
      simp only [Zlength_nil, Zlength_app, Zlength_cons] at htl
      have := Zlength_nonneg middle
      have := Zlength_nonneg suffix
      omega
    | cons y qrest =>
      rcases htc with ⟨position, srest, tail_cost, hremove, hrest, hsum⟩
      have hyx : y ≤ x := by
        have hpb := FirstRemove_position_bound _ _ _ _ hremove
        have hpv := FirstRemove_Znth _ _ _ _ hremove
        have hpr : pos ≤ pos + (position : Int) ∧
            pos + (position : Int) < min (Zlength current) (pos + remaining + 1) := by
          have hcur_len : Zlength current = Zlength sp + Zlength (middle ++ x :: suffix) := by
            rw [hcur]; simp only [Zlength_app]; omega
          have hpbz : (position : Int) < Zlength (middle ++ x :: suffix) := by
            simp only [Zlength, Int.ofNat_eq_coe]; omega
          constructor
          · omega
          · apply lt_min
            · omega
            · omega
        have hbest : Znth best current 0 = x := by
          rw [hcur]
          simp only [List.append_assoc]
          rw [app_Znth2 0 sp (middle ++ x :: suffix) best (by omega),
            show best - Zlength sp = Zlength middle by omega,
            app_Znth2 0 middle (x :: suffix) _ (by omega), sub_self, Znth0_cons]
        have hposition : Znth (pos + (position : Int)) current 0 = y := by
          rw [hcur]
          simp only [List.append_assoc]
          rw [app_Znth2 0 sp (middle ++ x :: suffix) _ (by omega),
            show pos + (position : Int) - Zlength sp = (position : Int) by omega]
          exact hpv
        have hh := hmax _ hpr
        rwa [hposition, hbest] at hh
      by_cases hlt : y < x
      · left
        rw [hmoved, hq]
        simp only [List.append_assoc, List.cons_append]
        exact LexLe_common_prefix_lt _ _ _ _ _ hlt
      · have he : y = x := by omega
        subst y
        obtain ⟨hepos, herest⟩ := FirstRemove_functional _ _ _ _ hremove _ _ hselected
        subst position
        subst srest
        have htailbudget : (tail_cost : Int) ≤ remaining - (best - pos) := by
          simp only [Zlength, Int.ofNat_eq_coe] at hmid
          omega
        have hreconstructed : CanonicalRemovalCost
            ((sp ++ [x]) ++ (middle ++ suffix)) ((sp ++ [x]) ++ qrest) tail_cost :=
          (CanonicalRemovalCost_common_prefix (sp ++ [x]) _ _ tail_cost).mpr hrest
        have hreach := SwapReach_monotone _ _ _ _ (CanonicalRemovalCost_sound _ _ _ hreconstructed) htailbudget
        right
        constructor
        · rw [hmoved, hq]
          have hposlen : Zlength (sp ++ [x]) = pos + 1 := by simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega
          have hrestlen := CanonicalRemovalCost_length _ _ _ hrest
          have hpref := PrefixEq_common_prefix (sp ++ [x]) qrest (middle ++ suffix)
            (by simp only [Zlength, Int.ofNat_eq_coe]; omega)
          simpa only [List.append_assoc, List.singleton_append, hposlen] using hpref
        · rw [hmoved, hq]
          simpa only [List.append_assoc, List.singleton_append] using hreach

theorem GreedySelectionReady_universal (current : List Int) (pos remaining : Int) :
    GreedySelectionReady current pos remaining := by
  intro best hm
  exact ReachableFirstMaximum_exchange _ _ _ _ hm

theorem swap_reach_refl__initialization (a : List Int) (k : Int) (hk : 0 ≤ k) : SwapReach a a k := by
  refine ⟨[a], ⟨by simp only [Zlength_cons, Zlength_nil]; omega, by simp only [Zlength_cons, Zlength_nil]; omega⟩,
    rfl, ?_, ?_⟩
  · simp only [Zlength_cons, Zlength_nil]; rfl
  · intro i hi; simp only [Zlength_cons, Zlength_nil] at hi; omega

theorem greedy_progress_initial__initialization (input : List Int) (budget : Int) (hb : 0 ≤ budget) :
    GreedyProgress input budget input 0 budget := by
  refine ⟨rfl, ⟨le_rfl, Zlength_nonneg _⟩, ⟨hb, le_rfl⟩, ?_, ?_⟩
  · rw [sub_self]
    exact swap_reach_refl__initialization _ _ le_rfl
  · intro q hr
    right
    refine ⟨?_, hr⟩
    obtain ⟨cost, hc, hb⟩ := SwapReach_canonical_lower_bound _ _ _ hr
    have hl := CanonicalRemovalCost_length _ _ _ hc
    exact ⟨by simp only [Zlength, hl, Int.ofNat_eq_coe], ⟨le_rfl, Zlength_nonneg _⟩, by intro j hj; omega⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
