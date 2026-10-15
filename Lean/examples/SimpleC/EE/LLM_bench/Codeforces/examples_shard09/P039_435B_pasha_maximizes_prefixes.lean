import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_swap_paths

set_option linter.unusedVariables false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open AUXLib

theorem p039_Zlength_sublist (lo hi : Int) (l : List Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi - lo := ListLib.Zlength_sublist lo hi l hlo hhi

theorem p039_app_Znth1 (pref tail : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength pref) :
    Znth i (pref ++ tail) 0 = Znth i pref 0 := ListLib.app_Znth1 0 pref tail i hi

theorem FirstRemove_length (x : Int) (source : List Int) (position : Nat) (rest : List Int)
    (hr : FirstRemove x source position rest) : source.length = rest.length + 1 := by
  induction hr with
  | FirstRemove_here tail => rfl
  | FirstRemove_later y tail p rest hn hr ih => simp only [List.length_cons]; omega

theorem FirstRemove_position_bound (x : Int) (source : List Int) (position : Nat) (rest : List Int)
    (hr : FirstRemove x source position rest) : position < source.length := by
  induction hr with
  | FirstRemove_here tail => simp
  | FirstRemove_later y tail p rest hn hr ih => simp only [List.length_cons]; omega

theorem FirstRemove_decompose (x : Int) (source : List Int) (position : Nat) (rest : List Int)
    (hr : FirstRemove x source position rest) :
    ∃ pref suffix, source = pref ++ x :: suffix ∧ rest = pref ++ suffix ∧
      pref.length = position ∧ Forall (fun y => x ≠ y) pref := by
  induction hr with
  | FirstRemove_here tail => exact ⟨[], tail, rfl, rfl, rfl, Forall.nil⟩
  | FirstRemove_later y tail p rest hn hr ih =>
    obtain ⟨pref, suffix, hs, hr', hl, ha⟩ := ih
    exact ⟨y :: pref, suffix, by simp [hs], by simp [hr'], by simp [hl], Forall.cons hn ha⟩

theorem FirstRemove_app_absent (x : Int) (pref suffix : List Int)
    (ha : Forall (fun y => x ≠ y) pref) :
    FirstRemove x (pref ++ x :: suffix) pref.length (pref ++ suffix) := by
  induction ha with
  | nil => exact FirstRemove_here _
  | @cons y pref hy ht ih => exact FirstRemove_later _ _ _ _ hy ih

theorem FirstRemove_functional (x : Int) (source : List Int) (p1 : Nat) (rest1 : List Int)
    (hf : FirstRemove x source p1 rest1) :
    ∀ p2 rest2, FirstRemove x source p2 rest2 → p1 = p2 ∧ rest1 = rest2 := by
  induction hf with
  | FirstRemove_here tail =>
    intro p2 rest2 hs
    cases hs with
    | FirstRemove_here => exact ⟨rfl, rfl⟩
    | FirstRemove_later y tail p rest hn hr => exact False.elim (hn rfl)
  | FirstRemove_later y tail p rest hn hr ih =>
    intro p2 rest2 hs
    cases hs with
    | FirstRemove_here => exact False.elim (hn rfl)
    | FirstRemove_later y' tail' p' rest' hn' hr' =>
      obtain ⟨rfl, rfl⟩ := ih _ _ hr'
      exact ⟨rfl, rfl⟩

theorem CanonicalRemovalCost_length (source target : List Int) (cost : Nat)
    (hc : CanonicalRemovalCost source target cost) : source.length = target.length := by
  induction target generalizing source cost with
  | nil => rcases hc with ⟨rfl, he⟩; rfl
  | cons x target ih =>
    rcases hc with ⟨p, rest, cost', hr, ht, he⟩
    have hs := FirstRemove_length _ _ _ _ hr
    have hh := ih _ _ ht
    simp only [List.length_cons]; omega

theorem CanonicalRemovalCost_cons_iff (x : Int) (source target : List Int) (cost : Nat) :
    CanonicalRemovalCost (x :: source) (x :: target) cost ↔ CanonicalRemovalCost source target cost := by
  constructor
  · rintro ⟨p, rest, cost', hr, ht, he⟩
    obtain ⟨hp, hs⟩ := FirstRemove_functional x (x :: source) 0 source (FirstRemove_here _) p rest hr
    subst p; subst rest
    have he' : cost = cost' := by omega
    rwa [he']
  · intro ht
    exact ⟨0, source, cost, FirstRemove_here _, ht, by omega⟩

theorem CanonicalRemovalCost_common_prefix (pref source target : List Int) (cost : Nat) :
    CanonicalRemovalCost (pref ++ source) (pref ++ target) cost ↔ CanonicalRemovalCost source target cost := by
  induction pref with
  | nil => rfl
  | cons x pref ih => exact (CanonicalRemovalCost_cons_iff x _ _ cost).trans ih

theorem SwapReach_monotone (source target : List Int) (small large : Int)
    (hr : SwapReach source target small) (hb : small ≤ large) : SwapReach source target large := by
  rcases hr with ⟨states, hl, hf, ht, hs⟩
  exact ⟨states, ⟨hl.1, by omega⟩, hf, ht, hs⟩

theorem PrefixEq_common_prefix (pref left right : List Int) (hl : Zlength left = Zlength right) :
    PrefixEq (pref ++ left) (pref ++ right) (Zlength pref) := by
  refine ⟨by simp only [Zlength_app]; omega, ⟨Zlength_nonneg _, ?_⟩, ?_⟩
  · rw [Zlength_app]; have := Zlength_nonneg left; omega
  · intro j hj
    rw [p039_app_Znth1 pref left j hj, p039_app_Znth1 pref right j hj]

theorem PrefixEq_decompose (left right : List Int) (position : Int)
    (hp : PrefixEq left right position) :
    ∃ pref left_tail right_tail, left = pref ++ left_tail ∧ right = pref ++ right_tail ∧
      Zlength pref = position ∧ Zlength left_tail = Zlength right_tail := by
  rcases hp with ⟨hlen, hpos, heq⟩
  have hpr : sublist 0 position left = sublist 0 position right := by
    apply (ListLib.list_eq_ext _ _ 0).mpr
    simp only [ListLib.Zlength, ListLib.Znth]
    have hl := p039_Zlength_sublist 0 position left ⟨by omega, hpos.1⟩ hpos.2
    have hr := p039_Zlength_sublist 0 position right ⟨by omega, hpos.1⟩ (by omega)
    refine ⟨by simpa using hl.trans hr.symm, ?_⟩
    intro j hj
    rw [Znth_sublist 0 0 j position left (by omega) (by omega),
      Znth_sublist 0 0 j position right (by omega) (by omega)]
    exact heq (j + 0) (by omega)
  refine ⟨sublist 0 position left, sublist position (Zlength left) left,
    sublist position (Zlength right) right, ?_, ?_, ?_, ?_⟩
  · rw [← sublist_split 0 (Zlength left) position left ⟨by omega, hpos.1⟩ ⟨hpos.2, le_rfl⟩,
      sublist_self left _ rfl]
  · rw [hpr, ← sublist_split 0 (Zlength right) position right ⟨by omega, hpos.1⟩ ⟨by omega, le_rfl⟩,
      sublist_self right _ rfl]
  · simpa using p039_Zlength_sublist 0 position left ⟨by omega, hpos.1⟩ hpos.2
  · rw [p039_Zlength_sublist position (Zlength left) left hpos le_rfl,
      p039_Zlength_sublist position (Zlength right) right ⟨hpos.1, by omega⟩ le_rfl, hlen]

theorem move_left_app_middle (pref middle : List Int) (x : Int) (suffix : List Int) :
    move_left (pref ++ middle ++ x :: suffix) (Zlength pref + Zlength middle) (Zlength pref) =
      pref ++ x :: middle ++ suffix := by
  have hp := Zlength_nonneg pref
  have hm := Zlength_nonneg middle
  have hs := Zlength_nonneg suffix
  unfold move_left
  simp only [List.append_assoc]
  rw [sublist_app_exact1 pref (middle ++ x :: suffix)]
  rw [app_Znth2 0 pref _ _ (by omega)]
  have hsub : Zlength pref + Zlength middle - Zlength pref = Zlength middle := by omega
  rw [hsub, app_Znth2 0 middle (x :: suffix) _ (by omega), sub_self, Znth0_cons]
  rw [sublist_split_app_r _ _ _ pref (middle ++ x :: suffix) rfl ⟨by omega, by omega⟩,
    sub_self, hsub, sublist_app_exact1]
  simp only [Zlength_app, Zlength_cons]
  rw [sublist_split_app_r _ _ _ pref (middle ++ x :: suffix) rfl ⟨by omega, by omega⟩]
  rw [show Zlength pref + Zlength middle + 1 - Zlength pref = Zlength middle + 1 by omega,
    show Zlength pref + (Zlength middle + (Zlength suffix + 1)) - Zlength pref =
      Zlength middle + (Zlength suffix + 1) by omega]
  rw [sublist_split_app_r _ _ _ middle (x :: suffix) rfl ⟨by omega, by omega⟩]
  rw [show Zlength middle + 1 - Zlength middle = 1 by omega,
    show Zlength middle + (Zlength suffix + 1) - Zlength middle = Zlength suffix + 1 by omega]
  rw [sublist_cons2 1 (Zlength suffix + 1) x suffix ⟨by omega, by omega⟩ (by rw [Zlength_cons])]
  rw [show (1 : Int) - 1 = 0 by omega, show Zlength suffix + 1 - 1 = Zlength suffix by omega,
    sublist_self suffix _ rfl]
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
