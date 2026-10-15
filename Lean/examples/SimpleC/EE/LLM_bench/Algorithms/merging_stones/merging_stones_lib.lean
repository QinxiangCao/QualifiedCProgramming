import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib
open AUXLib

abbrev _List_Z := List Int

def StoneMassesBounded (stones : List Int) (n : Int) : Prop :=
  Zlength stones = n ∧ ∀ i : Int, (0 ≤ i ∧ i < n) → (1 ≤ Znth i stones 0 ∧ Znth i stones 0 ≤ 1000)

inductive StoneMergePlan (stones : List Int) : Int → Int → Int → Prop where
  | StoneMergePlan_single (left : Int) : (0 ≤ left ∧ left < Zlength stones) → StoneMergePlan stones left left 0
  | StoneMergePlan_join (left split right left_cost right_cost : Int) :
      0 ≤ left → (left ≤ split ∧ split < right) → right < Zlength stones →
      StoneMergePlan stones left split left_cost → StoneMergePlan stones (split + 1) right right_cost →
      StoneMergePlan stones left right (left_cost + right_cost + sum (sublist left (right + 1) stones))
export StoneMergePlan (StoneMergePlan_single StoneMergePlan_join)

def StoneIntervalMin (stones : List Int) (left right answer : Int) : Prop :=
  MaxMinLib.min_value_of_subset (· ≤ ·) (fun cost => StoneMergePlan stones left right cost) (fun cost => cost) answer

def StoneMinimumCostLegacy (stones : List Int) (n answer : Int) : Prop :=
  Zlength stones = n ∧ StoneIntervalMin stones 0 (n - 1) answer

def StonePrefixProgressLegacy (stones «prefix» : List Int) (n done : Int) : Prop :=
  Zlength stones = n ∧ Zlength «prefix» = done + 1 ∧ (0 ≤ done ∧ done ≤ n) ∧
  ∀ k : Int, (0 ≤ k ∧ k ≤ done) → Znth k «prefix» 0 = sum (sublist 0 k stones)

def StonePrefixDoneLegacy (stones «prefix» : List Int) (n : Int) : Prop := StonePrefixProgressLegacy stones «prefix» n n

def StoneTableShape (table : List (List Int)) (n : Int) : Prop :=
  Zlength table = n ∧ ∀ row : Int, (0 ≤ row ∧ row < n) → Zlength (Znth row table []) = n

def StoneZeroRowsLegacy (table : List (List Int)) (n row : Int) : Prop :=
  StoneTableShape table n ∧ (0 ≤ row ∧ row ≤ n) ∧
  ∀ r c : Int, (0 ≤ r ∧ r < row) → (0 ≤ c ∧ c < n) → Znth c (Znth r table []) 0 = 0

def StoneZeroProgressLegacy (table : List (List Int)) (n row col : Int) : Prop :=
  StoneTableShape table n ∧ (0 ≤ row ∧ row < n) ∧ (0 ≤ col ∧ col ≤ n) ∧
  (∀ r c : Int, (0 ≤ r ∧ r < row) → (0 ≤ c ∧ c < n) → Znth c (Znth r table []) 0 = 0) ∧
  (∀ c : Int, (0 ≤ c ∧ c < col) → Znth c (Znth row table []) 0 = 0)

def StoneLenDoneLegacy (stones : List Int) (table : List (List Int)) (n len : Int) : Prop :=
  Zlength stones = n ∧ StoneTableShape table n ∧ 1 ≤ len ∧
  ∀ l left right : Int, (1 ≤ l ∧ l < len) → right = left + l - 1 → 0 ≤ left → left + l ≤ n →
    StoneIntervalMin stones left right (Znth right (Znth left table []) 0)

def StoneLeftProgressLegacy (stones : List Int) (table : List (List Int)) (n len left : Int) : Prop :=
  StoneLenDoneLegacy stones table n len ∧ (2 ≤ len ∧ len ≤ n) ∧ (0 ≤ left ∧ left ≤ n - len + 1) ∧
  ∀ done_left right : Int, (0 ≤ done_left ∧ done_left < left) →
    right = done_left + len - 1 → done_left + len ≤ n →
    StoneIntervalMin stones done_left right (Znth right (Znth done_left table []) 0)

def StoneSplitCandidate (stones : List Int) (table : List (List Int)) (left right split candidate : Int) : Prop :=
  (left ≤ split ∧ split < right) ∧ right < Zlength stones ∧
  candidate = Znth split (Znth left table []) 0 + Znth right (Znth (split + 1) table []) 0 +
    sum (sublist left (right + 1) stones)

def StoneSplitProgressLegacy (stones : List Int) (table : List (List Int)) (n len left split best : Int) : Prop :=
  StoneLeftProgressLegacy stones table n len left ∧
  let right := left + len - 1
  (left ≤ split ∧ split ≤ right) ∧ (0 ≤ best ∧ best ≤ 1000000) ∧
  ((split = left ∧ best = 1000000) ∨
   (left < split ∧ MaxMinLib.min_value_of_subset (· ≤ ·)
    (fun candidate => ∃ k : Int, (left ≤ k ∧ k < split) ∧ StoneSplitCandidate stones table left right k candidate)
    (fun candidate => candidate) best))

def StoneUpdatedCell (stones : List Int) (old_table new_table : List (List Int))
    (left right value : Int) : Prop :=
  (0 ≤ left ∧ left < Zlength old_table) ∧ (0 ≤ right ∧ right < Zlength (Znth left old_table [])) ∧
  new_table = replace_Znth left (replace_Znth right value (Znth left old_table [])) old_table ∧
  StoneIntervalMin stones left right value

set_option maxHeartbeats 4000000

private theorem minimum_iff (P : Int → Prop) (v : Int) :
    MaxMinLib.min_value_of_subset (· ≤ ·) P id v ↔ P v ∧ ∀ x, P x → v ≤ x := by
  constructor
  · rintro ⟨x, ⟨hx, hl⟩, rfl⟩; exact ⟨hx, hl⟩
  · rintro ⟨hx, hl⟩; exact ⟨v, ⟨hx, hl⟩, rfl⟩

theorem list_sum_bounds__arithmetic_safety (l : List Int)
    (hb : ∀ i, (0 ≤ i ∧ i < Zlength l) → (1 ≤ Znth i l 0 ∧ Znth i l 0 ≤ 1000)) :
    Zlength l ≤ sum l ∧ sum l ≤ Zlength l * 1000 := by
  induction l with
  | nil => exact ⟨by decide, by decide⟩
  | cons x xs ih =>
    have hx : 1 ≤ x ∧ x ≤ 1000 := hb 0 ⟨by omega, by rw [Zlength_cons]; have := Zlength_nonneg xs; omega⟩
    have ht : ∀ i, (0 ≤ i ∧ i < Zlength xs) → (1 ≤ Znth i xs 0 ∧ Znth i xs 0 ≤ 1000) := by
      intro i hi
      have h := hb (i+1) ⟨by omega, by rw [Zlength_cons]; omega⟩
      rw [Znth_cons 0 (i+1) x xs (by omega)] at h
      simpa only [Int.add_sub_cancel] using h
    have hh := ih ht
    change Zlength (x::xs) ≤ x+sum xs ∧ x+sum xs ≤ Zlength (x::xs)*1000
    rw [Zlength_cons]; omega

theorem sum_lower_bound__prefix_math (l : List Int)
    (hb : ∀ i, (0 ≤ i ∧ i < Zlength l) → 1 ≤ Znth i l 0) : Zlength l ≤ sum l := by
  induction l with
  | nil => decide
  | cons x xs ih =>
    have hx : 1 ≤ x := hb 0 ⟨by omega, by rw [Zlength_cons]; have := Zlength_nonneg xs; omega⟩
    have ht : ∀ i, (0 ≤ i ∧ i < Zlength xs) → 1 ≤ Znth i xs 0 := by
      intro i hi
      have h := hb (i+1) ⟨by omega, by rw [Zlength_cons]; omega⟩
      rw [Znth_cons 0 (i+1) x xs (by omega)] at h
      simpa only [Int.add_sub_cancel] using h
    have hh := ih ht
    change Zlength (x::xs) ≤ x+sum xs
    rw [Zlength_cons]; omega

theorem StoneMassesBounded_Znth__prefix_math (stones : List Int) (n i : Int)
    (hm : StoneMassesBounded stones n) (hi : 0 ≤ i ∧ i < n) :
    1 ≤ Znth i stones 0 ∧ Znth i stones 0 ≤ 1000 := hm.2 i hi

theorem StoneMassesBounded_sublist_sum_bounds__prefix_math (stones : List Int) (n lo hi : Int)
    (hm : StoneMassesBounded stones n) (hl : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ n) :
    hi-lo ≤ sum (sublist lo hi stones) ∧ sum (sublist lo hi stones) ≤ (hi-lo)*1000 := by
  have hlen : Zlength (sublist lo hi stones) = hi-lo :=
    ListLib.Zlength_sublist lo hi stones hl (by change hi ≤ Zlength stones; rw [hm.1]; exact hh)
  have hb := list_sum_bounds__arithmetic_safety (sublist lo hi stones) (by
    intro i hi'
    rw [hlen] at hi'
    rw [Znth_sublist 0 lo i hi stones hl.1 hi']
    exact hm.2 (i+lo) ⟨by omega, by omega⟩)
  rwa [hlen] at hb

theorem stone_interval_sum_bounds__arithmetic_safety (stones : List Int) (n left right : Int)
    (hn : n ≤ 8) (hl : 0 ≤ left) (hlr : left < right) (hr : right < n)
    (hm : StoneMassesBounded stones n) :
    2 ≤ sum (sublist left (right+1) stones) ∧ sum (sublist left (right+1) stones) ≤ 8000 := by
  have h := StoneMassesBounded_sublist_sum_bounds__prefix_math stones n left (right+1) hm ⟨hl, by omega⟩ (by omega)
  omega

theorem StonePrefixProgress_value_bounds__prefix_math (stones pre : List Int) (n done k : Int)
    (hm : StoneMassesBounded stones n) (hn : n ≤ 8)
    (hp : StonePrefixProgressLegacy stones pre n done) (hk : 0 ≤ k ∧ k ≤ done) :
    0 ≤ Znth k pre 0 ∧ Znth k pre 0 ≤ 8000 := by
  rw [hp.2.2.2 k hk]
  have h := StoneMassesBounded_sublist_sum_bounds__prefix_math stones n 0 k hm ⟨by omega, hk.1⟩ (by have := hp.2.2.1; omega)
  have := hp.2.2.1
  omega

theorem StonePrefixProgress_extend__prefix_math (stones pre : List Int) (n i : Int)
    (hp : StonePrefixProgressLegacy stones pre n i) (hi : 0 ≤ i ∧ i < n) :
    StonePrefixProgressLegacy stones (pre ++ [Znth i pre 0 + Znth i stones 0]) n (i+1) := by
  refine ⟨hp.1, ?_, ⟨by omega, by omega⟩, ?_⟩
  · rw [Zlength_app, Zlength_cons, Zlength_nil, hp.2.1]; omega
  · intro k hk
    by_cases he : k = i+1
    · subst k
      rw [app_Znth2 0 pre _ (i+1) (by have := hp.2.1; omega), hp.2.1, Int.sub_self]
      change Znth i pre 0 + Znth i stones 0 = sum (sublist 0 (i+1) stones)
      rw [hp.2.2.2 i ⟨hi.1, le_refl _⟩,
        sublist_split 0 (i+1) i stones ⟨by omega, hi.1⟩ ⟨by omega, by rw [hp.1]; omega⟩,
        sum_app, sublist_single 0 i stones (by rw [hp.1]; exact hi)]
      simp [sum]
    · have ha : Znth k (pre ++ [Znth i pre 0 + Znth i stones 0]) 0 = Znth k pre 0 :=
        ListLib.app_Znth1 0 pre _ k ⟨hk.1, by change k < Zlength pre; have := hp.2.1; omega⟩
      rw [ha]
      exact hp.2.2.2 k ⟨hk.1, by omega⟩

theorem StonePrefixDone_interval_sum__prefix_math (stones pre : List Int) (n lo hi : Int)
    (hp : StonePrefixDoneLegacy stones pre n) (hl : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ n) :
    Znth hi pre 0 - Znth lo pre 0 = sum (sublist lo hi stones) := by
  rw [hp.2.2.2 hi ⟨by omega, hh⟩, hp.2.2.2 lo ⟨hl.1, by omega⟩,
    sublist_split 0 hi lo stones ⟨by omega, hl.1⟩ ⟨hl.2, by rw [hp.1]; exact hh⟩,
    sum_app]
  omega

theorem StonePrefixDone_interval_bounds__prefix_math (stones pre : List Int) (n lo hi : Int)
    (hm : StoneMassesBounded stones n) (hp : StonePrefixDoneLegacy stones pre n)
    (hl : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ n) :
    hi-lo ≤ Znth hi pre 0-Znth lo pre 0 ∧ Znth hi pre 0-Znth lo pre 0 ≤ (hi-lo)*1000 := by
  rw [StonePrefixDone_interval_sum__prefix_math stones pre n lo hi hp hl hh]
  exact StoneMassesBounded_sublist_sum_bounds__prefix_math stones n lo hi hm hl hh

theorem StoneSplitProgress_initial__prefix_math (stones : List Int) (table : List (List Int)) (n len left : Int)
    (hp : StoneLeftProgressLegacy stones table n len left) (hl : 2 ≤ len) :
    StoneSplitProgressLegacy stones table n len left left 1000000 :=
  ⟨hp, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inl ⟨rfl, rfl⟩⟩

private theorem shape_update (t : List (List Int)) (n r c v : Int)
    (hs : StoneTableShape t n) (hr : 0 ≤ r ∧ r < n) :
    StoneTableShape (replace_Znth r (replace_Znth c v (Znth r t [])) t) n := by
  refine ⟨by rw [Zlength_replace_Znth]; exact hs.1, ?_⟩
  intro j hj
  by_cases he : r = j
  · subst j
    rw [Znth_replace_Znth_Same [] t r _ (by rw [hs.1]; exact hr), Zlength_replace_Znth]
    exact hs.2 r hr
  · rw [Znth_replace_Znth_Diff [] t r j _ (by rw [hs.1]; exact hr) (by rw [hs.1]; exact hj) he]
    exact hs.2 j hj

private theorem cell_update_same (t : List (List Int)) (n r c v : Int)
    (hs : StoneTableShape t n) (hr : 0 ≤ r ∧ r < n) (hc : 0 ≤ c ∧ c < n) :
    Znth c (Znth r (replace_Znth r (replace_Znth c v (Znth r t [])) t) []) 0 = v := by
  rw [Znth_replace_Znth_Same [] t r _ (by rw [hs.1]; exact hr),
    Znth_replace_Znth_Same 0 _ c v (by rw [hs.2 r hr]; exact hc)]

private theorem cell_update_diff (t : List (List Int)) (n r c v i j : Int)
    (hs : StoneTableShape t n) (hr : 0 ≤ r ∧ r < n) (hc : 0 ≤ c ∧ c < n)
    (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n) (hne : r ≠ i ∨ c ≠ j) :
    Znth j (Znth i (replace_Znth r (replace_Znth c v (Znth r t [])) t) []) 0 = Znth j (Znth i t []) 0 := by
  by_cases he : r = i
  · subst i
    rw [Znth_replace_Znth_Same [] t r _ (by rw [hs.1]; exact hr),
      Znth_replace_Znth_Diff 0 _ c j v (by rw [hs.2 r hr]; exact hc)
        (by rw [hs.2 r hr]; exact hj) (hne.resolve_left (by omega))]
  · rw [Znth_replace_Znth_Diff [] t r i _ (by rw [hs.1]; exact hr) (by rw [hs.1]; exact hi) he]

theorem StoneZeroProgress_store__zero_table (table : List (List Int)) (n row col : Int) (d : List Int)
    (hp : StoneZeroProgressLegacy table n row col) (hc : col < n) :
    StoneZeroProgressLegacy (replace_Znth row (replace_Znth col 0 (Znth row table d)) table) n row (col+1) := by
  have hd := Znth_indep table row d [] (by rw [hp.1.1]; exact hp.2.1)
  rw [hd]
  refine ⟨shape_update table n row col 0 hp.1 hp.2.1, hp.2.1,
    ⟨by have := hp.2.2.1; omega, by omega⟩, ?_, ?_⟩
  · intro r c hr hc'
    rw [cell_update_diff table n row col 0 r c hp.1 hp.2.1
      ⟨hp.2.2.1.1, hc⟩ ⟨hr.1, by have := hp.2.1; omega⟩ hc' (Or.inl (by omega))]
    exact hp.2.2.2.1 r c hr hc'
  · intro c hc'
    by_cases he : c = col
    · subst c
      exact cell_update_same table n row col 0 hp.1 hp.2.1 ⟨hp.2.2.1.1, hc⟩
    · rw [cell_update_diff table n row col 0 row c hp.1 hp.2.1
        ⟨hp.2.2.1.1, hc⟩ hp.2.1 ⟨hc'.1, by omega⟩ (Or.inr (by omega))]
      exact hp.2.2.2.2 c ⟨hc'.1, by omega⟩

theorem StoneIntervalMin_singleton__zero_table (stones : List Int) (left : Int)
    (hl : 0 ≤ left ∧ left < Zlength stones) : StoneIntervalMin stones left left 0 := by
  apply (minimum_iff _ _).mpr
  refine ⟨StoneMergePlan_single left hl, ?_⟩
  intro cost hp
  cases hp with
  | StoneMergePlan_single => omega
  | StoneMergePlan_join l k r lc rc hl hb => omega

theorem StoneLenDone_two_of_zero__zero_table (stones : List Int) (table : List (List Int)) (n : Int)
    (hlen : Zlength stones = n) (hn : 1 ≤ n) (hz : StoneZeroRowsLegacy table n n) :
    StoneLenDoneLegacy stones table n 2 := by
  refine ⟨hlen, hz.1, by omega, ?_⟩
  intro len left right hl hr hleft hfit
  have hel : len = 1 := by omega
  have her : right = left := by omega
  subst len right
  rw [hz.2.2 left left ⟨hleft, by omega⟩ ⟨hleft, by omega⟩]
  exact StoneIntervalMin_singleton__zero_table stones left ⟨hleft, by omega⟩

theorem StoneIntervalSum_bounds__interval_min_core (stones : List Int) (n left right : Int)
    (hm : StoneMassesBounded stones n) (hn : n ≤ 8) (hl : 0 ≤ left ∧ left ≤ right) (hr : right < n) :
    0 ≤ sum (sublist left (right+1) stones) ∧ sum (sublist left (right+1) stones) ≤ 8000 := by
  have h := StoneMassesBounded_sublist_sum_bounds__prefix_math stones n left (right+1) hm ⟨hl.1, by omega⟩ (by omega)
  omega

theorem StoneMergePlan_bounds__interval_min_core (stones : List Int) (left right cost : Int)
    (hp : StoneMergePlan stones left right cost) (n : Int)
    (hm : StoneMassesBounded stones n) (hn : n ≤ 8) : 0 ≤ cost ∧ cost ≤ (right-left)*8000 := by
  induction hp with
  | StoneMergePlan_single => omega
  | StoneMergePlan_join l k r lc rc hl hb hr hpl hpr ihl ihr =>
    have hsum := StoneIntervalSum_bounds__interval_min_core stones n l r hm hn ⟨hl, by omega⟩ (by have := hm.1; omega)
    omega

theorem StoneIntervalMin_precise_bounds__interval_min_core (stones : List Int) (n left right answer : Int)
    (hm : StoneMassesBounded stones n) (hn : n ≤ 8) (hl : 0 ≤ left ∧ left ≤ right) (hr : right < n)
    (hp : StoneIntervalMin stones left right answer) : 0 ≤ answer ∧ answer ≤ (right-left)*8000 :=
  StoneMergePlan_bounds__interval_min_core stones left right answer ((minimum_iff _ _).mp hp).1 n hm hn

theorem StoneIntervalMin_bounds__interval_min_core (stones : List Int) (n left right answer : Int)
    (hm : StoneMassesBounded stones n) (hn : n ≤ 8) (hl : 0 ≤ left ∧ left ≤ right) (hr : right < n)
    (hp : StoneIntervalMin stones left right answer) : 0 ≤ answer ∧ answer ≤ 56000 := by
  have h := StoneIntervalMin_precise_bounds__interval_min_core stones n left right answer hm hn hl hr hp
  omega

theorem StoneLenDone_entry_precise_bounds__interval_min_core (stones : List Int) (table : List (List Int))
    (n len left right : Int) (hm : StoneMassesBounded stones n) (hn : n ≤ 8)
    (hd : StoneLenDoneLegacy stones table n len) (hl : 0 ≤ left ∧ left ≤ right) (hr : right < n)
    (hshort : right-left+1 < len) :
    0 ≤ Znth right (Znth left table []) 0 ∧ Znth right (Znth left table []) 0 ≤ (right-left)*8000 :=
  StoneIntervalMin_precise_bounds__interval_min_core stones n left right _ hm hn hl hr
    (hd.2.2.2 (right-left+1) left right ⟨by omega, hshort⟩ (by omega) hl.1 (by omega))

theorem StoneLenDone_entry_bounds__interval_min_core (stones : List Int) (table : List (List Int))
    (n len left right : Int) (hm : StoneMassesBounded stones n) (hn : n ≤ 8)
    (hd : StoneLenDoneLegacy stones table n len) (hl : 0 ≤ left ∧ left ≤ right) (hr : right < n)
    (hshort : right-left+1 < len) :
    0 ≤ Znth right (Znth left table []) 0 ∧ Znth right (Znth left table []) 0 ≤ 56000 := by
  have h := StoneLenDone_entry_precise_bounds__interval_min_core stones table n len left right hm hn hd hl hr hshort
  omega

theorem StoneSplitProgress_table_shape__interval_min_core (stones : List Int) (table : List (List Int))
    (n len left split best : Int) (hp : StoneSplitProgressLegacy stones table n len left split best) :
    StoneTableShape table n := hp.1.1.2.1

theorem StoneSplitProgress_child_bounds__interval_min_core (stones : List Int) (table : List (List Int))
    (n len left split right best : Int) (d : List Int) (hm : StoneMassesBounded stones n) (hn : n ≤ 8)
    (hp : StoneSplitProgressLegacy stones table n len left split best) (hr : right = left+len-1)
    (hk : left ≤ split ∧ split < right) (hrn : right < n) :
    (0 ≤ Znth split (Znth left table d) 0 ∧ Znth split (Znth left table d) 0 ≤ 56000) ∧
    (0 ≤ Znth right (Znth (split+1) table d) 0 ∧ Znth right (Znth (split+1) table d) 0 ≤ 56000) := by
  have hleft := hp.1.2.2.1.1
  have hs := hp.1.1.2.1.1
  rw [Znth_indep table left d [] (by rw [hs]; omega), Znth_indep table (split+1) d [] (by rw [hs]; omega)]
  exact ⟨StoneLenDone_entry_bounds__interval_min_core stones table n len left split hm hn hp.1.1
      ⟨hleft, hk.1⟩ (by omega) (by omega),
    StoneLenDone_entry_bounds__interval_min_core stones table n len (split+1) right hm hn hp.1.1
      ⟨by omega, by omega⟩ hrn (by omega)⟩

theorem StoneSplitProgress_candidate_facts__interval_min_core (stones : List Int) (table : List (List Int))
    (n len left split right best interval_sum : Int) (d : List Int)
    (hm : StoneMassesBounded stones n) (hn : n ≤ 8)
    (hp : StoneSplitProgressLegacy stones table n len left split best) (hr : right = left+len-1)
    (hk : left ≤ split ∧ split < right) (hrn : right < n)
    (hsm : interval_sum = sum (sublist left (right+1) stones)) :
    let candidate := Znth split (Znth left table d) 0+Znth right (Znth (split+1) table d) 0+interval_sum
    (0 ≤ candidate ∧ candidate ≤ 56000) ∧ StoneSplitCandidate stones table left right split candidate := by
  dsimp
  have hleft := hp.1.2.2.1.1
  have hs := hp.1.1.2.1.1
  rw [Znth_indep table left d [] (by rw [hs]; omega), Znth_indep table (split+1) d [] (by rw [hs]; omega)]
  have hlb := StoneLenDone_entry_precise_bounds__interval_min_core stones table n len left split hm hn hp.1.1
    ⟨hleft, hk.1⟩ (by omega) (by omega)
  have hrb := StoneLenDone_entry_precise_bounds__interval_min_core stones table n len (split+1) right hm hn hp.1.1
    ⟨by omega, by omega⟩ hrn (by omega)
  have hsb := StoneIntervalSum_bounds__interval_min_core stones n left right hm hn ⟨hleft, by omega⟩ hrn
  exact ⟨⟨by omega, by omega⟩, hk, by have := hm.1; omega, by rw [hsm]⟩

theorem StoneSplitProgress_complete__interval_min_core (stones : List Int) (table : List (List Int))
    (n len left right best : Int) (hr : right = left+len-1) (hlr : left < right) (hrn : right < n)
    (hp : StoneSplitProgressLegacy stones table n len left right best) : StoneIntervalMin stones left right best := by
  have hleft := hp.1.2.2.1.1
  have hdim : right < Zlength stones := by have := hp.1.1.1; omega
  have hmin := hp.2.2.2.resolve_left (by intro h; omega)
  rw [←hr] at hmin
  have hm := (minimum_iff _ best).mp hmin.2
  have children (k : Int) (hk : left ≤ k ∧ k < right) :=
    And.intro
      (hp.1.1.2.2.2 (k-left+1) left k ⟨by omega, by omega⟩ (by omega) hleft (by omega))
      (hp.1.1.2.2.2 (right-k) (k+1) right ⟨by omega, by omega⟩ (by omega) (by omega) (by omega))
  apply (minimum_iff _ best).mpr
  constructor
  · obtain ⟨k, hk, hc⟩ := hm.1
    rw [hc.2.2]
    have hch := children k hk
    exact StoneMergePlan_join left k right _ _ hleft hk hdim
      ((minimum_iff _ _).mp hch.1).1 ((minimum_iff _ _).mp hch.2).1
  · intro cost hplan
    cases hplan with
    | StoneMergePlan_single => omega
    | StoneMergePlan_join l k r lc rc hl hk hd hpl hpr =>
      have hch := children k hk
      have hlc := ((minimum_iff _ _).mp hch.1).2 lc hpl
      have hrc := ((minimum_iff _ _).mp hch.2).2 rc hpr
      have hcan := hm.2 _ ⟨k, hk, hk, hd, rfl⟩
      omega

theorem StoneLenDone_final_facts__interval_min_core (stones : List Int) (table : List (List Int))
    (n len : Int) (d : List Int) (hn : 1 ≤ n) (hnu : n ≤ 8) (hm : StoneMassesBounded stones n)
    (hl : len > n) (hu : len ≤ n+1) (hp : StoneLenDoneLegacy stones table n len) :
    let answer := Znth (n-1) (Znth 0 table d) 0
    StoneLenDoneLegacy stones table n (n+1) ∧ StoneMinimumCostLegacy stones n answer ∧ (0 ≤ answer ∧ answer ≤ 56000) := by
  have he : len = n+1 := by omega
  subst len
  have hmin := hp.2.2.2 n 0 (n-1) ⟨hn, by omega⟩ (by omega) (by omega) (by omega)
  rw [Znth_indep table 0 [] d (by rw [hp.2.1.1]; omega)] at hmin
  exact ⟨hp, ⟨hp.1, hmin⟩, StoneIntervalMin_bounds__interval_min_core stones n 0 (n-1) _ hm hnu
    ⟨by omega, by omega⟩ (by omega) hmin⟩

theorem StoneSplitProgress_keep_best__split_loop_step (stones : List Int) (table : List (List Int))
    (n len left right split candidate best : Int) (hr : right = left+len-1) (hk : split < right)
    (hcmax : candidate ≤ 56000) (hbetter : best ≤ candidate)
    (hc : StoneSplitCandidate stones table left right split candidate)
    (hp : StoneSplitProgressLegacy stones table n len left split best) :
    StoneSplitProgressLegacy stones table n len left (split+1) best := by
  have hstate := hp.2.2.2.resolve_left (by intro h; omega)
  have hm := (minimum_iff _ best).mp hstate.2
  refine ⟨hp.1, ⟨by have := hp.2.1; omega, by omega⟩, hp.2.2.1, Or.inr ⟨by omega, ?_⟩⟩
  apply (minimum_iff _ best).mpr
  constructor
  · obtain ⟨k, hb, hkc⟩ := hm.1
    exact ⟨k, ⟨hb.1, by omega⟩, hkc⟩
  · rintro value ⟨k, hb, hkc⟩
    by_cases hlt : k < split
    · exact hm.2 value ⟨k, ⟨hb.1, hlt⟩, hkc⟩
    · have he : k = split := by omega
      subst k
      have hv : candidate = value := by rw [hr] at hc; exact hc.2.2.trans hkc.2.2.symm
      omega

theorem StoneSplitProgress_replace_best__split_loop_step (stones : List Int) (table : List (List Int))
    (n len left right split candidate best : Int) (hr : right = left+len-1) (hk : split < right)
    (hc0 : 0 ≤ candidate) (hcmax : candidate ≤ 1000000) (hbetter : candidate < best)
    (hc : StoneSplitCandidate stones table left right split candidate)
    (hp : StoneSplitProgressLegacy stones table n len left split best) :
    StoneSplitProgressLegacy stones table n len left (split+1) candidate := by
  refine ⟨hp.1, ⟨by have := hp.2.1; omega, by omega⟩, ⟨hc0, hcmax⟩,
    Or.inr ⟨by have := hp.2.1; omega, ?_⟩⟩
  apply (minimum_iff _ candidate).mpr
  rw [hr] at hc
  constructor
  · exact ⟨split, ⟨hp.2.1.1, by omega⟩, hc⟩
  · rintro value ⟨k, hb, hkc⟩
    by_cases hlt : k < split
    · have hstate := hp.2.2.2.resolve_left (by intro h; omega)
      have hm := (minimum_iff _ best).mp hstate.2
      exact le_trans (le_of_lt hbetter) (hm.2 value ⟨k, ⟨hb.1, hlt⟩, hkc⟩)
    · have he : k = split := by omega
      subst k
      exact le_of_eq (hc.2.2.trans hkc.2.2.symm)

theorem StoneLenDone_to_initial_left_progress__table_progress (stones : List Int) (table : List (List Int))
    (n len : Int) (hp : StoneLenDoneLegacy stones table n len) (hl : 2 ≤ len ∧ len ≤ n) :
    StoneLeftProgressLegacy stones table n len 0 :=
  ⟨hp, hl, ⟨by omega, by omega⟩, fun l r hb _ _ => False.elim (by omega)⟩

theorem StoneUpdatedCell_to_next_left_progress__table_progress (stones : List Int)
    (old_table new_table : List (List Int)) (n len left right value : Int)
    (hp : StoneLeftProgressLegacy stones old_table n len left) (hr : right = left+len-1) (hfit : left+len ≤ n)
    (hu : StoneUpdatedCell stones old_table new_table left right value) :
    StoneLeftProgressLegacy stones new_table n len (left+1) := by
  rcases hu with ⟨hli, hri, rfl, hmin⟩
  have hs := hp.1.2.1
  have hl : 0 ≤ left ∧ left < n := by have := hp.2.2.1; have := hp.2.1; omega
  have hrr : 0 ≤ right ∧ right < n := by have := hp.2.1; omega
  refine ⟨⟨hp.1.1, shape_update old_table n left right value hs hl, hp.1.2.2.1, ?_⟩,
    hp.2.1, ⟨by omega, by omega⟩, ?_⟩
  · intro l i j hlen hj hi hfits
    have hir : 0 ≤ i ∧ i < n := ⟨hi, by omega⟩
    have hjr : 0 ≤ j ∧ j < n := ⟨by omega, by omega⟩
    have hneq : left ≠ i ∨ right ≠ j := by
      by_cases he : left = i
      · right; omega
      · exact Or.inl he
    rw [cell_update_diff old_table n left right value i j hs hl hrr hir hjr hneq]
    exact hp.1.2.2.2 l i j hlen hj hi hfits
  · intro i j hi hj hfits
    by_cases he : i = left
    · subst i
      have hej : j = right := by omega
      rw [hej]
      rw [cell_update_same old_table n left right value hs hl hrr]
      exact hmin
    · rw [cell_update_diff old_table n left right value i j hs hl hrr
        ⟨hi.1, by omega⟩ ⟨by have := hp.2.1; omega, by omega⟩ (Or.inl (by omega))]
      exact hp.2.2.2 i j ⟨hi.1, by omega⟩ hj hfits

theorem StoneLeftProgress_to_next_len_done__table_progress (stones : List Int) (table : List (List Int))
    (n len left : Int) (hp : StoneLeftProgressLegacy stones table n len left) (he : left+len > n) :
    StoneLenDoneLegacy stones table n (len+1) := by
  refine ⟨hp.1.1, hp.1.2.1, by have := hp.2.1; omega, ?_⟩
  intro l i j hl hj hi hfit
  by_cases hlt : l < len
  · exact hp.1.2.2.2 l i j ⟨hl.1, hlt⟩ hj hi hfit
  · have heq : l = len := by omega
    subst l
    exact hp.2.2.2 i j ⟨hi, by omega⟩ hj hfit

end SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib
open AUXLib

def StoneMinimumCost (stones : List Int) (answer : Int) : Prop :=
  StoneIntervalMin stones 0 (Zlength stones - 1) answer
def StonePrefixProgress (stones «prefix» : List Int) (done : Int) : Prop :=
  ∀ k : Int, (0 ≤ k ∧ k ≤ done) → Znth k «prefix» 0 = sum (sublist 0 k stones)
def StonePrefixDone (stones «prefix» : List Int) (n : Int) : Prop :=
  StonePrefixProgress stones «prefix» n
def StoneZeroRows (table : List (List Int)) (row : Int) : Prop :=
  Forall (Forall (Eq 0)) (sublist 0 row table)
def StoneZeroProgress (table : List (List Int)) (row col : Int) : Prop :=
  StoneZeroRows table row ∧ Forall (Eq 0) (sublist 0 col (Znth row table []))
def StoneLenDone (stones : List Int) (table : List (List Int)) (n len : Int) : Prop :=
  ∀ l left right : Int, (1 ≤ l ∧ l < len) → right = left + l - 1 →
    0 ≤ left → left + l ≤ n → StoneIntervalMin stones left right (Znth right (Znth left table []) 0)
def StoneLeftProgress (stones : List Int) (table : List (List Int)) (n len left : Int) : Prop :=
  StoneLenDone stones table n len ∧ ∀ done_left right : Int,
    (0 ≤ done_left ∧ done_left < left) → right = done_left + len - 1 → done_left + len ≤ n →
    StoneIntervalMin stones done_left right (Znth right (Znth done_left table []) 0)
def StoneSplitProgress (stones : List Int) (table : List (List Int)) (n len left split best : Int) : Prop :=
  StoneLeftProgress stones table n len left ∧
  ((split = left ∧ best = 1000000) ∨ (left < split ∧
    MaxMinLib.min_value_of_subset (LE.le (α := Int))
      (fun candidate => ∃ k : Int, (left ≤ k ∧ k < split) ∧
        StoneSplitCandidate stones table left (left + len - 1) k candidate)
      (fun candidate => candidate) best))

theorem StoneMinimumCostLegacy.toAnnotation (h : StoneMinimumCostLegacy stones n answer) :
    StoneMinimumCost stones answer := by
  rcases h with ⟨hlen, hmin⟩
  change StoneIntervalMin stones 0 (Zlength stones - 1) answer
  rw [hlen]
  exact hmin
theorem StonePrefixProgressLegacy.toAnnotation (h : StonePrefixProgressLegacy stones xs n done) :
    StonePrefixProgress stones xs done := h.2.2.2
theorem StoneLenDoneLegacy.toAnnotation (h : StoneLenDoneLegacy stones table n len) :
    StoneLenDone stones table n len := h.2.2.2

end SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib
namespace SimpleC.EE.LLM_bench.Algorithms.merging_stones
export merging_stones_lib (StoneMinimumCost StonePrefixProgress StonePrefixDone StoneZeroRows StoneZeroProgress StoneLenDone StoneLeftProgress StoneSplitProgress)
end SimpleC.EE.LLM_bench.Algorithms.merging_stones
