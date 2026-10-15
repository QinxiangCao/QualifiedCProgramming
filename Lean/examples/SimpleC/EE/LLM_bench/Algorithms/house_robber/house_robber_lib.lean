import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import AUXLib.ListLib.NPerm
import Mathlib.Data.List.Perm.Subperm

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib
open AUXLib

def NonAdjacentIndexList (limit : Int) (picks : List Int) : Prop :=
  0 ≤ limit ∧ NoDup picks ∧ Forall (fun i => 0 ≤ i ∧ i < limit) picks ∧
  ∀ i j : Int, i ∈ picks → j ∈ picks → i ≠ j → 2 ≤ Z.abs (i - j)

def RobPlanValue (l picks : List Int) : Int := sum (picks.map (fun i => Znth i l 0))

def RobPrefixValue (l : List Int) (len value : Int) : Prop :=
  ∃ picks, (0 ≤ len ∧ len ≤ Zlength l) ∧ NonAdjacentIndexList len picks ∧
    value = RobPlanValue l picks

def RobPrefixOpt (l : List Int) (len answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun value => RobPrefixValue l len value)
    (fun value => value) answer

def HouseRobberAnswer (l : List Int) (answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun value => RobPrefixValue l (Zlength l) value)
    (fun value => value) answer

def HouseRobberDPState (l : List Int) (i prev2 prev1 : Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength l) ∧ RobPrefixOpt l i prev1 ∧
    ((i = 0 ∧ prev2 = 0) ∨ (0 < i ∧ RobPrefixOpt l (i - 1) prev2))


@[simp] private theorem plan_nil (l : List Int) : RobPlanValue l [] = 0 := rfl
@[simp] private theorem plan_cons (l : List Int) (x : Int) (xs : List Int) :
    RobPlanValue l (x :: xs) = Znth x l 0 + RobPlanValue l xs := rfl

private theorem remove_mem (x y : Int) (xs : List Int) :
    y ∈ remove_eqdec x xs ↔ y ∈ xs ∧ y ≠ x := by
  induction xs with
  | nil => simp [remove_eqdec]
  | cons z zs ih =>
    by_cases h : x = z
    · subst z; simp [remove_eqdec, ih]; tauto
    · simp only [remove_eqdec, if_neg h, List.mem_cons, ih]
      constructor
      · rintro (hy | ⟨hy, hn⟩)
        · exact ⟨Or.inl hy, by intro he; exact h (he.symm.trans hy)⟩
        · exact ⟨Or.inr hy, hn⟩
      · rintro ⟨hy | hy, hn⟩
        · exact Or.inl hy
        · exact Or.inr ⟨hy, hn⟩

private theorem remove_notin (x : Int) (xs : List Int) (h : x ∉ xs) :
    remove_eqdec x xs = xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.mem_cons, not_or] at h
    simp [remove_eqdec, h.1, ih h.2]

theorem rob_prefix_opt_elim (l : List Int) (len answer : Int)
    (h : RobPrefixOpt l len answer) :
    RobPrefixValue l len answer ∧
    (∀ value, RobPrefixValue l len value → value ≤ answer) := by
  rcases h with ⟨a, ⟨ha, hb⟩, rfl⟩
  exact ⟨ha, hb⟩

theorem rob_prefix_opt_intro (l : List Int) (len answer : Int)
    (ha : RobPrefixValue l len answer)
    (hb : ∀ value, RobPrefixValue l len value → value ≤ answer) :
    RobPrefixOpt l len answer := ⟨answer, ⟨ha, hb⟩, rfl⟩

theorem RobPrefixOpt_zero (l : List Int) : RobPrefixOpt l 0 0 := by
  apply rob_prefix_opt_intro
  · refine ⟨[], ⟨by omega, Zlength_nonneg l⟩, ?_, rfl⟩
    exact ⟨by omega, by simp [NoDup], .nil, by simp⟩
  · rintro value ⟨picks, hlen, hna, rfl⟩
    cases picks with
    | nil => simp
    | cons x xs => have h := hna.2.2.1.mem (by simp : x ∈ x :: xs); omega

theorem rob_plan_value_nonneg_bound (l : List Int) (n : Int) (picks : List Int)
    (hr : ∀ k, 0 ≤ k ∧ k < n → 0 ≤ Znth k l 0 ∧ Znth k l 0 ≤ 10000)
    (hf : Forall (fun i => 0 ≤ i ∧ i < n) picks) :
    0 ≤ RobPlanValue l picks ∧ RobPlanValue l picks ≤ 10000 * (picks.length : Int) := by
  induction hf with
  | nil => simp
  | @cons x xs hx hxs ih =>
    have h := hr x hx
    simp only [plan_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    omega

theorem NoDup_remove_Z (x : Int) (l : List Int) (h : NoDup l) :
    NoDup (remove_eqdec x l) := by
  induction l with
  | nil => simp [NoDup, remove_eqdec]
  | cons a xs ih =>
    obtain ⟨hna, hnd⟩ := List.nodup_cons.mp h
    by_cases heq : x = a
    · simpa only [remove_eqdec, if_pos heq] using ih hnd
    · simp only [remove_eqdec, if_neg heq]
      exact List.nodup_cons.mpr ⟨fun hm => hna ((remove_mem x a xs).mp hm).1, ih hnd⟩

theorem NoDup_map_Z_to_nat (picks : List Int)
    (hf : Forall (fun i => 0 ≤ i) picks) (hn : NoDup picks) :
    NoDup (picks.map Int.toNat) := by
  induction picks with
  | nil => simp [NoDup]
  | cons x xs ih =>
    cases hf with
    | cons hx hs =>
      obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hn
      simp only [List.map_cons, NoDup, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
        have hnon := hs.mem hy
        have hxy : y = x := by omega
        exact hnot (hxy ▸ hy)
      · exact ih hs hnd

theorem NoDup_range_length (limit : Int) (picks : List Int) (hl : 0 ≤ limit)
    (hn : NoDup picks) (hf : Forall (fun i => 0 ≤ i ∧ i < limit) picks) :
    (picks.length : Int) ≤ limit := by
  have hm := NoDup_map_Z_to_nat picks
    (Forall.iff_forall_mem.mpr (fun x hx => (hf.mem hx).1)) hn
  have hs : picks.map Int.toNat ⊆ List.range limit.toNat := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hh := hf.mem hy
    simp only [List.mem_range]
    omega
  have hh := (hm.subperm hs).length_le
  simp only [List.length_map, List.length_range] at hh
  omega

theorem rob_prefix_value_bound_by_len (l : List Int) (len value n : Int)
    (hle : len ≤ n)
    (hr : ∀ k, 0 ≤ k ∧ k < n → 0 ≤ Znth k l 0 ∧ Znth k l 0 ≤ 10000)
    (hv : RobPrefixValue l len value) : 0 ≤ value ∧ value ≤ 10000 * len := by
  obtain ⟨picks, hlen, hna, rfl⟩ := hv
  have hf : Forall (fun i => 0 ≤ i ∧ i < n) picks :=
    Forall.iff_forall_mem.mpr (fun x hx => by have h := hna.2.2.1.mem hx; omega)
  have hb := rob_plan_value_nonneg_bound l n picks hr hf
  have hc := NoDup_range_length len picks hlen.1 hna.2.1 hna.2.2.1
  omega

theorem rob_prefix_opt_bound_by_len (l : List Int) (len value n : Int)
    (hle : len ≤ n)
    (hr : ∀ k, 0 ≤ k ∧ k < n → 0 ≤ Znth k l 0 ∧ Znth k l 0 ≤ 10000)
    (hv : RobPrefixOpt l len value) : 0 ≤ value ∧ value ≤ 10000 * len :=
  rob_prefix_value_bound_by_len l len value n hle hr (rob_prefix_opt_elim l len value hv).1

theorem nonadj_drop_last_notin (limit : Int) (picks : List Int) (hl : 0 ≤ limit)
    (hna : NonAdjacentIndexList (limit + 1) picks) (hnot : limit ∉ picks) :
    NonAdjacentIndexList limit picks := by
  refine ⟨hl, hna.2.1, Forall.iff_forall_mem.mpr ?_, hna.2.2.2⟩
  intro x hx
  have hb := hna.2.2.1.mem hx
  have hne : x ≠ limit := fun he => hnot (he ▸ hx)
  omega

theorem nonadj_single_zero : NonAdjacentIndexList 1 [0] := by
  refine ⟨by omega, by simp [NoDup], .cons (by omega) .nil, ?_⟩
  intro i j hi hj hne
  simp only [List.mem_singleton] at hi hj
  omega

theorem nonadj_cons_current (i : Int) (picks : List Int) (hi : 0 < i)
    (hna : NonAdjacentIndexList (i - 1) picks) :
    NonAdjacentIndexList (i + 1) (i :: picks) := by
  have hh : i ∉ picks := by intro hx; have hb := hna.2.2.1.mem hx; omega
  refine ⟨by omega, List.nodup_cons.mpr ⟨hh, hna.2.1⟩, .cons (by omega) ?_, ?_⟩
  · apply Forall.iff_forall_mem.mpr
    intro x hx
    have hb := hna.2.2.1.mem hx
    omega
  · intro a b ha hb hne
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      rcases List.mem_cons.mp hb with hb | hb
      · exact (hne hb.symm).elim
      · have h := hna.2.2.1.mem hb
        rw [(Z.abs_eq_iff _).mpr (by omega)]
        omega
    · rcases List.mem_cons.mp hb with hb | hb
      · subst b
        have h := hna.2.2.1.mem ha
        have he : a - i = -(i - a) := by omega
        rw [he, Z.abs_neg, (Z.abs_eq_iff _).mpr (by omega)]
        omega
      · exact hna.2.2.2 a b ha hb hne

theorem nonadj_remove_current (i : Int) (picks : List Int) (hi : 0 < i)
    (hin : i ∈ picks) (hna : NonAdjacentIndexList (i + 1) picks) :
    NonAdjacentIndexList (i - 1) (remove_eqdec i picks) := by
  refine ⟨by omega, NoDup_remove_Z i picks hna.2.1, Forall.iff_forall_mem.mpr ?_, ?_⟩
  · intro x hx
    obtain ⟨hxm, hne⟩ := (remove_mem i x picks).mp hx
    have hb := hna.2.2.1.mem hxm
    have hd := hna.2.2.2 i x hin hxm (Ne.symm hne)
    rw [(Z.abs_eq_iff _).mpr (by omega)] at hd
    omega
  · intro a b ha hb hab
    exact hna.2.2.2 a b ((remove_mem i a picks).mp ha).1
      ((remove_mem i b picks).mp hb).1 hab

theorem remove_zero_range_one_nil (picks : List Int)
    (hf : Forall (fun x => 0 ≤ x ∧ x < 1) picks) : remove_eqdec 0 picks = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨hm, hne⟩ := (remove_mem 0 x picks).mp hx
  have hb := hf.mem hm
  omega

theorem rob_plan_value_remove (l : List Int) (x : Int) (picks : List Int)
    (hn : NoDup picks) (hin : x ∈ picks) :
    RobPlanValue l picks = Znth x l 0 + RobPlanValue l (remove_eqdec x picks) := by
  induction picks with
  | nil => simp at hin
  | cons y ys ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hn
    by_cases hxy : x = y
    · subst y
      simp [remove_eqdec, remove_notin x ys hnot]
    · have hm := (List.mem_cons.mp hin).resolve_left hxy
      have hv := ih hnd hm
      simp only [remove_eqdec, if_neg hxy, plan_cons]
      omega


theorem NonAdjacentIndexList_extend (limit1 limit2 : Int) (picks : List Int)
    (hle : limit1 ≤ limit2) (hna : NonAdjacentIndexList limit1 picks) :
    NonAdjacentIndexList limit2 picks := by
  refine ⟨by have h := hna.1; omega, hna.2.1, Forall.iff_forall_mem.mpr ?_, hna.2.2.2⟩
  intro x hx
  have hb := hna.2.2.1.mem hx
  omega

theorem RobPrefixValue_extend (l : List Int) (len value : Int)
    (hl : len < Zlength l) (hv : RobPrefixValue l len value) :
    RobPrefixValue l (len + 1) value := by
  obtain ⟨picks, hr, hna, hv⟩ := hv
  exact ⟨picks, by omega, NonAdjacentIndexList_extend len (len + 1) picks (by omega) hna, hv⟩

theorem NonAdjacentIndexList_drop_last_notin (i : Int) (picks : List Int) (hi : 0 ≤ i)
    (hna : NonAdjacentIndexList (i + 1) picks) (hn : i ∉ picks) :
    NonAdjacentIndexList i picks := nonadj_drop_last_notin i picks hi hna hn

theorem NonAdjacentIndexList_remove_current (i : Int) (picks : List Int) (hi : 0 < i)
    (hna : NonAdjacentIndexList (i + 1) picks) (hin : i ∈ picks) :
    NonAdjacentIndexList (i - 1) (remove_eqdec i picks) :=
  nonadj_remove_current i picks hi hin hna

theorem RobPlanValue_remove_in (l picks : List Int) (i : Int)
    (hn : NoDup picks) (hin : i ∈ picks) :
    RobPlanValue l picks = Znth i l 0 + RobPlanValue l (remove_eqdec i picks) :=
  rob_plan_value_remove l i picks hn hin

theorem RobPlanValue_limit_one_in (l picks : List Int)
    (hna : NonAdjacentIndexList 1 picks) (hin : 0 ∈ picks) :
    RobPlanValue l picks = Znth 0 l 0 := by
  rw [RobPlanValue_remove_in l picks 0 hna.2.1 hin,
    remove_zero_range_one_nil picks hna.2.2.1, plan_nil, add_zero]

theorem RobPrefixValue_remove_current (l : List Int) (i : Int) (picks : List Int)
    (hi : 0 < i) (hl : i + 1 ≤ Zlength l)
    (hna : NonAdjacentIndexList (i + 1) picks) (hin : i ∈ picks) :
    RobPrefixValue l (i - 1) (RobPlanValue l (remove_eqdec i picks)) :=
  ⟨remove_eqdec i picks, by omega, nonadj_remove_current i picks hi hin hna, rfl⟩

private theorem rob_step_bound (l : List Int) (i prev2 prev1 value : Int)
    (hc : RobPrefixOpt l i prev1)
    (hp : (i = 0 ∧ prev2 = 0) ∨ (0 < i ∧ RobPrefixOpt l (i - 1) prev2))
    (hl : i + 1 ≤ Zlength l) (hv : RobPrefixValue l (i + 1) value) :
    value ≤ prev1 ∨ value ≤ prev2 + Znth i l 0 := by
  obtain ⟨picks, hr, hna, rfl⟩ := hv
  by_cases hin : i ∈ picks
  · right
    rcases hp with ⟨rfl, rfl⟩ | ⟨hi, hp⟩
    · have he := RobPlanValue_limit_one_in l picks hna hin
      omega
    · have hb := (rob_prefix_opt_elim l (i - 1) prev2 hp).2 _
        (RobPrefixValue_remove_current l i picks hi hl hna hin)
      rw [RobPlanValue_remove_in l picks i hna.2.1 hin]
      omega
  · left
    obtain ⟨hcval, hmax⟩ := rob_prefix_opt_elim l i prev1 hc
    obtain ⟨best, hi, _⟩ := hcval
    exact hmax _ ⟨picks, hi, nonadj_drop_last_notin i picks hi.1 hna hin, rfl⟩

theorem rob_prefix_step_take (l : List Int) (i prev2 prev1 : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hs : HouseRobberDPState l i prev2 prev1)
    (ht : prev1 < prev2 + Znth i l 0) : RobPrefixOpt l (i + 1) (prev2 + Znth i l 0) := by
  apply rob_prefix_opt_intro
  · rcases hs.2.2 with ⟨hz, hpz⟩ | ⟨hip, hp⟩
    · subst i prev2
      refine ⟨[0], by omega, nonadj_single_zero, ?_⟩
      simp
    · obtain ⟨picks, hr, hna, hv⟩ := (rob_prefix_opt_elim l (i - 1) prev2 hp).1
      refine ⟨i :: picks, by omega, nonadj_cons_current i picks hip hna, ?_⟩
      simp only [plan_cons]
      omega
  · intro value hv
    have hb := rob_step_bound l i prev2 prev1 value hs.2.1 hs.2.2 (by omega) hv
    omega

theorem house_robber_dp_step_take (l : List Int) (n i prev2 prev1 : Int)
    (hl : Zlength l = n) (hi : 0 ≤ i) (hin : i < n)
    (hs : HouseRobberDPState l i prev2 prev1) (ht : prev2 + Znth i l 0 > prev1) :
    HouseRobberDPState l (i + 1) prev1 (prev2 + Znth i l 0) := by
  refine ⟨by omega, rob_prefix_step_take l i prev2 prev1 (by omega) hs ht, Or.inr ⟨by omega, ?_⟩⟩
  simpa using hs.2.1

theorem house_robber_take_value_bound (l : List Int) (n i prev2 prev1 : Int)
    (hl : Zlength l = n) (hn : n ≤ 100000)
    (hr : ∀ k, 0 ≤ k ∧ k < n → 0 ≤ Znth k l 0 ∧ Znth k l 0 ≤ 10000)
    (hi : 0 ≤ i) (hin : i < n) (hs : HouseRobberDPState l i prev2 prev1) :
    prev2 + Znth i l 0 ≤ 1000000000 := by
  have hb := hr i ⟨hi, hin⟩
  rcases hs.2.2 with ⟨hz, hpz⟩ | ⟨hip, hp⟩
  · omega
  · have hpbound := rob_prefix_opt_bound_by_len l (i - 1) prev2 n (by omega) hr hp
    omega

theorem RobPrefixOpt_step_skip (l : List Int) (i prev2 prev1 : Int)
    (hc : RobPrefixOpt l i prev1)
    (hp : (i = 0 ∧ prev2 = 0) ∨ (0 < i ∧ RobPrefixOpt l (i - 1) prev2))
    (hskip : prev2 + Znth i l 0 ≤ prev1) (hl : i + 1 ≤ Zlength l) :
    RobPrefixOpt l (i + 1) prev1 := by
  apply rob_prefix_opt_intro
  · exact RobPrefixValue_extend l i prev1 (by omega) (rob_prefix_opt_elim l i prev1 hc).1
  · intro value hv
    have hb := rob_step_bound l i prev2 prev1 value hc hp hl hv
    omega

theorem HouseRobberDPState_skip_step (l : List Int) (i prev2 prev1 : Int)
    (hs : HouseRobberDPState l i prev2 prev1)
    (hskip : prev2 + Znth i l 0 ≤ prev1) (hl : i + 1 ≤ Zlength l) :
    HouseRobberDPState l (i + 1) prev1 prev1 := by
  refine ⟨by have h := hs.1; omega,
    RobPrefixOpt_step_skip l i prev2 prev1 hs.2.1 hs.2.2 hskip hl, Or.inr ⟨?_, ?_⟩⟩
  · have h := hs.1; omega
  · simpa using hs.2.1

end SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib
