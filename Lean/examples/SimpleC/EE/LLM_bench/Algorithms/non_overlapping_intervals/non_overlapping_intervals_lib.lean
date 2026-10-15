import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_lib
open AUXLib


open MaxMinLib

def interval : Type := Int × Int
def mk_interval (start finish : Int) : interval := (start, finish)
def interval_start (p : interval) : Int := p.1
def interval_end (p : interval) : Int := p.2
def default_interval : interval := mk_interval 0 1

def PairIntervals (starts ends : List Int) (ps : List interval) : Prop :=
  Zlength starts = Zlength ends ∧ Zlength ps = Zlength starts ∧ ∀ k, (0 ≤ k ∧ k < Zlength starts) →
    Znth k ps default_interval = mk_interval (Znth k starts 0) (Znth k ends 0)

def IntervalBounds (ps : List interval) : Prop :=
  Forall (fun p => -10000 ≤ interval_start p ∧ interval_start p < interval_end p ∧ interval_end p ≤ 10000) ps

def IntervalPermutation : List interval → List interval → Prop := List.Perm

def interval_swap (ps : List interval) (i j : Int) : List interval :=
  replace_Znth j (Znth i ps default_interval) (replace_Znth i (Znth j ps default_interval) ps)

def IntervalSwappedAt (before after : List interval) (i j : Int) : Prop := after = interval_swap before i j

def IntervalSameOutsideRange (before after : List interval) (left right : Int) : Prop :=
  Zlength before = Zlength after ∧ ∀ k, (0 ≤ k ∧ k < Zlength before) → (k < left ∨ right < k) →
    Znth k after default_interval = Znth k before default_interval

def IntervalPartitionedAt (ps : List interval) (low high pivot : Int) : Prop :=
  (low ≤ pivot ∧ pivot ≤ high) ∧
    (∀ k, (low ≤ k ∧ k < pivot) → interval_end (Znth k ps default_interval) ≤ interval_end (Znth pivot ps default_interval)) ∧
    (∀ k, (pivot < k ∧ k ≤ high) → interval_end (Znth pivot ps default_interval) < interval_end (Znth k ps default_interval))

def IntervalsEndSortedRange (ps : List interval) (left right : Int) : Prop :=
  ∀ i j, left ≤ i → i ≤ j → j ≤ right → interval_end (Znth i ps default_interval) ≤ interval_end (Znth j ps default_interval)

def IntervalsEndSorted (ps : List interval) : Prop :=
  ∀ i j, 0 ≤ i → i ≤ j → j < Zlength ps → interval_end (Znth i ps default_interval) ≤ interval_end (Znth j ps default_interval)

def NonOverlappingSchedule (kept : List interval) : Prop :=
  ∀ i j, 0 ≤ i → i < j → j < Zlength kept → interval_end (Znth i kept default_interval) ≤ interval_start (Znth j kept default_interval)

def IntervalSelection (input kept : List interval) : Prop := ∃ removed, List.Perm input (kept ++ removed)

def FeasibleRemovalCount (input : List interval) (removed_count : Int) : Prop :=
  ∃ kept, IntervalSelection input kept ∧ NonOverlappingSchedule kept ∧ removed_count = Zlength input - Zlength kept

def MinimumRemovals (input : List interval) (answer : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (FeasibleRemovalCount input) (fun removed_count => removed_count) answer

def LomutoScanState (before current : List interval) (low high placed scanned pivot_end : Int) : Prop :=
  IntervalPermutation before current ∧ IntervalSameOutsideRange before current low high ∧
    interval_end (Znth high current default_interval) = pivot_end ∧
    (∀ k, (low ≤ k ∧ k ≤ placed) → interval_end (Znth k current default_interval) ≤ pivot_end) ∧
    (∀ k, (placed < k ∧ k < scanned) → pivot_end < interval_end (Znth k current default_interval))

def schedule_finish (kept : List interval) : Int := interval_end (Znth (Zlength kept - 1) kept default_interval)

def GreedyPrefixState (ps : List interval) (processed kept_count last_finish : Int) : Prop :=
  ∃ kept, IntervalSelection (sublist 0 processed ps) kept ∧ NonOverlappingSchedule kept ∧
    Zlength kept = kept_count ∧ 0 < Zlength kept ∧ last_finish = schedule_finish kept ∧
    (∀ alternative, IntervalSelection (sublist 0 processed ps) alternative → NonOverlappingSchedule alternative → Zlength alternative ≤ kept_count) ∧
    (∀ alternative, IntervalSelection (sublist 0 processed ps) alternative → NonOverlappingSchedule alternative → Zlength alternative = kept_count → last_finish ≤ schedule_finish alternative)

private theorem forall_nth {A : Type} {P : A → Prop} (l : List A) (d : A) (i : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  induction hp generalizing i with
  | nil => simp [Zlength] at hi; omega
  | @cons a l ha ht ih =>
    rw [Zlength_cons] at hi
    by_cases he : i = 0
    · subst i; simpa only [Znth0_cons] using ha
    · rw [Znth_cons d i a l (by omega)]
      exact ih (i-1) ⟨by omega, by omega⟩

private theorem nth_mem {A : Type} (l : List A) (d : A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l :=
  forall_nth l d i (Forall.iff_forall_mem.mpr (by intro x hx; exact hx)) hi

private theorem mem_nth {A : Type} (l : List A) (d : A) (x : A) (hx : x ∈ l) :
    ∃ i : Int, (0 ≤ i ∧ i < Zlength l) ∧ Znth i l d = x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨0, ⟨by omega, by rw [Zlength_cons]; have := Zlength_nonneg l; omega⟩, rfl⟩
    · rcases ih hx with ⟨i, hi, he⟩
      refine ⟨i+1, ⟨by omega, by rw [Zlength_cons]; omega⟩, ?_⟩
      rw [Znth_cons d (i+1) a l (by omega)]
      simpa only [show i+1-1 = i by omega] using he


private theorem replace_at_prefix {A : Type} (pre : List A) (x y : A) (rest : List A) :
    replace_Znth (Zlength pre) y (pre++x::rest) = pre++y::rest := by
  rw [replace_Znth_app_r _ _ pre _ (by omega), replace_Znth_nothing _ pre _ (by omega), Int.sub_self]
  rfl

theorem replace_Znth_swap_form__swap_records {A : Type} (l1 l2 l3 : List A) (xi xj : A) :
    replace_Znth (Zlength l1+1+Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1++xi::l2++xj::l3)) = l1++xj::l2++xi::l3 := by
  simp only [List.append_assoc, List.cons_append]
  rw [replace_at_prefix l1 xi xj (l2++xj::l3)]
  have hl := Zlength_nonneg l2
  rw [replace_Znth_app_r _ _ l1 _ (by omega), replace_Znth_nothing _ l1 _ (by omega)]
  rw [show Zlength l1+1+Zlength l2-Zlength l1 = Zlength l2+1 by omega,
    replace_Znth_cons _ _ xj _ (by omega), show Zlength l2+1-1 = Zlength l2 by omega,
    replace_at_prefix l2 xj xi l3]

private theorem cons_replace_perm {A : Type} (ps : List A) (x d : A) (n : Nat) (hn : n < ps.length) :
    (x::ps).Perm (ps.getD n d :: replace_nth n ps x) := by
  induction ps generalizing n with
  | nil => simp at hn
  | cons y ys ih =>
    cases n with
    | zero => exact List.Perm.swap y x ys
    | succ n =>
      change (x::y::ys).Perm (ys.getD n d :: y :: replace_nth n ys x)
      exact (List.Perm.swap y x ys).trans
        ((List.Perm.cons y (ih n (by simpa using hn))).trans (List.Perm.swap _ _ _))

private theorem swap_nth_perm {A : Type} (ps : List A) (d : A) (i j : Nat)
    (hi : i < ps.length) (hj : j < ps.length) :
    ps.Perm (replace_nth j (replace_nth i ps (ps.getD j d)) (ps.getD i d)) := by
  induction ps generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact List.Perm.refl _
      | succ j =>
        exact cons_replace_perm xs x d j (by simpa using hj)
    | succ i =>
      cases j with
      | zero =>
        exact cons_replace_perm xs x d i (by simpa using hi)
      | succ j =>
        exact List.Perm.cons x (ih i j (by simpa using hi) (by simpa using hj))


theorem permutation_swap_Znth_lt__swap_records {A : Type} (l : List A) (i j : Int) (d : A)
    (h : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    List.Perm l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  exact swap_nth_perm l d i.toNat j.toNat
    (by change 0 ≤ i ∧ i < j ∧ j < (l.length : Int) at h; omega)
    (by change 0 ≤ i ∧ i < j ∧ j < (l.length : Int) at h; omega)
theorem replace_nth_comm_Z__swap_records {A : Type} (ni nj : Nat) (ps : List A) (a b : A)
    (hn : ni ≠ nj) : replace_nth nj (replace_nth ni ps a) b = replace_nth ni (replace_nth nj ps b) a := by
  induction ps generalizing ni nj with
  | nil => simp [replace_nth]
  | cons x xs ih =>
    cases ni <;> cases nj <;> simp only [replace_nth]
    · contradiction
    · exact congrArg (List.cons x) (ih _ _ (by omega))

theorem replace_Znth_comm__swap_records {A : Type} (ps : List A) (i j : Int) (a b : A)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : i ≠ j) :
    replace_Znth j b (replace_Znth i a ps) = replace_Znth i a (replace_Znth j b ps) :=
  replace_nth_comm_Z__swap_records i.toNat j.toNat ps a b (by omega)


theorem interval_swap_permutation__swap_records (ps : List interval) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) : IntervalPermutation ps (interval_swap ps i j) :=
  swap_nth_perm ps default_interval i.toNat j.toNat
    (by change 0 ≤ i ∧ i < (ps.length : Int) at hi; omega)
    (by change 0 ≤ j ∧ j < (ps.length : Int) at hj; omega)

theorem interval_swap_bounds__swap_records (ps : List interval) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) (hb : IntervalBounds ps) :
    IntervalBounds (interval_swap ps i j) := hb.perm (interval_swap_permutation__swap_records ps i j hi hj)

private theorem swap_nth_point {A : Type} (l : List A) (d : A) (i j k : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) (hk : 0 ≤ k ∧ k < Zlength l) :
    Znth k (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) d =
      if k = j then Znth i l d else if k = i then Znth j l d else Znth k l d := by
  by_cases he : k = j
  · subst k
    rw [if_pos rfl, Znth_replace_Znth_Same d _ j _ (by rw [Zlength_replace_Znth]; exact hj)]
  · rw [if_neg he, Znth_replace_Znth_Diff d _ j k _ (by rw [Zlength_replace_Znth]; exact hj)
      (by rw [Zlength_replace_Znth]; exact hk) (Ne.symm he)]
    by_cases hei : k = i
    · subst k; rw [if_pos rfl, Znth_replace_Znth_Same d l i _ hi]
    · rw [if_neg hei, Znth_replace_Znth_Diff d l i k _ hi hk (Ne.symm hei)]

theorem pair_intervals_swap__swap_records (starts ends : List Int) (ps : List interval) (i j : Int)
    (hp : PairIntervals starts ends ps) (hi : 0 ≤ i ∧ i < Zlength starts) (hj : 0 ≤ j ∧ j < Zlength starts) :
    PairIntervals (replace_Znth j (Znth i starts 0) (replace_Znth i (Znth j starts 0) starts))
      (replace_Znth j (Znth i ends 0) (replace_Znth i (Znth j ends 0) ends)) (interval_swap ps i j) := by
  obtain ⟨hse, hps, hpoint⟩ := hp
  unfold PairIntervals interval_swap
  simp only [Zlength_replace_Znth]
  refine ⟨hse, hps, ?_⟩
  intro k hk
  rw [swap_nth_point ps default_interval i j k ⟨hi.1, by omega⟩ ⟨hj.1, by omega⟩ ⟨hk.1, by omega⟩,
    swap_nth_point starts 0 i j k hi hj hk,
    swap_nth_point ends 0 i j k ⟨hi.1, by omega⟩ ⟨hj.1, by omega⟩ ⟨hk.1, by omega⟩]
  by_cases hkj : k = j
  · simp only [if_pos hkj]; exact hpoint i hi
  · simp only [if_neg hkj]
    by_cases hki : k = i
    · simp only [if_pos hki]; exact hpoint j hj
    · simp only [if_neg hki]; exact hpoint k hk

theorem pair_intervals_lengths_and_fields__partition_lomuto (starts ends : List Int) (ps : List interval)
    (hp : PairIntervals starts ends ps) : Zlength starts = Zlength ends ∧ Zlength ps = Zlength starts ∧
      ∀ k, (0 ≤ k ∧ k < Zlength starts) →
        interval_start (Znth k ps default_interval) = Znth k starts 0 ∧ interval_end (Znth k ps default_interval) = Znth k ends 0 := by
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro k hk; rw [hp.2.2 k hk]; exact ⟨rfl, rfl⟩

theorem interval_same_outside_range_refl__partition_lomuto (ps : List interval) (low high : Int) :
    IntervalSameOutsideRange ps ps low high := ⟨rfl, fun _ _ _ => rfl⟩

theorem interval_swap_length__partition_lomuto (ps : List interval) (i j : Int) :
    Zlength (interval_swap ps i j) = Zlength ps := by unfold interval_swap; simp only [Zlength_replace_Znth]

theorem interval_swap_Znth_left__partition_lomuto (ps : List interval) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) :
    Znth i (interval_swap ps i j) default_interval = Znth j ps default_interval := by
  unfold interval_swap
  rw [swap_nth_point ps default_interval i j i hi hj hi]
  simp only [if_pos rfl]
  split_ifs with he
  · rw [he]
  · rfl

theorem interval_swap_Znth_right__partition_lomuto (ps : List interval) (i j : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) :
    Znth j (interval_swap ps i j) default_interval = Znth i ps default_interval := by
  unfold interval_swap; rw [swap_nth_point ps default_interval i j j hi hj hj, if_pos rfl]

theorem interval_swap_Znth_other__partition_lomuto (ps : List interval) (i j k : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hj : 0 ≤ j ∧ j < Zlength ps) (hk : 0 ≤ k ∧ k < Zlength ps)
    (hki : k ≠ i) (hkj : k ≠ j) : Znth k (interval_swap ps i j) default_interval = Znth k ps default_interval := by
  unfold interval_swap; rw [swap_nth_point ps default_interval i j k hi hj hk, if_neg hkj, if_neg hki]

theorem interval_same_outside_range_swap_inside__partition_lomuto (before cur : List interval) (low high i j : Int)
    (hs : IntervalSameOutsideRange before cur low high) (hir : low ≤ i ∧ i ≤ high) (hjr : low ≤ j ∧ j ≤ high)
    (hi : 0 ≤ i ∧ i < Zlength cur) (hj : 0 ≤ j ∧ j < Zlength cur) :
    IntervalSameOutsideRange before (interval_swap cur i j) low high := by
  refine ⟨by rw [interval_swap_length__partition_lomuto]; exact hs.1, ?_⟩
  intro k hk hko
  rw [interval_swap_Znth_other__partition_lomuto cur i j k hi hj ⟨hk.1, by rw [← hs.1]; exact hk.2⟩ (by omega) (by omega)]
  exact hs.2 k hk hko

theorem lomuto_scan_init__partition_lomuto (starts ends : List Int) (ps : List interval) (low high : Int)
    (hp : PairIntervals starts ends ps) (hl : 0 ≤ low) (hlh : low ≤ high) (hh : high < Zlength starts) :
    LomutoScanState ps ps low high (low-1) low (Znth high ends 0) := by
  refine ⟨List.Perm.refl _, interval_same_outside_range_refl__partition_lomuto ps low high,
    (pair_intervals_lengths_and_fields__partition_lomuto starts ends ps hp).2.2 high ⟨by omega, hh⟩ |>.2, ?_, ?_⟩
  · intro k hk; omega
  · intro k hk; omega

theorem lomuto_scan_accept__partition_lomuto (before cur after : List interval) (low high placed scanned pivot_end : Int)
    (hl : 0 ≤ low) (hlh : low ≤ high) (hh : high < Zlength cur) (hp : low-1 ≤ placed)
    (hps : placed < scanned) (hsh : scanned < high) (hs : LomutoScanState before cur low high placed scanned pivot_end)
    (hperm : IntervalPermutation cur after) (hswap : IntervalSwappedAt cur after (placed+1) scanned)
    (hguard : interval_end (Znth scanned cur default_interval) ≤ pivot_end) :
    LomutoScanState before after low high (placed+1) (scanned+1) pivot_end := by
  obtain ⟨hperm0, hsame, hpiv, hle, hgt⟩ := hs
  rw [hswap] at hperm ⊢
  have hi : 0 ≤ placed+1 ∧ placed+1 < Zlength cur := ⟨by omega, by omega⟩
  have hj : 0 ≤ scanned ∧ scanned < Zlength cur := ⟨by omega, by omega⟩
  refine ⟨hperm0.trans hperm, interval_same_outside_range_swap_inside__partition_lomuto before cur low high (placed+1) scanned
    hsame ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hi hj, ?_, ?_, ?_⟩
  · rw [interval_swap_Znth_other__partition_lomuto cur _ _ high hi hj ⟨by omega, hh⟩ (by omega) (by omega)]; exact hpiv
  · intro k hk
    by_cases he : k = placed+1
    · rw [he, interval_swap_Znth_left__partition_lomuto cur _ _ hi hj]; exact hguard
    · rw [interval_swap_Znth_other__partition_lomuto cur _ _ k hi hj ⟨by omega, by omega⟩ he (by omega)]
      exact hle k ⟨hk.1, by omega⟩
  · intro k hk
    by_cases he : k = scanned
    · rw [he, interval_swap_Znth_right__partition_lomuto cur _ _ hi hj]; exact hgt _ ⟨by omega, by omega⟩
    · rw [interval_swap_Znth_other__partition_lomuto cur _ _ k hi hj ⟨by omega, by omega⟩ (by omega) he]
      exact hgt k ⟨by omega, by omega⟩

theorem lomuto_scan_skip__partition_lomuto (before cur : List interval) (low high placed scanned pivot_end : Int)
    (hsh : scanned < high) (hs : LomutoScanState before cur low high placed scanned pivot_end)
    (hg : pivot_end < interval_end (Znth scanned cur default_interval)) :
    LomutoScanState before cur low high placed (scanned+1) pivot_end := by
  obtain ⟨hp, hsame, hpiv, hle, hgt⟩ := hs
  refine ⟨hp, hsame, hpiv, hle, ?_⟩
  intro k hk
  by_cases he : k = scanned
  · rw [he]; exact hg
  · exact hgt k ⟨hk.1, by omega⟩

theorem lomuto_scan_finish__partition_lomuto (before cur after : List interval) (low high placed scanned pivot_end : Int)
    (hl : 0 ≤ low) (hlh : low ≤ high) (hh : high < Zlength cur) (hp : low-1 ≤ placed)
    (hps : placed < scanned) (hsh : scanned ≤ high) (hhs : scanned ≥ high)
    (hs : LomutoScanState before cur low high placed scanned pivot_end)
    (hperm : IntervalPermutation cur after) (hswap : IntervalSwappedAt cur after (placed+1) high) :
    IntervalPermutation before after ∧ IntervalSameOutsideRange before after low high ∧ IntervalPartitionedAt after low high (placed+1) := by
  have he : scanned = high := by omega
  subst scanned
  obtain ⟨hperm0, hsame, hpiv, hle, hgt⟩ := hs
  rw [hswap] at hperm ⊢
  have hi : 0 ≤ placed+1 ∧ placed+1 < Zlength cur := ⟨by omega, by omega⟩
  have hj : 0 ≤ high ∧ high < Zlength cur := ⟨by omega, hh⟩
  have hpa : interval_end (Znth (placed+1) (interval_swap cur (placed+1) high) default_interval) = pivot_end := by
    rw [interval_swap_Znth_left__partition_lomuto cur _ _ hi hj]; exact hpiv
  refine ⟨hperm0.trans hperm, interval_same_outside_range_swap_inside__partition_lomuto before cur low high (placed+1) high
    hsame ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hi hj, ⟨by omega, by omega⟩, ?_, ?_⟩
  · intro k hk
    rw [hpa, interval_swap_Znth_other__partition_lomuto cur _ _ k hi hj ⟨by omega, by omega⟩ (by omega) (by omega)]
    exact hle k ⟨hk.1, by omega⟩
  · intro k hk
    rw [hpa]
    by_cases he : k = high
    · rw [he, interval_swap_Znth_right__partition_lomuto cur _ _ hi hj]; exact hgt _ ⟨by omega, by omega⟩
    · rw [interval_swap_Znth_other__partition_lomuto cur _ _ k hi hj ⟨by omega, by omega⟩ (by omega) he]
      exact hgt k ⟨by omega, by omega⟩

theorem Forall_Znth_interval__quicksort_left (P : interval → Prop) (l : List interval) (i : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l default_interval) :=
  forall_nth l default_interval i hp hi

private theorem sub_length {A : Type} (l : List A) (lo hi : Int)
    (hr : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l) : Zlength (sublist lo hi l) = hi-lo :=
  ListLib.Zlength_sublist lo hi l hr hh

private theorem sub_mem_index {A : Type} (l : List A) (d x : A) (lo hi : Int)
    (hr : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l) (hx : x ∈ sublist lo hi l) :
    ∃ k, (lo ≤ k ∧ k < hi) ∧ Znth k l d = x := by
  obtain ⟨i, hi', he⟩ := mem_nth _ d x hx
  rw [sub_length l lo hi hr hh] at hi'
  rw [Znth_sublist d lo i hi l hr.1 hi'] at he
  exact ⟨i+lo, ⟨by omega, by omega⟩, he⟩

private theorem sub_nth_mem {A : Type} (l : List A) (d : A) (lo hi k : Int)
    (hr : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l) (hk : lo ≤ k ∧ k < hi) :
    Znth k l d ∈ sublist lo hi l := by
  have hn := nth_mem (sublist lo hi l) d (k-lo) (by rw [sub_length l lo hi hr hh]; omega)
  rw [Znth_sublist d lo (k-lo) hi l hr.1 ⟨by omega, by omega⟩] at hn
  simpa only [Int.sub_add_cancel] using hn

theorem Forall_sublist_interval__quicksort_left (P : interval → Prop) (l : List interval) (lo hi : Int)
    (hr : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l)
    (hp : ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l default_interval)) : Forall P (sublist lo hi l) := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨k, hk, he⟩ := sub_mem_index l default_interval x lo hi hr hh hx
  rw [← he]; exact hp k hk

theorem sublist_interval_eq_from_Znth__quicksort_left (l1 l2 : List interval) (lo hi : Int)
    (hl : Zlength l1 = Zlength l2) (hr : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l1)
    (hp : ∀ k, (lo ≤ k ∧ k < hi) → Znth k l1 default_interval = Znth k l2 default_interval) :
    sublist lo hi l1 = sublist lo hi l2 := by
  apply (ListLib.list_eq_ext _ _ default_interval).mpr
  have hlen1 := sub_length l1 lo hi hr hh
  have hlen2 := sub_length l2 lo hi hr (by omega)
  refine ⟨hlen1.trans hlen2.symm, ?_⟩
  intro i hi'
  change 0 ≤ i ∧ i < Zlength (sublist lo hi l1) at hi'
  rw [hlen1] at hi'
  change Znth i (sublist lo hi l1) default_interval = Znth i (sublist lo hi l2) default_interval
  rw [Znth_sublist default_interval lo i hi l1 hr.1 hi', Znth_sublist default_interval lo i hi l2 hr.1 hi']
  exact hp _ ⟨by omega, by omega⟩

theorem list_interval_decompose_sublist__quicksort_left (l : List interval) (lo hi : Int)
    (hr : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l) :
    l = sublist 0 lo l ++ (sublist lo hi l ++ sublist hi (Zlength l) l) := by
  rw [← sublist_split lo (Zlength l) hi l hr ⟨hh, le_refl _⟩,
    ← sublist_split 0 (Zlength l) lo l ⟨le_refl _, hr.1⟩ ⟨by omega, le_refl _⟩,
    sublist_self l _ rfl]

theorem interval_same_outside_prefix__quicksort_left (l l1 : List interval) (left right : Int)
    (hs : IntervalSameOutsideRange l l1 left right) (hr : 0 ≤ left ∧ left ≤ Zlength l) :
    sublist 0 left l1 = sublist 0 left l := by
  apply sublist_interval_eq_from_Znth__quicksort_left l1 l 0 left hs.1.symm ⟨le_refl _, hr.1⟩ (by rw [← hs.1]; exact hr.2)
  intro k hk; exact hs.2 k ⟨hk.1, by omega⟩ (Or.inl hk.2)

theorem interval_same_outside_suffix__quicksort_left (l l1 : List interval) (left right : Int)
    (hs : IntervalSameOutsideRange l l1 left right) (hr : 0 ≤ right+1 ∧ right+1 ≤ Zlength l) :
    sublist (right+1) (Zlength l1) l1 = sublist (right+1) (Zlength l) l := by
  rw [← hs.1]
  apply sublist_interval_eq_from_Znth__quicksort_left l1 l _ _ hs.1.symm hr (by rw [hs.1])
  intro k hk; exact hs.2 k ⟨by omega, hk.2⟩ (Or.inr (by omega))

theorem interval_middle_permutation__quicksort_left (l l1 : List interval) (left right : Int)
    (hp : IntervalPermutation l l1) (hs : IntervalSameOutsideRange l l1 left right)
    (hr : 0 ≤ left ∧ left ≤ right+1) (hh : right+1 ≤ Zlength l) :
    List.Perm (sublist left (right+1) l) (sublist left (right+1) l1) := by
  have hpre := interval_same_outside_prefix__quicksort_left l l1 left right hs ⟨hr.1, by omega⟩
  have hsuf := interval_same_outside_suffix__quicksort_left l l1 left right hs ⟨by omega, hh⟩
  have h1 := list_interval_decompose_sublist__quicksort_left l left (right+1) hr hh
  have h2 := list_interval_decompose_sublist__quicksort_left l1 left (right+1) hr (by rw [← hs.1]; exact hh)
  change List.Perm l l1 at hp
  rw [h1, h2, hpre, hsuf] at hp
  exact (List.perm_append_right_iff _).mp ((List.perm_append_left_iff _).mp hp)

private theorem sub_forall_transfer (P : interval → Prop) (before after : List interval) (lo hi : Int)
    (hl : Zlength before = Zlength after) (hr : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength before)
    (hp : List.Perm (sublist lo hi before) (sublist lo hi after))
    (hpoint : ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k before default_interval))
    (k : Int) (hk : lo ≤ k ∧ k < hi) : P (Znth k after default_interval) := by
  have hforall := (Forall_sublist_interval__quicksort_left P before lo hi hr hh hpoint).perm hp
  exact hforall.mem (sub_nth_mem after default_interval lo hi k hr (by rw [← hl]; exact hh) hk)

theorem partition_preserved_by_left_sort__quicksort_left (before after : List interval) (low high pivot : Int)
    (hp : IntervalPermutation before after) (hs : IntervalSameOutsideRange before after low (pivot-1))
    (hl : 0 ≤ low) (hh : high < Zlength before) (hpart : IntervalPartitionedAt before low high pivot) :
    IntervalPartitionedAt after low high pivot := by
  obtain ⟨hr, hleft, hright⟩ := hpart
  have hpi := hs.2 pivot ⟨by omega, by omega⟩ (Or.inr (by omega))
  refine ⟨hr, ?_, ?_⟩
  · intro k hk
    rw [hpi]
    have hmid := interval_middle_permutation__quicksort_left before after low (pivot-1) hp hs ⟨hl, by omega⟩ (by omega)
    simp only [show pivot-1+1 = pivot by omega] at hmid
    exact sub_forall_transfer (fun q => interval_end q ≤ interval_end (Znth pivot before default_interval)) before after low pivot hs.1 ⟨hl, hr.1⟩ (by omega) hmid hleft k hk
  · intro k hk
    rw [hpi, hs.2 k ⟨by omega, by omega⟩ (Or.inr (by omega))]
    exact hright k hk

theorem outside_range_compose_nested__quicksort_left (original middle final : List interval) (left right nested_right : Int)
    (h1 : IntervalSameOutsideRange original middle left right) (h2 : IntervalSameOutsideRange middle final left nested_right)
    (hn : nested_right ≤ right) : IntervalSameOutsideRange original final left right := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  intro k hk hko
  rw [h2.2 k ⟨hk.1, by rw [← h1.1]; exact hk.2⟩ (by rcases hko with h | h; exact Or.inl h; exact Or.inr (by omega))]
  exact h1.2 k hk hko

theorem sorted_range_empty__quicksort_left (ps : List interval) (left right : Int) (hr : right < left) :
    IntervalsEndSortedRange ps left right := by intro i j hi hij hj; omega

theorem outside_range_compose_nested__quicksort_finish (before middle after : List interval) (left inner_left right : Int)
    (hi : left ≤ inner_left) (h1 : IntervalSameOutsideRange before middle left right)
    (h2 : IntervalSameOutsideRange middle after inner_left right) : IntervalSameOutsideRange before after left right := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  intro k hk hko
  rw [h2.2 k ⟨hk.1, by rw [← h1.1]; exact hk.2⟩ (by rcases hko with h | h; exact Or.inl (by omega); exact Or.inr h)]
  exact h1.2 k hk hko

theorem Forall_interval_permutation__quicksort_finish (P : interval → Prop) (l1 l2 : List interval)
    (hp : IntervalPermutation l1 l2) (hf : Forall P l1) : Forall P l2 := hf.perm hp

theorem Forall_Znth_interval__quicksort_finish (P : interval → Prop) (l : List interval) (i : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l default_interval) :=
  Forall_Znth_interval__quicksort_left P l i hp hi

theorem Forall_sublist_interval_by_Znth__quicksort_finish (P : interval → Prop) (l : List interval) (lo hi : Int)
    (hr : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l)
    (hp : ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l default_interval)) : Forall P (sublist lo hi l) :=
  Forall_sublist_interval__quicksort_left P l lo hi hr hh hp

theorem sublist_eq_from_Znth_interval__quicksort_finish (l1 l2 : List interval) (lo hi : Int)
    (hl : Zlength l1 = Zlength l2) (hr : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l1)
    (hp : ∀ k, (lo ≤ k ∧ k < hi) → Znth k l1 default_interval = Znth k l2 default_interval) :
    sublist lo hi l1 = sublist lo hi l2 := sublist_interval_eq_from_Znth__quicksort_left l1 l2 lo hi hl hr hh hp

theorem list_decompose_sublist_interval__quicksort_finish (l : List interval) (lo hi : Int)
    (hr : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength l) :
    l = sublist 0 lo l ++ (sublist lo hi l ++ sublist hi (Zlength l) l) :=
  list_interval_decompose_sublist__quicksort_left l lo hi hr hh

theorem same_outside_prefix_interval__quicksort_finish (l1 l2 : List interval) (left right : Int)
    (hs : IntervalSameOutsideRange l1 l2 left right) (hr : 0 ≤ left ∧ left ≤ Zlength l1) :
    sublist 0 left l2 = sublist 0 left l1 := interval_same_outside_prefix__quicksort_left l1 l2 left right hs hr

theorem same_outside_suffix_interval__quicksort_finish (l1 l2 : List interval) (left right : Int)
    (hs : IntervalSameOutsideRange l1 l2 left right) (hr : 0 ≤ right+1 ∧ right+1 ≤ Zlength l1) :
    sublist (right+1) (Zlength l2) l2 = sublist (right+1) (Zlength l1) l1 :=
  interval_same_outside_suffix__quicksort_left l1 l2 left right hs hr

theorem middle_permutation_interval__quicksort_finish (l1 l2 : List interval) (left right : Int)
    (hp : IntervalPermutation l1 l2) (hs : IntervalSameOutsideRange l1 l2 left right)
    (hr : 0 ≤ left ∧ left ≤ right+1) (hh : right+1 ≤ Zlength l1) :
    IntervalPermutation (sublist left (right+1) l1) (sublist left (right+1) l2) :=
  interval_middle_permutation__quicksort_left l1 l2 left right hp hs hr hh

theorem right_sort_preserves_left_partition__quicksort_finish (before after : List interval) (left right pivot : Int)
    (hp : IntervalPermutation before after) (hs : IntervalSameOutsideRange before after (pivot+1) right)
    (hl : 0 ≤ left) (hpiv : pivot ≤ right) (hr : right < Zlength before)
    (hpart : IntervalPartitionedAt before left right pivot) : IntervalPartitionedAt after left right pivot := by
  obtain ⟨hrange, hleft, hright⟩ := hpart
  have hpi := hs.2 pivot ⟨by omega, by omega⟩ (Or.inl (by omega))
  refine ⟨hrange, ?_, ?_⟩
  · intro k hk
    rw [hpi, hs.2 k ⟨by omega, by omega⟩ (Or.inl (by omega))]
    exact hleft k hk
  · intro k hk
    rw [hpi]
    have hmid := interval_middle_permutation__quicksort_left before after (pivot+1) right hp hs ⟨by omega, by omega⟩ (by omega)
    exact sub_forall_transfer (fun q => interval_end (Znth pivot before default_interval) < interval_end q) before after (pivot+1) (right+1) hs.1 ⟨by omega, by omega⟩ (by omega) hmid
      (fun j hj => hright j ⟨by omega, by omega⟩) k ⟨by omega, by omega⟩

theorem sorted_range_preserved_on_left__quicksort_finish (before after : List interval) (left right pivot : Int)
    (hs : IntervalSameOutsideRange before after (pivot+1) right) (hl : 0 ≤ left) (hp : pivot ≤ right)
    (hr : right < Zlength before) (hsorted : IntervalsEndSortedRange before left (pivot-1)) :
    IntervalsEndSortedRange after left (pivot-1) := by
  intro i j hi hij hj
  rw [hs.2 i ⟨by omega, by omega⟩ (Or.inl (by omega)), hs.2 j ⟨by omega, by omega⟩ (Or.inl (by omega))]
  exact hsorted i j hi hij hj

theorem partition_merge_sorted_ranges__quicksort_finish (ps : List interval) (left right pivot : Int)
    (hp : IntervalPartitionedAt ps left right pivot) (hl : IntervalsEndSortedRange ps left (pivot-1))
    (hr : IntervalsEndSortedRange ps (pivot+1) right) : IntervalsEndSortedRange ps left right := by
  obtain ⟨hpr, hpl, hpright⟩ := hp
  intro i j hi hij hj
  by_cases hjl : j < pivot
  · exact hl i j hi hij (by omega)
  · by_cases hil : i < pivot
    · have h1 := hpl i ⟨hi, hil⟩
      by_cases hje : j = pivot
      · rw [hje]; exact h1
      · have h2 := hpright j ⟨by omega, hj⟩; omega
    · by_cases hie : i = pivot
      · rw [hie]
        by_cases hje : j = pivot
        · rw [hje]
        · have := hpright j ⟨by omega, hj⟩; omega
      · exact hr i j (by omega) hij hj

theorem sorted_range_trivial__quicksort_finish (ps : List interval) (left right : Int) (hlr : left ≥ right) :
    IntervalsEndSortedRange ps left right := by
  intro i j hi hij hj
  have he : i = j := by omega
  rw [he]

theorem same_outside_refl__quicksort_finish (ps : List interval) (left right : Int) :
    IntervalSameOutsideRange ps ps left right := interval_same_outside_range_refl__partition_lomuto ps left right

theorem sorted_full_range__quicksort_finish (ps : List interval) (n : Int) (hl : Zlength ps = n)
    (hs : IntervalsEndSortedRange ps 0 (n-1)) : IntervalsEndSorted ps := by
  intro i j hi hij hj; exact hs i j hi hij (by omega)

-- Reached dependency: Coq.Sorting.Sorted.StronglySorted, with source constructor order.
inductive StronglySorted {A : Type} (R : A → A → Prop) : List A → Prop where
  | SSorted_nil : StronglySorted R []
  | SSorted_cons (a : A) {l : List A} : StronglySorted R l → Forall (R a) l → StronglySorted R (a :: l)

@[match_pattern] abbrev SSorted_nil {A : Type} (R : A → A → Prop) : StronglySorted R [] := .SSorted_nil
@[match_pattern] abbrev SSorted_cons {A : Type} {R : A → A → Prop} (a : A) {l : List A}
    (ht : StronglySorted R l) (hh : Forall (R a) l) : StronglySorted R (a :: l) := .SSorted_cons a ht hh

private theorem strongly_pairwise {A : Type} (R : A → A → Prop) (l : List A) : StronglySorted R l ↔ l.Pairwise R := by
  induction l with
  | nil => exact ⟨fun _ => .nil, fun _ => .SSorted_nil⟩
  | cons x xs ih =>
    constructor
    · intro h
      cases h with
      | SSorted_cons _ ht hh => exact .cons (fun y hy => Forall.mem hh hy) (ih.mp ht)
    · intro h
      obtain ⟨hh, ht⟩ := List.pairwise_cons.mp h
      exact .SSorted_cons x (ih.mpr ht) (Forall.iff_forall_mem.mpr hh)

theorem forall_znth__greedy_prefix (A : Type) (P : A → Prop) (default : A) (values : List A) :
    Forall P values ↔ ∀ index, (0 ≤ index ∧ index < Zlength values) → P (Znth index values default) := by
  rw [Forall.iff_forall_mem]
  constructor
  · intro h idx hi; exact h _ (nth_mem values default idx hi)
  · intro h x hx
    obtain ⟨idx, hi, he⟩ := mem_nth values default x hx
    rw [← he]; exact h idx hi

private theorem strongly_cons (R : interval → interval → Prop) (head : interval) (tail : List interval) :
    StronglySorted R (head :: tail) ↔ Forall (R head) tail ∧ StronglySorted R tail := by
  constructor
  · intro h; cases h with | SSorted_cons _ ht hh => exact ⟨hh, ht⟩
  · intro h; exact .SSorted_cons head h.2 h.1

private theorem strongly_index (R : interval → interval → Prop) (values : List interval) :
    StronglySorted R values ↔ ∀ left right, 0 ≤ left → left < right → right < Zlength values → R (Znth left values default_interval) (Znth right values default_interval) := by
  induction values with
  | nil => constructor <;> intro h; intro l r hl ho hr; have : Zlength ([] : List interval) = 0 := rfl; omega; exact .SSorted_nil
  | cons x xs ih =>
    rw [strongly_cons, forall_znth__greedy_prefix interval (R x) default_interval xs, ih]
    constructor
    · intro ⟨hh, ht⟩ l r hl ho hr
      by_cases he : l = 0
      · subst l
        rw [Znth0_cons, Znth_cons default_interval r x xs (by omega)]
        exact hh (r-1) (by simp only [Zlength, Int.ofNat_eq_coe, List.length_cons] at *; omega)
      · rw [Znth_cons default_interval l x xs (by omega), Znth_cons default_interval r x xs (by omega)]
        exact ht (l-1) (r-1) (by omega) (by omega) (by simp only [Zlength, Int.ofNat_eq_coe, List.length_cons] at *; omega)
    · intro h
      constructor
      · intro idx hi
        have hs := h 0 (idx+1) (by omega) (by omega) (by simp only [Zlength, Int.ofNat_eq_coe, List.length_cons] at *; omega)
        simpa only [Znth0_cons, Znth_cons default_interval (idx+1) x xs (by omega), Int.add_sub_cancel] using hs
      · intro l r hl ho hr
        have hs := h (l+1) (r+1) (by omega) (by omega) (by simp only [Zlength, Int.ofNat_eq_coe, List.length_cons] at *; omega)
        simpa only [Znth_cons default_interval (l+1) x xs (by omega), Znth_cons default_interval (r+1) x xs (by omega), Int.add_sub_cancel] using hs


theorem nonoverlap_strongly_sorted__greedy_prefix (xs : List interval) :
    NonOverlappingSchedule xs ↔ StronglySorted (fun x y => interval_end x ≤ interval_start y) xs :=
  (strongly_index (fun x y => interval_end x ≤ interval_start y) xs).symm

private theorem nonoverlap_pairwise (xs : List interval) :
    NonOverlappingSchedule xs ↔ xs.Pairwise (fun x y => interval_end x ≤ interval_start y) :=
  (nonoverlap_strongly_sorted__greedy_prefix xs).trans (strongly_pairwise _ xs)

theorem nonoverlap_remove_middle__greedy_prefix (left : List interval) (pivot : interval) (right : List interval)
    (hn : NonOverlappingSchedule (left++pivot::right)) : NonOverlappingSchedule (left++right) := by
  apply (nonoverlap_pairwise _).mpr
  exact List.Pairwise.sublist ((List.Sublist.refl left).append ((List.Sublist.refl right).cons pivot)) ((nonoverlap_pairwise _).mp hn)

private theorem perm_remove_middle {A : Type} (old pre post : List A) (p : A)
    (hp : List.Perm (old++[p]) (pre++p::post)) : List.Perm old (pre++post) := by
  have hh : List.Perm (p::old) (p::(pre++post)) :=
    List.perm_append_comm.trans (hp.trans List.perm_middle)
  exact hh.cons_inv

theorem interval_selection_extend_cases__greedy_prefix (old : List interval) (p : interval) (alternative : List interval)
    (hs : IntervalSelection (old++[p]) alternative) : IntervalSelection old alternative ∨
      ∃ left right, alternative = left++p::right ∧ IntervalSelection old (left++right) := by
  obtain ⟨removed, hp⟩ := hs
  have hm : p ∈ alternative++removed := hp.mem_iff.mp (by simp)
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    right; refine ⟨pre, post, he, removed, ?_⟩
    rw [he] at hp
    simp only [List.append_assoc, List.cons_append] at hp
    have hh := perm_remove_middle old pre (post++removed) p hp
    simpa only [List.append_assoc] using hh
  · obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    left; refine ⟨pre++post, ?_⟩
    rw [he] at hp
    have hh : List.Perm (old++[p]) ((alternative++pre)++p::post) := by simpa only [List.append_assoc] using hp
    simpa only [List.append_assoc] using perm_remove_middle old (alternative++pre) post p hh

theorem interval_selection_extend_schedule_cases__greedy_prefix (old : List interval) (p : interval) (alternative : List interval)
    (hs : IntervalSelection (old++[p]) alternative) (hn : NonOverlappingSchedule alternative) :
    (IntervalSelection old alternative ∧ NonOverlappingSchedule alternative) ∨
    ∃ left right, alternative = left++p::right ∧ IntervalSelection old (left++right) ∧ NonOverlappingSchedule (left++right) := by
  rcases interval_selection_extend_cases__greedy_prefix old p alternative hs with hs | ⟨l,r,he,hs⟩
  · exact Or.inl ⟨hs, hn⟩
  · exact Or.inr ⟨l,r,he,hs,nonoverlap_remove_middle__greedy_prefix l p r (by rw [← he]; exact hn)⟩

theorem prefix_snoc__greedy_prefix (ps : List interval) (i : Int) (hi : 0 ≤ i ∧ i < Zlength ps) :
    sublist 0 (i+1) ps = sublist 0 i ps++[Znth i ps default_interval] := by
  rw [sublist_split 0 (i+1) i ps ⟨le_refl _, hi.1⟩ ⟨by omega, by omega⟩, sublist_single default_interval i ps hi]

theorem interval_bounds_prefix__greedy_prefix (ps : List interval) (n : Int)
    (hn : 0 ≤ n ∧ n ≤ Zlength ps) (hb : IntervalBounds ps) : IntervalBounds (sublist 0 n ps) := by
  apply Forall_sublist_interval__quicksort_left _ ps 0 n ⟨le_refl _, hn.1⟩ hn.2
  intro k hk; exact forall_nth ps default_interval k hb ⟨hk.1, by omega⟩

theorem interval_bounds_selected__greedy_prefix (input kept : List interval)
    (hb : IntervalBounds input) (hs : IntervalSelection input kept) : IntervalBounds kept := by
  obtain ⟨removed, hp⟩ := hs
  apply Forall.iff_forall_mem.mpr
  intro p hp'; exact hb.mem (hp.mem_iff.mpr (List.mem_append_left _ hp'))

theorem selected_member_end_le_current__greedy_prefix (ps : List interval) (processed : Int) (selected : List interval) (q : interval)
    (hi : 0 ≤ processed ∧ processed < Zlength ps) (hs : IntervalsEndSorted ps)
    (hsel : IntervalSelection (sublist 0 processed ps) selected) (hq : q ∈ selected) :
    interval_end q ≤ interval_end (Znth processed ps default_interval) := by
  obtain ⟨removed, hp⟩ := hsel
  have hmem := hp.mem_iff.mpr (List.mem_append_left removed hq)
  obtain ⟨k,hk,he⟩ := sub_mem_index ps default_interval q 0 processed ⟨le_refl _, hi.1⟩ (by omega) hmem
  rw [← he]; exact hs k processed hk.1 (by omega) hi.2

theorem nonoverlap_member_end_le_finish__greedy_prefix (xs : List interval) (p : interval)
    (hn : NonOverlappingSchedule xs) (hb : IntervalBounds xs) (hp : p ∈ xs) : interval_end p ≤ schedule_finish xs := by
  obtain ⟨k,hk,he⟩ := mem_nth xs default_interval p hp
  unfold schedule_finish
  by_cases hlast : k = Zlength xs-1
  · rw [← hlast, he]
  · have hno := hn k (Zlength xs-1) hk.1 (by omega) (by omega)
    have hlastbound := forall_nth xs default_interval (Zlength xs-1) hb ⟨by omega, by omega⟩
    rw [he] at hno
    omega

theorem interval_selection_append__greedy_prefix (old kept : List interval) (p : interval)
    (hs : IntervalSelection old kept) : IntervalSelection (old++[p]) (kept++[p]) := by
  obtain ⟨removed,hp⟩ := hs
  refine ⟨removed, ?_⟩
  have hh := (hp.append (List.Perm.refl [p])).trans
    (by simpa only [List.append_assoc] using (List.Perm.refl kept).append (List.perm_append_comm (l₁ := removed) (l₂ := [p])))
  simpa only [List.append_assoc] using hh

theorem nonoverlap_append__greedy_prefix (kept : List interval) (p : interval)
    (hn : NonOverlappingSchedule kept) (hb : IntervalBounds kept) (hp : 0 < Zlength kept)
    (hf : schedule_finish kept ≤ interval_start p) : NonOverlappingSchedule (kept++[p]) := by
  apply (nonoverlap_pairwise _).mpr
  apply List.pairwise_append.mpr
  refine ⟨(nonoverlap_pairwise _).mp hn, by simp, ?_⟩
  intro x hx y hy
  have he : y = p := by simpa using hy
  subst y
  exact le_trans (nonoverlap_member_end_le_finish__greedy_prefix kept x hn hb hx) hf

theorem schedule_finish_snoc__greedy_prefix (xs : List interval) (p : interval) : schedule_finish (xs++[p]) = interval_end p := by
  unfold schedule_finish
  rw [Zlength_app, Zlength_cons, Zlength_nil, show Zlength xs+(0+1)-1 = Zlength xs by omega,
    app_Znth2 default_interval xs [p] _ (le_refl _), Int.sub_self, Znth0_cons]

theorem nonoverlap_snoc_previous_finish__greedy_prefix (xs : List interval) (p : interval)
    (hn : NonOverlappingSchedule (xs++[p])) (hp : 0 < Zlength xs) : schedule_finish xs ≤ interval_start p := by
  have hh := hn (Zlength xs-1) (Zlength xs) (by omega) (by omega) (by rw [Zlength_app, Zlength_cons, Zlength_nil]; omega)
  have ha : Znth (Zlength xs-1) (xs++[p]) default_interval = Znth (Zlength xs-1) xs default_interval :=
    ListLib.app_Znth1 default_interval xs [p] _ (show 0 ≤ Zlength xs-1 ∧ Zlength xs-1 < Zlength xs from ⟨by omega, by omega⟩)
  rw [ha,
    app_Znth2 default_interval xs [p] _ (le_refl _), Int.sub_self, Znth0_cons] at hh
  exact hh

theorem latest_interval_right_nil__greedy_prefix (left : List interval) (p : interval) (right : List interval)
    (hn : NonOverlappingSchedule (left++p::right)) (hb : IntervalBounds right)
    (he : ∀ q ∈ right, interval_end q ≤ interval_end p) : right = [] := by
  have hh := (List.pairwise_append.mp ((nonoverlap_pairwise _).mp hn)).2.1
  have hp := (List.pairwise_cons.mp hh).1
  cases right with
  | nil => rfl
  | cons q qs =>
    have h1 := hp q (by simp)
    have h2 := he q (by simp)
    have h3 : -10000 ≤ interval_start q ∧ interval_start q < interval_end q ∧ interval_end q ≤ 10000 := hb.mem (by simp)
    omega

theorem greedy_prefix_accept__greedy_prefix (ps : List interval) (i kept_count last_finish : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hb : IntervalBounds ps)
    (hs : GreedyPrefixState ps i kept_count last_finish)
    (ha : last_finish ≤ interval_start (Znth i ps default_interval)) :
    GreedyPrefixState ps (i+1) (kept_count+1) (interval_end (Znth i ps default_interval)) := by
  obtain ⟨kept,hsel,hno,hlen,hpos,hlast,hmax,hfront⟩ := hs
  let p := Znth i ps default_interval
  have hprefix := prefix_snoc__greedy_prefix ps i hi
  have hbprefix := interval_bounds_prefix__greedy_prefix ps i ⟨hi.1, by omega⟩ hb
  have hbkept := interval_bounds_selected__greedy_prefix _ kept hbprefix hsel
  have hbnew := interval_bounds_prefix__greedy_prefix ps (i+1) ⟨by omega, by omega⟩ hb
  refine ⟨kept++[p], ?_, nonoverlap_append__greedy_prefix kept p hno hbkept hpos (by rw [← hlast]; exact ha),
    ?_, ?_, (schedule_finish_snoc__greedy_prefix kept p).symm, ?_, ?_⟩
  · rw [hprefix]; exact interval_selection_append__greedy_prefix _ kept p hsel
  · rw [Zlength_app, Zlength_cons, Zlength_nil]; omega
  · rw [Zlength_app, Zlength_cons, Zlength_nil]; omega
  · intro alt hsa hna
    rw [hprefix] at hsa
    rcases interval_selection_extend_schedule_cases__greedy_prefix _ p alt hsa hna with ⟨hsold,hnold⟩ | ⟨l,r,he,hsold,hnold⟩
    · have := hmax alt hsold hnold; omega
    · have hh := hmax (l++r) hsold hnold
      rw [he, Zlength_app, Zlength_cons]
      rw [Zlength_app] at hh; omega
  · intro alt hsa hna hla
    have hba := interval_bounds_selected__greedy_prefix _ alt hbnew hsa
    rw [hprefix] at hsa
    rcases interval_selection_extend_schedule_cases__greedy_prefix _ p alt hsa hna with ⟨hsold,hnold⟩ | ⟨l,r,he,hsold,hnold⟩
    · have := hmax alt hsold hnold; omega
    · exact nonoverlap_member_end_le_finish__greedy_prefix alt p hna hba (by rw [he]; simp)

theorem interval_selection_retain__greedy_prefix (old kept : List interval) (p : interval)
    (hs : IntervalSelection old kept) : IntervalSelection (old++[p]) kept := by
  obtain ⟨removed,hp⟩ := hs
  refine ⟨p::removed, ?_⟩
  have hh := (hp.append (List.Perm.refl [p])).trans
    (by simpa only [List.append_assoc] using (List.Perm.refl kept).append (List.perm_append_comm (l₁ := removed) (l₂ := [p])))
  simpa only [List.append_assoc] using hh

theorem selected_finish_end_le_current__greedy_prefix (ps : List interval) (processed : Int) (kept : List interval)
    (hi : 0 ≤ processed ∧ processed < Zlength ps) (hs : IntervalsEndSorted ps)
    (hsel : IntervalSelection (sublist 0 processed ps) kept) (hp : 0 < Zlength kept) :
    schedule_finish kept ≤ interval_end (Znth processed ps default_interval) :=
  selected_member_end_le_current__greedy_prefix ps processed kept _ hi hs hsel
    (nth_mem kept default_interval (Zlength kept-1) ⟨by omega, by omega⟩)

theorem greedy_prefix_skip__greedy_prefix (ps : List interval) (i kept_count last_finish : Int)
    (hi : 0 ≤ i ∧ i < Zlength ps) (hb : IntervalBounds ps) (hsorted : IntervalsEndSorted ps)
    (hs : GreedyPrefixState ps i kept_count last_finish)
    (hskip : interval_start (Znth i ps default_interval) < last_finish) :
    GreedyPrefixState ps (i+1) kept_count last_finish := by
  obtain ⟨kept,hsel,hno,hlen,hpos,hlast,hmax,hfront⟩ := hs
  let p := Znth i ps default_interval
  have hprefix := prefix_snoc__greedy_prefix ps i hi
  have hbprefix := interval_bounds_prefix__greedy_prefix ps i ⟨hi.1, by omega⟩ hb
  have hbnew := interval_bounds_prefix__greedy_prefix ps (i+1) ⟨by omega, by omega⟩ hb
  have hkfinish := selected_finish_end_le_current__greedy_prefix ps i kept hi hsorted hsel hpos
  refine ⟨kept, ?_, hno, hlen, hpos, hlast, ?_, ?_⟩
  · rw [hprefix]; exact interval_selection_retain__greedy_prefix _ kept p hsel
  · intro alt hsa hna
    rw [hprefix] at hsa
    rcases interval_selection_extend_schedule_cases__greedy_prefix _ p alt hsa hna with ⟨hsold,hnold⟩ | ⟨l,r,he,hsold,hnold⟩
    · exact hmax alt hsold hnold
    · have hbold := interval_bounds_selected__greedy_prefix _ (l++r) hbprefix hsold
      have hbr : IntervalBounds r := Forall.iff_forall_mem.mpr (fun q hq => hbold.mem (List.mem_append_right _ hq))
      have hrend (q : interval) (hq : q ∈ r) : interval_end q ≤ interval_end p :=
        selected_member_end_le_current__greedy_prefix ps i (l++r) q hi hsorted hsold (List.mem_append_right _ hq)
      have hrnil := latest_interval_right_nil__greedy_prefix l p r (by rw [← he]; exact hna) hbr hrend
      subst r
      simp only [List.append_nil] at hsold hnold
      have hml := hmax l hsold hnold
      by_contra htoo
      have hll : Zlength l = kept_count := by rw [he, Zlength_app, Zlength_cons, Zlength_nil] at htoo; omega
      have hfl := hfront l hsold hnold hll
      have hbefore := nonoverlap_snoc_previous_finish__greedy_prefix l p (by rw [← he]; exact hna) (by omega)
      change interval_start p < last_finish at hskip
      omega
  · intro alt hsa hna hla
    have hba := interval_bounds_selected__greedy_prefix _ alt hbnew hsa
    rw [hprefix] at hsa
    rcases interval_selection_extend_schedule_cases__greedy_prefix _ p alt hsa hna with ⟨hsold,hnold⟩ | ⟨l,r,he,hsold,hnold⟩
    · exact hfront alt hsold hnold hla
    · have hpfinish := nonoverlap_member_end_le_finish__greedy_prefix alt p hna hba (by rw [he]; simp)
      change schedule_finish kept ≤ interval_end p at hkfinish
      omega

theorem pair_intervals_fields_at__greedy_prefix (starts ends : List Int) (ps : List interval) (k : Int)
    (hp : PairIntervals starts ends ps) (hb : IntervalBounds ps) (hk : 0 ≤ k ∧ k < Zlength ps) :
    Znth k starts 0 = interval_start (Znth k ps default_interval) ∧
    Znth k ends 0 = interval_end (Znth k ps default_interval) ∧
    -10000 ≤ interval_start (Znth k ps default_interval) ∧
    interval_start (Znth k ps default_interval) < interval_end (Znth k ps default_interval) ∧
    interval_end (Znth k ps default_interval) ≤ 10000 := by
  have hfields := (pair_intervals_lengths_and_fields__partition_lomuto starts ends ps hp).2.2 k ⟨hk.1, by rw [← hp.2.1]; exact hk.2⟩
  exact ⟨hfields.1.symm,hfields.2.symm,forall_nth ps default_interval k hb hk⟩

theorem greedy_prefix_singleton__greedy_prefix (ps : List interval) (hl : 0 < Zlength ps) :
    GreedyPrefixState ps 1 1 (interval_end (Znth 0 ps default_interval)) := by
  let p := Znth 0 ps default_interval
  have hprefix : sublist 0 1 ps = [p] := sublist_single default_interval 0 ps ⟨le_refl _, hl⟩
  refine ⟨[p], ?_, ?_, rfl, by change (0 : Int) < 1; decide, ?_, ?_, ?_⟩
  · rw [hprefix]; exact ⟨[], by simp⟩
  · intro i j hi hij hj; change j < (1 : Int) at hj; omega
  · rfl
  · intro alt hs hn
    rw [hprefix] at hs
    obtain ⟨removed,hp⟩ := hs
    have hlp := hp.length_eq
    simp only [List.length_singleton, List.length_append] at hlp
    change (alt.length : Int) ≤ 1
    omega
  · intro alt hs hn hla
    rw [hprefix] at hs
    obtain ⟨removed,hp⟩ := hs
    have hlen := hp.length_eq
    change (alt.length : Int) = 1 at hla
    simp only [List.length_singleton, List.length_append] at hlen
    have hr : removed = [] := by cases removed with
      | nil => rfl
      | cons a l => simp only [List.length_cons] at hlen; omega
    rw [hr,List.append_nil] at hp
    have he : alt = [p] := (List.perm_singleton.mp hp.symm)
    rw [he]; rfl

theorem greedy_prefix_yields_minimum_removals__optimum_returns (input sorted : List interval) (kept last_finish : Int)
    (hl : Zlength input = Zlength sorted) (hp : IntervalPermutation input sorted)
    (hg : GreedyPrefixState sorted (Zlength input) kept last_finish) : MinimumRemovals input (Zlength input-kept) := by
  obtain ⟨chosen,hsel,hno,hlen,_,_,hmax,_⟩ := hg
  rw [sublist_self sorted (Zlength input) hl] at hsel hmax
  refine ⟨Zlength input-kept, ⟨?_, ?_⟩, rfl⟩
  · refine ⟨chosen, ?_, hno, by rw [hlen]⟩
    obtain ⟨removed,hr⟩ := hsel
    exact ⟨removed,hp.trans hr⟩
  · intro count hc
    obtain ⟨alternative,hsa,hna,he⟩ := hc
    have hs : IntervalSelection sorted alternative := by
      obtain ⟨removed,hr⟩ := hsa
      exact ⟨removed,hp.symm.trans hr⟩
    have := hmax alternative hs hna
    change Zlength input-kept ≤ count
    omega

theorem minimum_removals_empty__optimum_returns (input : List interval) (hl : Zlength input = 0) : MinimumRemovals input 0 := by
  have he : input = [] := by
    cases input with
    | nil => rfl
    | cons a l => rw [Zlength_cons] at hl; have := Zlength_nonneg l; omega
  subst input
  refine ⟨0, ⟨?_, ?_⟩, rfl⟩
  · refine ⟨[], ⟨[], List.Perm.refl _⟩, ?_, rfl⟩
    intro i j hi hij hj; change j < (0 : Int) at hj; omega
  · intro count hc
    obtain ⟨alt,⟨removed,hp⟩,_,he⟩ := hc
    have hlp := hp.length_eq
    simp only [List.length_nil,List.length_append] at hlp
    change count = 0-(alt.length : Int) at he
    dsimp; omega

end SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_lib
