import SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_goal
import SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open non_overlapping_intervals_goal non_overlapping_intervals_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem forall_indexed (α : Type) (P : α → Prop) (l : List α) (d : α) :
    Forall P l ↔ ∀ i, 0 ≤ i ∧ i < Zlength l → P (Znth i l d) := by
  rw [Forall.iff_forall_mem]
  constructor
  · intro h i hi
    have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
    have hm := h l[i.toNat] (List.mem_iff_getElem.mpr ⟨i.toNat, hn, rfl⟩)
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hm
  · intro h v hv
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hv
    have hi : 0 ≤ (n : Int) ∧ (n : Int) < Zlength l := by change 0 ≤ (n : Int) ∧ (n : Int) < (l.length : Int); omega
    have hh := h n hi
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hh

private theorem pair_bounds_iff (st ed : List Int) (ps : List interval) (hp : PairIntervals st ed ps) :
    (Forall (LE.le (-10000 : Int)) st ∧ Forall2 (LT.lt (α := Int)) st ed ∧ Forall (GE.ge (10000 : Int)) ed) ↔ IntervalBounds ps := by
  obtain ⟨hse, hps, hfields⟩ := pair_intervals_lengths_and_fields__partition_lomuto st ed ps hp
  have hseNat : st.length = ed.length := by
    have hh : (st.length : Int) = (ed.length : Int) := hse
    omega
  constructor
  · rintro ⟨hs, hm, he⟩
    apply (forall_indexed interval _ ps default_interval).mpr
    intro i hi
    have hf := hfields i (by omega)
    have hlo := (forall_indexed Int _ st 0).mp hs i (by omega)
    have hhi := (forall_indexed Int _ ed 0).mp he i (by omega)
    have hm' := ((Forall2_nth_iff Int Int _ st ed 0 0).mp hm).2 i.toNat (by have hh : i < (st.length : Int) := lt_of_lt_of_eq hi.2 hps; omega)
    change Znth i st 0 < Znth i ed 0 at hm'
    rw [hf.1, hf.2]
    exact ⟨hlo, hm', hhi⟩
  · intro hb
    have hb' := (forall_indexed interval _ ps default_interval).mp hb
    refine ⟨?_, ?_, ?_⟩
    · apply (forall_indexed Int _ st 0).mpr
      intro i hi
      have hf := hfields i hi
      have hh := hb' i (by omega)
      simpa only [hf.1] using hh.1
    · apply (Forall2_nth_iff Int Int _ st ed 0 0).mpr
      refine ⟨hseNat, ?_⟩
      intro n hn
      have hi : 0 ≤ (n : Int) ∧ (n : Int) < Zlength st := by change 0 ≤ (n : Int) ∧ (n : Int) < (st.length : Int); omega
      have hf := hfields n hi
      have hh := hb' n (by omega)
      change Znth (n : Int) st 0 < Znth (n : Int) ed 0
      simpa only [hf.1, hf.2] using hh.2.1
    · apply (forall_indexed Int _ ed 0).mpr
      intro i hi
      have hf := hfields i (by omega)
      have hh := hb' i (by omega)
      simpa only [hf.2] using hh.2.2

theorem proof_of_swap_intervals_return_wit_1 : swap_intervals_return_wit_1 := by
  unfold swap_intervals_return_wit_1
  left
  intro j_pre i_pre ed_pre st_pre ps ed_l st_l n PreH1 PreH2 PreH3 PreH4 PreH5
  prop_apply (intArray.full_Zlength st_pre n (replace_Znth j_pre (Znth i_pre st_l 0) (replace_Znth i_pre (Znth j_pre st_l 0) st_l)))
  Intros_p harr
  change Zlength (replace_Znth j_pre (Znth i_pre st_l 0) (replace_Znth i_pre (Znth j_pre st_l 0) st_l)) = n at harr
  rw [Zlength_replace_Znth, Zlength_replace_Znth] at harr
  have hp := pair_intervals_swap__swap_records st_l ed_l ps i_pre j_pre PreH5 (by omega) (by omega)
  have hs : IntervalSwappedAt ps (interval_swap ps i_pre j_pre) i_pre j_pre := rfl
  Exists (replace_Znth j_pre (Znth i_pre st_l 0) (replace_Znth i_pre (Znth j_pre st_l 0) st_l)) (replace_Znth j_pre (Znth i_pre ed_l 0) (replace_Znth i_pre (Znth j_pre ed_l 0) ed_l)) (interval_swap ps i_pre j_pre)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_partition_intervals_entail_wit_1 : partition_intervals_entail_wit_1 := by
  unfold partition_intervals_entail_wit_1
  left
  intro high_pre low_pre intervalsSize_pre ed_pre st_pre ps ed_l st_l PreH1 PreH2 PreH3 PreH4
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st_l)
  Intros_p harr
  change Zlength st_l = intervalsSize_pre at harr
  have hp := lomuto_scan_init__partition_lomuto st_l ed_l ps low_pre high_pre PreH4 PreH1 PreH2 (by omega)
  Exists st_l ps ed_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_partition_intervals_entail_wit_2_1 : partition_intervals_entail_wit_2_1 := by
  unfold partition_intervals_entail_wit_2_1
  left
  intro high_pre low_pre intervalsSize_pre ed_pre st_pre ps pivot_end j i st1_2 ed1_2 ps1_2 st1_3 ed1_3 ps1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_3)
  Intros_p harr
  change Zlength st1_3 = intervalsSize_pre at harr
  have hlnew := PreH1.2.1
  have hlold := PreH12.2.1
  have hsame : Zlength ps1_3 = Zlength ps1_2 := by rw [PreH2]; exact interval_swap_length__partition_lomuto _ _ _
  have hperm : IntervalPermutation ps1_2 ps1_3 := by rw [PreH2]; apply interval_swap_permutation__swap_records <;> omega
  have hf := (pair_intervals_lengths_and_fields__partition_lomuto st1_2 ed1_2 ps1_2 PreH12).2.2 j (by omega)
  have hg : interval_end (Znth j ps1_2 default_interval) ≤ pivot_end := by rw [hf.2]; exact PreH3
  have hn := lomuto_scan_accept__partition_lomuto ps ps1_2 ps1_3 low_pre high_pre i j pivot_end PreH5 PreH6 (by omega) PreH8 PreH9 PreH4 PreH13 hperm PreH2 hg
  have hfn := (pair_intervals_lengths_and_fields__partition_lomuto st1_3 ed1_3 ps1_3 PreH1).2.2 high_pre (by omega)
  have hpiv := hn.2.2.1
  rw [hfn.2] at hpiv
  Exists st1_3 ps1_3 ed1_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_partition_intervals_entail_wit_2_2 : partition_intervals_entail_wit_2_2 := by
  unfold partition_intervals_entail_wit_2_2
  left
  intro high_pre low_pre intervalsSize_pre ed_pre st_pre ps pivot_end j i st1_2 ed1_2 ps1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_2)
  Intros_p harr
  change Zlength st1_2 = intervalsSize_pre at harr
  have hl := PreH10.2.1
  have hf := (pair_intervals_lengths_and_fields__partition_lomuto st1_2 ed1_2 ps1_2 PreH10).2.2 j (by omega)
  have hg : pivot_end < interval_end (Znth j ps1_2 default_interval) := by rw [hf.2]; exact PreH1
  have hn := lomuto_scan_skip__partition_lomuto ps ps1_2 low_pre high_pre i j pivot_end PreH2 PreH11 hg
  Exists st1_2 ps1_2 ed1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_partition_intervals_return_wit_1 : partition_intervals_return_wit_1 := by
  unfold partition_intervals_return_wit_1
  left
  intro high_pre low_pre intervalsSize_pre ed_pre st_pre ps pivot_end j i st1_2 ed1_2 ps1_2 st1_3 ed1_3 ps1_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_3)
  Intros_p harr
  change Zlength st1_3 = intervalsSize_pre at harr
  have hlnew := PreH1.2.1
  have hsame : Zlength ps1_3 = Zlength ps1_2 := by rw [PreH2]; exact interval_swap_length__partition_lomuto _ _ _
  have hperm : IntervalPermutation ps1_2 ps1_3 := by rw [PreH2]; apply interval_swap_permutation__swap_records <;> omega
  obtain ⟨hp, ho, ht⟩ := lomuto_scan_finish__partition_lomuto ps ps1_2 ps1_3 low_pre high_pre i j pivot_end PreH4 PreH5 (by omega) PreH7 PreH8 PreH9 PreH3 PreH12 hperm PreH2
  Exists st1_3 ed1_3 ps1_3
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_quicksort_intervals_range_entail_wit_1_1 : quicksort_intervals_range_entail_wit_1_1 := by
  unfold quicksort_intervals_range_entail_wit_1_1
  left
  intro right_pre left_pre intervalsSize_pre ed_pre st_pre ps ed_l st_l retval st1 ed1 ps1 st1_2 ed1_2 ps1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_2)
  Intros_p harr
  change Zlength st1_2 = intervalsSize_pre at harr
  have hl := PreH1.2.1
  have hs := PreH3.1
  have hpiv := PreH9.1
  have hp : IntervalPermutation ps ps1_2 := PreH7.trans PreH2
  have ho := outside_range_compose_nested__quicksort_left ps ps1 ps1_2 left_pre right_pre (retval-1) PreH8 PreH3 (by omega)
  have ht := partition_preserved_by_left_sort__quicksort_left ps1 ps1_2 left_pre right_pre retval PreH2 PreH3 PreH12 (by omega) PreH9
  Exists st1_2 ed1_2 ps1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_quicksort_intervals_range_entail_wit_1_2 : quicksort_intervals_range_entail_wit_1_2 := by
  unfold quicksort_intervals_range_entail_wit_1_2
  left
  intro right_pre left_pre intervalsSize_pre ed_pre st_pre ps ed_l st_l retval st1 ed1 ps1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hpiv := PreH5.1
  have hs := sorted_range_empty__quicksort_left ps1 left_pre (retval-1) (by omega)
  Exists st1 ed1 ps1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_quicksort_intervals_range_return_wit_1 : quicksort_intervals_range_return_wit_1 := by
  unfold quicksort_intervals_range_return_wit_1
  left
  intro right_pre left_pre intervalsSize_pre ed_pre st_pre ps pivot current_st current_ed current_ps st1_2 ed1_2 ps1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_2)
  Intros_p harr
  change Zlength st1_2 = intervalsSize_pre at harr
  have hl := PreH1.2.1
  have hs := PreH3.1
  have ht := right_sort_preserves_left_partition__quicksort_finish current_ps ps1_2 left_pre right_pre pivot PreH2 PreH3 PreH7 PreH11 (by omega) PreH15
  have hleft := sorted_range_preserved_on_left__quicksort_finish current_ps ps1_2 left_pre right_pre pivot PreH3 PreH7 PreH11 (by omega) PreH16
  have hsorted := partition_merge_sorted_ranges__quicksort_finish ps1_2 left_pre right_pre pivot ht hleft PreH4
  have hp : IntervalPermutation ps ps1_2 := PreH13.trans PreH2
  have ho := outside_range_compose_nested__quicksort_finish ps current_ps ps1_2 left_pre (pivot+1) right_pre (by omega) PreH14 PreH3
  Exists st1_2 ed1_2 ps1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_quicksort_intervals_range_return_wit_2 : quicksort_intervals_range_return_wit_2 := by
  unfold quicksort_intervals_range_return_wit_2
  left
  intro right_pre left_pre intervalsSize_pre ed_pre st_pre ps pivot current_st current_ed current_ps PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hright := sorted_range_trivial__quicksort_finish current_ps (pivot+1) right_pre (by omega)
  have hs := partition_merge_sorted_ranges__quicksort_finish current_ps left_pre right_pre pivot PreH11 PreH12 hright
  Exists current_st current_ed current_ps
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_quicksort_intervals_range_return_wit_3 : quicksort_intervals_range_return_wit_3 := by
  unfold quicksort_intervals_range_return_wit_3
  left
  intro right_pre left_pre intervalsSize_pre ed_pre st_pre ps ed_l st_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have ho := same_outside_refl__quicksort_finish ps left_pre right_pre
  have hs := sorted_range_trivial__quicksort_finish ps left_pre right_pre PreH1
  have hp : IntervalPermutation ps ps := List.Perm.refl _
  Exists st_l ed_l ps
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_quicksort_intervals_return_wit_1 : quicksort_intervals_return_wit_1 := by
  unfold quicksort_intervals_return_wit_1
  left
  intro intervalsSize_pre ed_pre st_pre ps ed_l st_l st1_2 ed1_2 ps1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_2)
  Intros_p harr
  change Zlength st1_2 = intervalsSize_pre at harr
  have hl := PreH1.2.1
  have hs := sorted_full_range__quicksort_finish ps1_2 intervalsSize_pre (by omega) PreH4
  Exists st1_2 ed1_2 ps1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_eraseOverlapIntervals_entail_wit_1 : eraseOverlapIntervals_entail_wit_1 := by
  unfold eraseOverlapIntervals_entail_wit_1
  left
  intro intervalsSize_pre ed_pre st_pre ps ed_l st_l st1 ed1 ps1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1)
  Intros_p harr
  change Zlength st1 = intervalsSize_pre at harr
  have hl := PreH2.2.1
  have hb := ((pair_bounds_iff st_l ed_l ps PreH7).mp ⟨PreH8, PreH9, PreH10⟩).perm PreH3
  obtain ⟨hlo, hproper, hhi⟩ := (pair_bounds_iff st1 ed1 ps1 PreH2).mpr hb
  have hf := (pair_intervals_lengths_and_fields__partition_lomuto st1 ed1 ps1 PreH2).2.2 0 (by omega)
  have hg := greedy_prefix_singleton__greedy_prefix ps1 (by omega)
  rw [hf.2] at hg
  Exists st1 ed1 ps1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_eraseOverlapIntervals_entail_wit_2_1 : eraseOverlapIntervals_entail_wit_2_1 := by
  unfold eraseOverlapIntervals_entail_wit_2_1
  left
  intro intervalsSize_pre ed_pre st_pre ps last_end sorted_st_2 sorted_ed_2 sorted_ps_2 kept i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre sorted_st_2)
  Intros_p harr
  change Zlength sorted_st_2 = intervalsSize_pre at harr
  have hl := PreH7.2.1
  have hi : 0 ≤ i ∧ i < Zlength sorted_ps_2 := by omega
  have hb := (pair_bounds_iff sorted_st_2 sorted_ed_2 sorted_ps_2 PreH7).mp ⟨PreH8, PreH9, PreH10⟩
  have hf := (pair_intervals_lengths_and_fields__partition_lomuto sorted_st_2 sorted_ed_2 sorted_ps_2 PreH7).2.2 i (by omega)
  have hn := greedy_prefix_accept__greedy_prefix sorted_ps_2 i kept last_end hi hb PreH13 (by rw [hf.1]; exact PreH1)
  rw [hf.2] at hn
  Exists sorted_st_2 sorted_ed_2 sorted_ps_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_eraseOverlapIntervals_entail_wit_2_2 : eraseOverlapIntervals_entail_wit_2_2 := by
  unfold eraseOverlapIntervals_entail_wit_2_2
  left
  intro intervalsSize_pre ed_pre st_pre ps last_end sorted_st_2 sorted_ed_2 sorted_ps_2 kept i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre sorted_st_2)
  Intros_p harr
  change Zlength sorted_st_2 = intervalsSize_pre at harr
  have hl := PreH7.2.1
  have hi : 0 ≤ i ∧ i < Zlength sorted_ps_2 := by omega
  have hb := (pair_bounds_iff sorted_st_2 sorted_ed_2 sorted_ps_2 PreH7).mp ⟨PreH8, PreH9, PreH10⟩
  have hf := (pair_intervals_lengths_and_fields__partition_lomuto sorted_st_2 sorted_ed_2 sorted_ps_2 PreH7).2.2 i (by omega)
  have hn := greedy_prefix_skip__greedy_prefix sorted_ps_2 i kept last_end hi hb PreH12 PreH13 (by rw [hf.1]; exact PreH1)
  Exists sorted_st_2 sorted_ed_2 sorted_ps_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_eraseOverlapIntervals_return_wit_1 : eraseOverlapIntervals_return_wit_1 := by
  unfold eraseOverlapIntervals_return_wit_1
  left
  intro intervalsSize_pre ed_pre st_pre ps last_end sorted_st sorted_ed sorted_ps kept i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre sorted_st)
  Intros_p harr
  change Zlength sorted_st = intervalsSize_pre at harr
  have hl := PreH6.2.1
  have hperm : Zlength ps = Zlength sorted_ps := congrArg (fun n : Nat => (n : Int)) PreH10.length_eq
  have hf : GreedyPrefixState sorted_ps (Zlength ps) kept last_end := by convert PreH12 using 1 <;> omega
  have hm := greedy_prefix_yields_minimum_removals__optimum_returns ps sorted_ps kept last_end hperm PreH10 hf
  have hi : intervalsSize_pre = Zlength ps := by omega
  rw [← hi] at hm
  Exists sorted_ed sorted_st
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_eraseOverlapIntervals_return_wit_2 : eraseOverlapIntervals_return_wit_2 := by
  unfold eraseOverlapIntervals_return_wit_2
  left
  intro intervalsSize_pre ed_pre st_pre ps ed_l st_l st1_2 ed1_2 ps1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  prop_apply (intArray.full_Zlength st_pre intervalsSize_pre st1_2)
  Intros_p harr
  change Zlength st1_2 = intervalsSize_pre at harr
  have hl := PreH2.2.1
  have hperm : Zlength ps = Zlength ps1 := congrArg (fun n : Nat => (n : Int)) PreH3.length_eq
  have hm := minimum_removals_empty__optimum_returns ps (by omega)
  Exists ed1_2 st1_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_quicksort_intervals_range_partial_solve_wit_2_pure : quicksort_intervals_range_partial_solve_wit_2_pure := by
  unfold quicksort_intervals_range_partial_solve_wit_2_pure
  right
  intro right_pre left_pre intervalsSize_pre ed_pre st_pre ps ed_l st_l retval st1 ed1 ps1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hp := PreH13.1
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

end SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_proof_manual
