Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals Require Import non_overlapping_intervals_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_lib.
Local Open Scope sac.

Lemma proof_of_swap_intervals_return_wit_1 : swap_intervals_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre n
    (replace_Znth j_pre (Znth i_pre st_l 0)
      (replace_Znth i_pre (Znth j_pre st_l 0) st_l))).
  Intros_p Hstlen.
  Exists (replace_Znth j_pre (Znth i_pre st_l 0)
    (replace_Znth i_pre (Znth j_pre st_l 0) st_l))
    (replace_Znth j_pre (Znth i_pre ed_l 0)
    (replace_Znth i_pre (Znth j_pre ed_l 0) ed_l))
    (interval_swap ps i_pre j_pre).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial.
    + apply pair_intervals_swap__swap_records; try assumption;
        repeat rewrite Zlength_replace_Znth in *; lia.
    + reflexivity.
Qed.

Lemma proof_of_partition_intervals_entail_wit_1 : partition_intervals_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st_l).
  Intros_p Hstlen.
  Exists st_l ps ed_l.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try reflexivity; try assumption.
    eapply (lomuto_scan_init__partition_lomuto st_l ed_l ps); auto; lia.
Qed.

Lemma proof_of_partition_intervals_entail_wit_2_1 : partition_intervals_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st1_3).
  Intros_p Hstlen.
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    st1_2 ed1_2 ps1_2 PreH12) as [_ [Hlen_old Hfields_old]].
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    st1_3 ed1_3 ps1_3 PreH1) as [_ [Hlen_new Hfields_new]].
  assert (Hsame_len : Zlength ps1_3 = Zlength ps1_2).
  { rewrite PreH2. apply interval_swap_length__partition_lomuto. }
  assert (Hswap_perm : IntervalPermutation ps1_2 ps1_3).
  { rewrite PreH2. apply interval_swap_permutation__swap_records; lia. }
  assert (Hguard : interval_end (Znth j ps1_2 default_interval) <= pivot_end).
  { rewrite (proj2 (Hfields_old j ltac:(lia))). exact PreH3. }
  assert (Hnext : LomutoScanState ps ps1_3 low_pre high_pre
    (i + 1) (j + 1) pivot_end).
  { eapply lomuto_scan_accept__partition_lomuto; eauto; lia. }
  assert (Hpivot : pivot_end = Znth high_pre ed1_3 0).
  { pose proof Hnext as [_ [_ [Hlogical _]]].
    rewrite (proj2 (Hfields_new high_pre ltac:(lia))) in Hlogical.
    symmetry. exact Hlogical. }
  Exists st1_3 ps1_3 ed1_3.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_partition_intervals_entail_wit_2_2 : partition_intervals_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st1_2).
  Intros_p Hstlen.
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    st1_2 ed1_2 ps1_2 PreH10) as [_ [Hlen Hfields]].
  assert (Hguard : pivot_end < interval_end (Znth j ps1_2 default_interval)).
  { rewrite (proj2 (Hfields j ltac:(lia))). lia. }
  assert (Hnext : LomutoScanState ps ps1_2 low_pre high_pre i (j + 1) pivot_end).
  { eapply lomuto_scan_skip__partition_lomuto; eauto. }
  Exists st1_2 ps1_2 ed1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_partition_intervals_return_wit_1 : partition_intervals_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st1_3).
  Intros_p Hstlen.
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    st1_2 ed1_2 ps1_2 PreH11) as [_ [Hlen_old _]].
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    st1_3 ed1_3 ps1_3 PreH1) as [_ [Hlen_new _]].
  assert (Hsame_len : Zlength ps1_3 = Zlength ps1_2).
  { rewrite PreH2. apply interval_swap_length__partition_lomuto. }
  assert (Hswap_perm : IntervalPermutation ps1_2 ps1_3).
  { rewrite PreH2. apply interval_swap_permutation__swap_records; lia. }
  assert (Hfinish : IntervalPermutation ps ps1_3 /\
    IntervalSameOutsideRange ps ps1_3 low_pre high_pre /\
    IntervalPartitionedAt ps1_3 low_pre high_pre (i + 1)).
  { eapply lomuto_scan_finish__partition_lomuto; eauto; lia. }
  destruct Hfinish as [Hperm [Houtside Hpartition]].
  Exists st1_3 ed1_3 ps1_3.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_quicksort_intervals_range_entail_wit_1_1 : quicksort_intervals_range_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto || auto).
  prop_apply (IntArray.full_length st_pre intervalsSize_pre st1_2).
  Intros_p Hst1_2_len.
  pose proof (proj1 PreH9) as Hpivot_range.
  assert (Hps1_2_len : Zlength ps1_2 = intervalsSize_pre).
  {
    apply pair_intervals_indexed in PreH1.
    destruct PreH1 as [_ [Hps_st _]].
    rewrite Hps_st, Zlength_correct.
    exact Hst1_2_len.
  }
  assert (Hps1_len : Zlength ps1 = intervalsSize_pre).
  {
    pose proof PreH3 as Hsame_left.
    destruct Hsame_left as [Hperm_len _].
    lia.
  }
  assert (Hperm : IntervalPermutation ps ps1_2).
  {
    unfold IntervalPermutation in *.
    eapply Permutation_trans.
    - exact PreH7.
    - exact PreH2.
  }
  assert (Houtside :
    IntervalSameOutsideRange ps ps1_2 left_pre right_pre).
  {
    eapply outside_range_compose_nested__quicksort_left.
    - exact PreH8.
    - exact PreH3.
    - lia.
  }
  assert (Hpartition :
    IntervalPartitionedAt ps1_2 left_pre right_pre retval).
  {
    eapply partition_preserved_by_left_sort__quicksort_left.
    - exact PreH2.
    - exact PreH3.
    - lia.
    - rewrite Hps1_len. lia.
    - exact PreH9.
  }
  Exists st1_2 ed1_2 ps1_2.
  split_pure_spatial.
  - cancel.
  - repeat split_pures;
      try (dump_pre_spatial; lia);
      try (dump_pre_spatial; assumption).
Qed.

Lemma proof_of_quicksort_intervals_range_entail_wit_1_2 : quicksort_intervals_range_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto || auto).
  pose proof (proj1 PreH5) as Hpivot_range.
  assert (Hretval : retval = left_pre) by lia.
  assert (Hsorted :
    IntervalsEndSortedRange ps1 left_pre (retval - 1)).
  {
    apply sorted_range_empty__quicksort_left.
    lia.
  }
  Exists st1 ed1 ps1.
  split_pure_spatial.
  - cancel.
  - repeat split_pures;
      try (dump_pre_spatial; lia);
      try (dump_pre_spatial; assumption).
Qed.

Lemma proof_of_quicksort_intervals_range_return_wit_1 : quicksort_intervals_range_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto || auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st1_2).
  Intros_p Hstlen.
  assert (Hps1len : Zlength ps1_2 = intervalsSize_pre).
  {
    pose proof PreH1 as Hpair.
    apply pair_intervals_indexed in Hpair.
    destruct Hpair as [_ [Hpsst _]].
    lia.
  }
  assert (Hcurrentlen : Zlength current_ps = intervalsSize_pre).
  {
    pose proof PreH3 as Hsamecopy.
    destruct Hsamecopy as [Hlen _].
    lia.
  }
  assert (Hpartition :
      IntervalPartitionedAt ps1_2 left_pre right_pre pivot).
  {
    eapply right_sort_preserves_left_partition__quicksort_finish.
    - exact PreH2.
    - exact PreH3.
    - lia.
    - lia.
    - lia.
    - exact PreH15.
  }
  assert (Hleftsorted :
      IntervalsEndSortedRange ps1_2 left_pre (pivot - 1)).
  {
    eapply sorted_range_preserved_on_left__quicksort_finish.
    - exact PreH3.
    - lia.
    - lia.
    - lia.
    - exact PreH16.
  }
  assert (Hsorted : IntervalsEndSortedRange ps1_2 left_pre right_pre).
  {
    eapply partition_merge_sorted_ranges__quicksort_finish.
    - exact Hpartition.
    - exact Hleftsorted.
    - exact PreH4.
  }
  assert (Hperm : IntervalPermutation ps ps1_2).
  {
    unfold IntervalPermutation in *.
    eapply Permutation_trans; eauto.
  }
  assert (Houtside :
      IntervalSameOutsideRange ps ps1_2 left_pre right_pre).
  {
    eapply outside_range_compose_nested__quicksort_finish
      with (middle := current_ps) (inner_left := pivot + 1).
    - lia.
    - exact PreH14.
    - exact PreH3.
  }
  Exists st1_2; Exists ed1_2; Exists ps1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact Hperm.
    + dump_pre_spatial. exact Houtside.
    + dump_pre_spatial. exact Hsorted.
Qed.

Lemma proof_of_quicksort_intervals_range_return_wit_2 : quicksort_intervals_range_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto || auto).
  assert (Hpivot : pivot = right_pre) by lia.
  assert (Hrightsorted :
      IntervalsEndSortedRange current_ps (pivot + 1) right_pre).
  {
    apply sorted_range_trivial__quicksort_finish.
    lia.
  }
  assert (Hsorted :
      IntervalsEndSortedRange current_ps left_pre right_pre).
  {
    eapply partition_merge_sorted_ranges__quicksort_finish.
    - exact PreH11.
    - exact PreH12.
    - exact Hrightsorted.
  }
  Exists current_st; Exists current_ed; Exists current_ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial. exact Hsorted.
Qed.

Lemma proof_of_quicksort_intervals_range_return_wit_3 : quicksort_intervals_range_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto || auto).
  assert (Houtside : IntervalSameOutsideRange ps ps left_pre right_pre).
  { apply same_outside_refl__quicksort_finish. }
  assert (Hsorted : IntervalsEndSortedRange ps left_pre right_pre).
  { apply sorted_range_trivial__quicksort_finish. exact PreH1. }
  Exists st_l; Exists ed_l; Exists ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. apply Permutation_refl.
    + dump_pre_spatial. exact Houtside.
    + dump_pre_spatial. exact Hsorted.
Qed.

Lemma proof_of_quicksort_intervals_range_partial_solve_wit_2_pure_split_goal_1 : quicksort_intervals_range_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (proj1 PreH13) as Hpivot_range.
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_quicksort_intervals_range_partial_solve_wit_2_pure : quicksort_intervals_range_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_intervals_range_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_quicksort_intervals_return_wit_1 : quicksort_intervals_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto || auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st1_2).
  Intros_p Hstlen.
  assert (Hpslen : Zlength ps1_2 = intervalsSize_pre).
  {
    pose proof PreH1 as Hpair.
    apply pair_intervals_indexed in Hpair.
    destruct Hpair as [_ [Hpsst _]].
    lia.
  }
  assert (Hsorted : IntervalsEndSorted ps1_2).
  {
    eapply sorted_full_range__quicksort_finish.
    - exact Hpslen.
    - exact PreH4.
  }
  Exists st1_2; Exists ed1_2; Exists ps1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact Hsorted.
Qed.

Lemma proof_of_eraseOverlapIntervals_entail_wit_1 : eraseOverlapIntervals_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st1).
  Intros_p Hstlen.
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    st1 ed1 ps1 PreH2) as [_ [Hpslen Hfields]].
  assert (Hbounds : Forall (fun p => -10000 <= interval_start p /\
    interval_start p < interval_end p /\ interval_end p <= 10000) ps1).
  { eapply Permutation_Forall; [exact PreH3|].
    apply (proj1 (pair_intervals_bounds_iff st_l ed_l ps PreH7)).
    repeat split; assumption. }
  pose proof (proj2 (pair_intervals_bounds_iff st1 ed1 ps1 PreH2) Hbounds)
    as [Hstarts [Hproper Hends]].
  pose proof (greedy_prefix_singleton__greedy_prefix ps1 ltac:(lia)) as Hgreedy.
  pose proof (proj2 (Hfields 0 ltac:(lia))) as Hend.
  Exists st1 ed1 ps1.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    rewrite <- Hend. exact Hgreedy.
Qed.

Lemma proof_of_eraseOverlapIntervals_entail_wit_2_1 : eraseOverlapIntervals_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre sorted_st_2).
  Intros_p Hstlen.
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    sorted_st_2 sorted_ed_2 sorted_ps_2 PreH7) as [_ [Hpslen Hfields]].
  assert (Hi : 0 <= i < Zlength sorted_ps_2) by lia.
  pose proof (Hfields i ltac:(lia)) as [Hstart Hend].
  assert (Hbounds : Forall (fun p => -10000 <= interval_start p /\
    interval_start p < interval_end p /\ interval_end p <= 10000) sorted_ps_2).
  { apply (proj1 (pair_intervals_bounds_iff
      sorted_st_2 sorted_ed_2 sorted_ps_2 PreH7)). repeat split; assumption. }
  pose proof (greedy_prefix_accept__greedy_prefix sorted_ps_2 i kept last_end
    Hi Hbounds PreH13 ltac:(lia)) as Hnext.
  Exists sorted_st_2 sorted_ed_2 sorted_ps_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    rewrite <- Hend. exact Hnext.
Qed.

Lemma proof_of_eraseOverlapIntervals_entail_wit_2_2 : eraseOverlapIntervals_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre sorted_st_2).
  Intros_p Hstlen.
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    sorted_st_2 sorted_ed_2 sorted_ps_2 PreH7) as [_ [Hpslen Hfields]].
  assert (Hi : 0 <= i < Zlength sorted_ps_2) by lia.
  pose proof (Hfields i ltac:(lia)) as [Hstart Hend].
  assert (Hbounds : Forall (fun p => -10000 <= interval_start p /\
    interval_start p < interval_end p /\ interval_end p <= 10000) sorted_ps_2).
  { apply (proj1 (pair_intervals_bounds_iff
      sorted_st_2 sorted_ed_2 sorted_ps_2 PreH7)). repeat split; assumption. }
  pose proof (greedy_prefix_skip__greedy_prefix sorted_ps_2 i kept last_end
    Hi Hbounds PreH12 PreH13 ltac:(lia)) as Hnext.
  Exists sorted_st_2 sorted_ed_2 sorted_ps_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

(* The strategy-only branch omits array length; the whole VC below is proved. *)
Lemma proof_of_eraseOverlapIntervals_return_wit_1_split_goal_1 : eraseOverlapIntervals_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_eraseOverlapIntervals_return_wit_1 : eraseOverlapIntervals_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre sorted_st).
  Intros_p Hstlen.
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    sorted_st sorted_ed sorted_ps PreH6) as [_ [Hpslen _]].
  assert (Hinputlen : Zlength ps = Zlength sorted_ps).
  { rewrite !Zlength_correct. now rewrite (Permutation_length PreH10). }
  assert (Hfull : GreedyPrefixState sorted_ps (Zlength ps) kept last_end).
  { replace (Zlength ps) with i by lia. exact PreH12. }
  pose proof (greedy_prefix_yields_minimum_removals__optimum_returns
    ps sorted_ps kept last_end Hinputlen PreH10 Hfull) as Hminimum.
  Exists sorted_ed sorted_st.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial. replace intervalsSize_pre with (Zlength ps) by lia.
    exact Hminimum.
Qed.

(* The strategy-only branch omits array length; the whole VC below is proved. *)
Lemma proof_of_eraseOverlapIntervals_return_wit_2_split_goal_1 : eraseOverlapIntervals_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_eraseOverlapIntervals_return_wit_2 : eraseOverlapIntervals_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st1_2).
  Intros_p Hstlen.
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    st1_2 ed1_2 ps1 PreH2) as [_ [Hpslen _]].
  pose proof (Permutation_length PreH3) as Hpermlen.
  Exists ed1_2 st1_2.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial. apply minimum_removals_empty__optimum_returns.
    rewrite !Zlength_correct in *. lia.
Qed.
