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
From SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals Require Import non_overlapping_intervals_proof_auto.
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
  prop_apply_p (IntArray.full_Zlength ed_pre n
    (replace_Znth j_pre (Znth i_pre ed_l 0)
      (replace_Znth i_pre (Znth j_pre ed_l 0) ed_l))).
  prop_apply_p (IntArray.full_Zlength st_pre n
    (replace_Znth j_pre (Znth i_pre st_l 0)
      (replace_Znth i_pre (Znth j_pre st_l 0) st_l))).
  Intros_p Hedlen.
  Intros_p Hstlen.
  Exists
    (replace_Znth j_pre (Znth i_pre st_l 0)
      (replace_Znth i_pre (Znth j_pre st_l 0) st_l))
    (replace_Znth j_pre (Znth i_pre ed_l 0)
      (replace_Znth i_pre (Znth j_pre ed_l 0) ed_l))
    (interval_swap ps i_pre j_pre).
  split_pure_spatial.
  - cancel
      (IntArray.full st_pre n
        (replace_Znth j_pre (Znth i_pre st_l 0)
          (replace_Znth i_pre (Znth j_pre st_l 0) st_l))).
    cancel
      (IntArray.full ed_pre n
        (replace_Znth j_pre (Znth i_pre ed_l 0)
          (replace_Znth i_pre (Znth j_pre ed_l 0) ed_l))).
  - split_pures.
    + dump_pre_spatial.
      apply pair_intervals_swap__swap_records; try assumption.
      all: repeat rewrite Zlength_replace_Znth in *; lia.
    + dump_pre_spatial.
      apply interval_swap_bounds__swap_records; try assumption.
      all: match goal with
           | Hpair : PairIntervals ?starts ?ends ?records |- _ =>
               destruct Hpair as [Hse [Hps Hpoint]]
           end;
           repeat rewrite Zlength_replace_Znth in *; lia.
    + dump_pre_spatial.
      apply interval_swap_permutation__swap_records.
      * match goal with
        | Hpair : PairIntervals ?starts ?ends ?records |- _ =>
            destruct Hpair as [Hse [Hps Hpoint]]
        end;
        repeat rewrite Zlength_replace_Znth in *; lia.
      * match goal with
        | Hpair : PairIntervals ?starts ?ends ?records |- _ =>
            destruct Hpair as [Hse [Hps Hpoint]]
        end;
        repeat rewrite Zlength_replace_Znth in *; lia.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_partition_intervals_entail_wit_1 : partition_intervals_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Harray_len.
  pose proof
    (pair_intervals_lengths_and_fields__partition_lomuto
       st_l ed_l ps PreH4) as [Hsame_len [Hps_len _]].
  Exists ps (Znth high_pre ed_l 0) ed_l st_l low_pre (low_pre - 1).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try reflexivity; try assumption.
    apply (lomuto_scan_init__partition_lomuto
      st_l ed_l ps low_pre high_pre); auto.
    lia.
Qed.

Lemma proof_of_partition_intervals_entail_wit_2_1 : partition_intervals_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (pair_intervals_lengths_and_fields__partition_lomuto
       st1_2 ed1_2 ps1_2 PreH16) as [_ [Hlen_old Hfields_old]].
  pose proof
    (pair_intervals_lengths_and_fields__partition_lomuto
       st1_3 ed1_3 ps1_3 PreH1) as [Hsame_new [Hlen_new Hfields_new]].
  assert (Hperm_len : Zlength ps1_2 = Zlength ps1_3).
  {
    unfold IntervalPermutation in PreH3.
    rewrite !Zlength_correct.
    rewrite (Permutation_length PreH3). reflexivity.
  }
  assert (Hguard :
      interval_end (Znth j_2 ps1_2 default_interval) <= pivot_end_2).
  {
    rewrite (proj2 (Hfields_old j_2 ltac:(lia))).
    exact PreH5.
  }
  assert (Hnext :
      LomutoScanState ps ps1_3 low_pre high_pre
        (i_2 + 1) (j_2 + 1) pivot_end_2).
  {
    eapply lomuto_scan_accept__partition_lomuto; eauto; lia.
  }
  assert (Hpivot_new : pivot_end_2 = Znth high_pre ed1_3 0).
  {
    pose proof Hnext as [_ [_ [Hlogical _]]].
    rewrite (proj2 (Hfields_new high_pre ltac:(lia))) in Hlogical.
    symmetry. exact Hlogical.
  }
  Exists ps1_3 pivot_end_2 ed1_3 st1_3 (j_2 + 1) (i_2 + 1).
  split_pure_spatial.
  - rewrite PreH13.
    cancel (IntArray.full st_pre intervalsSize_pre st1_3).
    cancel (IntArray.full ed_pre intervalsSize_pre ed1_3).
    repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try reflexivity;
      try assumption.
Qed.

Lemma proof_of_partition_intervals_entail_wit_2_2 : partition_intervals_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (pair_intervals_lengths_and_fields__partition_lomuto
       st1_2 ed1_2 ps1_2 PreH12) as [_ [Hlen Hfields]].
  assert (Hguard :
      pivot_end_2 < interval_end (Znth j_2 ps1_2 default_interval)).
  {
    rewrite (proj2 (Hfields j_2 ltac:(lia))).
    lia.
  }
  assert (Hnext :
      LomutoScanState ps ps1_2 low_pre high_pre
        i_2 (j_2 + 1) pivot_end_2).
  {
    eapply lomuto_scan_skip__partition_lomuto; eauto.
  }
  Exists ps1_2 pivot_end_2 ed1_2 st1_2 (j_2 + 1) i_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try reflexivity;
      try assumption.
Qed.

Lemma proof_of_partition_intervals_return_wit_1 : partition_intervals_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (pair_intervals_lengths_and_fields__partition_lomuto
       st1_2 ed1_2 ps1_2 PreH15) as [_ [Hlen _]].
  assert (Hfinish :
      IntervalPermutation ps ps1_3 /\
      IntervalSameOutsideRange ps ps1_3 low_pre high_pre /\
      IntervalPartitionedAt ps1_3 low_pre high_pre (i + 1)).
  {
    eapply lomuto_scan_finish__partition_lomuto; eauto; lia.
  }
  destruct Hfinish as [Hperm [Hsame Hpartitioned]].
  Exists st1_3 ed1_3 ps1_3.
  split_pure_spatial.
  - rewrite PreH12. repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_quicksort_intervals_range_entail_wit_1_1 : quicksort_intervals_range_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto || auto).
  prop_apply (IntArray.full_length st_pre intervalsSize_pre st1_2).
  Intros_p Hst1_2_len.
  assert (Hps1_2_len : Zlength ps1_2 = intervalsSize_pre).
  {
    destruct PreH1 as [_ [Hps_st _]].
    rewrite Hps_st, Zlength_correct.
    exact Hst1_2_len.
  }
  assert (Hps1_len : Zlength ps1 = intervalsSize_pre).
  {
    pose proof PreH4 as Hsame_left.
    destruct Hsame_left as [Hperm_len _].
    lia.
  }
  assert (Hperm : IntervalPermutation ps ps1_2).
  {
    unfold IntervalPermutation in *.
    eapply Permutation_trans.
    - exact PreH11.
    - exact PreH3.
  }
  assert (Houtside :
    IntervalSameOutsideRange ps ps1_2 left_pre right_pre).
  {
    eapply outside_range_compose_nested__quicksort_left.
    - exact PreH12.
    - exact PreH4.
    - lia.
  }
  assert (Hpartition :
    IntervalPartitionedAt ps1_2 left_pre right_pre retval).
  {
    eapply partition_preserved_by_left_sort__quicksort_left.
    - exact PreH3.
    - exact PreH4.
    - lia.
    - rewrite Hps1_len. lia.
    - exact PreH13.
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
    unfold PairIntervals in Hpair.
    destruct Hpair as [_ [Hpsst _]].
    lia.
  }
  assert (Hcurrentlen : Zlength current_ps = intervalsSize_pre).
  {
    pose proof PreH4 as Hsamecopy.
    destruct Hsamecopy as [Hlen _].
    lia.
  }
  assert (Hpartition :
      IntervalPartitionedAt ps1_2 left_pre right_pre pivot).
  {
    eapply right_sort_preserves_left_partition__quicksort_finish.
    - exact PreH3.
    - exact PreH4.
    - lia.
    - lia.
    - lia.
    - exact PreH17.
  }
  assert (Hleftsorted :
      IntervalsEndSortedRange ps1_2 left_pre (pivot - 1)).
  {
    eapply sorted_range_preserved_on_left__quicksort_finish.
    - exact PreH4.
    - lia.
    - lia.
    - lia.
    - exact PreH18.
  }
  assert (Hsorted : IntervalsEndSortedRange ps1_2 left_pre right_pre).
  {
    eapply partition_merge_sorted_ranges__quicksort_finish.
    - exact Hpartition.
    - exact Hleftsorted.
    - exact PreH5.
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
    - exact PreH16.
    - exact PreH4.
  }
  Exists st1_2; Exists ed1_2; Exists ps1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
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
    - exact PreH12.
    - exact PreH13.
    - exact Hrightsorted.
  }
  Exists current_st; Exists current_ed; Exists current_ps.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial. exact PreH11.
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
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. apply Permutation_refl.
    + dump_pre_spatial. exact Houtside.
    + dump_pre_spatial. exact Hsorted.
Qed.

Lemma proof_of_quicksort_intervals_return_wit_1 : quicksort_intervals_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto || auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st1_2).
  Intros_p Hstlen.
  assert (Hpslen : Zlength ps1_2 = intervalsSize_pre).
  {
    pose proof PreH1 as Hpair.
    unfold PairIntervals in Hpair.
    destruct Hpair as [_ [Hpsst _]].
    lia.
  }
  assert (Hsorted : IntervalsEndSorted ps1_2).
  {
    eapply sorted_full_range__quicksort_finish.
    - exact Hpslen.
    - exact PreH5.
  }
  Exists st1_2; Exists ed1_2; Exists ps1_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact Hsorted.
Qed.

Lemma proof_of_eraseOverlapIntervals_entail_wit_1 : eraseOverlapIntervals_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength ed_pre intervalsSize_pre ed1).
  Intros_p Hedlen.
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st1).
  Intros_p Hstlen.
  assert (Hsize : 0 < Zlength ps1).
  { lazymatch goal with
    | Hpair : PairIntervals st1 ed1 ps1 |- _ =>
        unfold PairIntervals in Hpair;
        destruct Hpair as [_ [Hpslen _]];
        pose proof (Zlength_nonneg ps1); lia
    end. }
  lazymatch goal with
  | Hpair : PairIntervals st1 ed1 ps1,
    Hbounds : IntervalBounds ps1 |- _ =>
      pose proof
        (pair_intervals_fields_at__greedy_prefix
           st1 ed1 ps1 0 Hpair Hbounds ltac:(lia)) as Hfields
  end.
  destruct Hfields as [Hstart [Hend [Hlower [Hproper Hupper]]]].
  pose proof (greedy_prefix_singleton__greedy_prefix ps1 Hsize) as Hgreedy.
  Exists ps1 ed1 st1 (Znth 0 ed1 0) 1 1.
  split_pure_spatial.
  - cancel ((( &( "i" ) )) # Int |-> 1).
    cancel ((( &( "kept" ) )) # Int |-> 1).
    cancel ((( &( "last_end" ) )) # Int |-> (Znth 0 ed1 0)).
    cancel ((( &( "st" ) )) # Ptr |-> st_pre).
    cancel ((( &( "ed" ) )) # Ptr |-> ed_pre).
    cancel ((( &( "intervalsSize" ) )) # Int |-> intervalsSize_pre).
    cancel (IntArray.full st_pre intervalsSize_pre st1).
    cancel (IntArray.full ed_pre intervalsSize_pre ed1).
  - split_pures.
  all: dump_pre_spatial; try assumption; try lia.
  rewrite Hend. exact Hgreedy.
Qed.

Lemma proof_of_eraseOverlapIntervals_entail_wit_2_1 : eraseOverlapIntervals_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hpslen : Zlength sorted_ps_2 = Zlength sorted_st_2).
  { lazymatch goal with
    | Hpair : PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2 |- _ =>
        unfold PairIntervals in Hpair; tauto
    end. }
  assert (Hi : 0 <= i_2 < Zlength sorted_ps_2) by lia.
  lazymatch goal with
  | Hpair : PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2,
    Hbounds : IntervalBounds sorted_ps_2 |- _ =>
      pose proof
        (pair_intervals_fields_at__greedy_prefix
           sorted_st_2 sorted_ed_2 sorted_ps_2 i_2
           Hpair Hbounds Hi) as Hfields
  end.
  destruct Hfields as [Hstart [Hend [Hlower [Hproper Hupper]]]].
  assert (Haccept :
            last_end_2 <=
              interval_start (Znth i_2 sorted_ps_2 default_interval)) by lia.
  lazymatch goal with
  | Hbounds : IntervalBounds sorted_ps_2,
    Hstate : GreedyPrefixState sorted_ps_2 i_2 kept_2 last_end_2 |- _ =>
      pose proof
        (greedy_prefix_accept__greedy_prefix
           sorted_ps_2 i_2 kept_2 last_end_2 Hi Hbounds Hstate Haccept)
        as Hnext
  end.
  Exists sorted_ps_2 sorted_ed_2 sorted_st_2
    (Znth i_2 sorted_ed_2 0) (kept_2 + 1) (i_2 + 1).
  split_pure_spatial.
  - cancel ((( &( "i" ) )) # Int |-> (i_2 + 1)).
    cancel ((( &( "kept" ) )) # Int |-> (kept_2 + 1)).
    cancel ((( &( "last_end" ) )) # Int |-> (Znth i_2 sorted_ed_2 0)).
    cancel ((( &( "st" ) )) # Ptr |-> st_pre).
    cancel ((( &( "ed" ) )) # Ptr |-> ed_pre).
    cancel ((( &( "intervalsSize" ) )) # Int |-> intervalsSize_pre).
    cancel (IntArray.full st_pre intervalsSize_pre sorted_st_2).
    cancel (IntArray.full ed_pre intervalsSize_pre sorted_ed_2).
  - split_pures.
  all: dump_pre_spatial; try assumption; try lia.
  rewrite Hend. exact Hnext.
Qed.

Lemma proof_of_eraseOverlapIntervals_entail_wit_2_2 : eraseOverlapIntervals_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hpslen : Zlength sorted_ps_2 = Zlength sorted_st_2).
  { lazymatch goal with
    | Hpair : PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2 |- _ =>
        unfold PairIntervals in Hpair; tauto
    end. }
  assert (Hi : 0 <= i_2 < Zlength sorted_ps_2) by lia.
  lazymatch goal with
  | Hpair : PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2,
    Hbounds : IntervalBounds sorted_ps_2 |- _ =>
      pose proof
        (pair_intervals_fields_at__greedy_prefix
           sorted_st_2 sorted_ed_2 sorted_ps_2 i_2
           Hpair Hbounds Hi) as Hfields
  end.
  destruct Hfields as [Hstart [Hend [Hlower [Hproper Hupper]]]].
  assert (Hskip :
            interval_start (Znth i_2 sorted_ps_2 default_interval) <
              last_end_2) by lia.
  lazymatch goal with
  | Hbounds : IntervalBounds sorted_ps_2,
    Hsorted : IntervalsEndSorted sorted_ps_2,
    Hstate : GreedyPrefixState sorted_ps_2 i_2 kept_2 last_end_2 |- _ =>
      pose proof
        (greedy_prefix_skip__greedy_prefix
           sorted_ps_2 i_2 kept_2 last_end_2 Hi
           Hbounds Hsorted Hstate Hskip) as Hnext
  end.
  Exists sorted_ps_2 sorted_ed_2 sorted_st_2
    last_end_2 kept_2 (i_2 + 1).
  split_pure_spatial.
  - cancel ((( &( "i" ) )) # Int |-> (i_2 + 1)).
    cancel ((( &( "kept" ) )) # Int |-> kept_2).
    cancel ((( &( "last_end" ) )) # Int |-> last_end_2).
    cancel ((( &( "st" ) )) # Ptr |-> st_pre).
    cancel ((( &( "ed" ) )) # Ptr |-> ed_pre).
    cancel ((( &( "intervalsSize" ) )) # Int |-> intervalsSize_pre).
    cancel (IntArray.full st_pre intervalsSize_pre sorted_st_2).
    cancel (IntArray.full ed_pre intervalsSize_pre sorted_ed_2).
  - split_pures.
  all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_eraseOverlapIntervals_entail_wit_3 : eraseOverlapIntervals_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hexit : i = intervalsSize_pre) by lia.
  assert (Hsorted_length : Zlength sorted_ps_2 = intervalsSize_pre).
  { unfold PairIntervals in PreH10. lia. }
  assert (Hinput_length : Zlength ps = Zlength sorted_ps_2).
  { unfold IntervalPermutation in PreH12.
    pose proof (Permutation_length PreH12) as Hnatlength.
    rewrite !Zlength_correct.
    now rewrite Hnatlength. }
  assert (Hminimum : MinimumRemovals ps (intervalsSize_pre - kept)).
  { assert (Hgreedy :
        GreedyPrefixState sorted_ps_2 (Zlength ps) kept last_end).
    { replace (Zlength ps) with i by lia. exact PreH14. }
    pose proof
      (greedy_prefix_yields_minimum_removals__optimum_returns
         ps sorted_ps_2 kept last_end Hinput_length PreH12 Hgreedy)
      as Hminimum0.
    replace intervalsSize_pre with (Zlength ps) by lia.
    exact Hminimum0. }
  assert (Hgreedy_full :
      GreedyPrefixState sorted_ps_2 intervalsSize_pre kept last_end).
  { rewrite <- Hexit. exact PreH14. }
  Exists sorted_st_2 sorted_ed_2 sorted_ps_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_eraseOverlapIntervals_return_wit_1 : eraseOverlapIntervals_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists sorted_st sorted_ed sorted_ps.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_eraseOverlapIntervals_return_wit_2 : eraseOverlapIntervals_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre intervalsSize_pre st1_2).
  Intros_p Hst_length.
  assert (Hsorted_length : Zlength ps1_2 = 0).
  { unfold PairIntervals in PreH2. lia. }
  assert (Hinput_length : Zlength ps = 0).
  { unfold IntervalPermutation in PreH4.
    pose proof (Permutation_length PreH4) as Hnatlength.
    rewrite !Zlength_correct in Hsorted_length |- *.
    lia. }
  assert (Hminimum : MinimumRemovals ps 0).
  { apply minimum_removals_empty__optimum_returns. exact Hinput_length. }
  Exists st1_2 ed1_2 ps1_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.
