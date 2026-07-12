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
From SimpleC.EE.LLM_bench.Algorithms.discretize Require Import discretize_goal.
From SimpleC.EE.LLM_bench.Algorithms.discretize Require Import discretize_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_lib.
Local Open Scope sac.

Lemma proof_of_swap_return_wit_1 : swap_return_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_partition_entail_wit_1 : partition_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l).
  - split_pures; dump_pre_spatial; try lia; try reflexivity.
    apply partition_scan_inv_init__partition_scan; lia.
Qed.

Lemma proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  Exists (replace_Znth j (Znth (i + 1) l1_2 0)
            (replace_Znth (i + 1) (Znth j l1_2 0) l1_2)).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre
      (replace_Znth j (Znth (i + 1) l1_2 0)
        (replace_Znth (i + 1) (Znth j l1_2 0) l1_2))).
  - split_pures; dump_pre_spatial; try lia; try reflexivity.
    assert (Hlen_l1 : Zlength l1_2 = n_pre).
    {
      rewrite <- Hlen.
      repeat rewrite Zlength_replace_Znth.
      reflexivity.
    }
    apply partition_scan_inv_step_le__partition_scan; auto; try lia.
Qed.

Lemma proof_of_partition_entail_wit_2_2 : partition_entail_wit_2_2.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l1_2).
  - split_pures; dump_pre_spatial; try lia; try reflexivity.
    apply partition_scan_inv_step_gt__partition_scan; auto; lia.
Qed.

Lemma proof_of_partition_return_wit_1 : partition_return_wit_1.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  Exists (replace_Znth high_pre (Znth (i + 1) l1_2 0)
            (replace_Znth (i + 1) (Znth high_pre l1_2 0) l1_2)).
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre
      (replace_Znth high_pre (Znth (i + 1) l1_2 0)
        (replace_Znth (i + 1) (Znth high_pre l1_2 0) l1_2))).
  - split_pures; dump_pre_spatial; try lia; try reflexivity.
    + assert (Hlen_l1 : Zlength l1_2 = n_pre).
      {
        rewrite <- Hlen.
        repeat rewrite Zlength_replace_Znth.
        reflexivity.
      }
      apply partition_scan_inv_final_permutation__partition_scan
        with (l := l) (l1 := l1_2) (low := low_pre) (high := high_pre)
             (pivot := pivot) (i := i) (j := j);
        auto; try lia.
    + assert (Hlen_l1 : Zlength l1_2 = n_pre).
      {
        rewrite <- Hlen.
        repeat rewrite Zlength_replace_Znth.
        reflexivity.
      }
      apply partition_scan_inv_final_same_outside__partition_scan
        with (l := l) (l1 := l1_2) (low := low_pre) (high := high_pre)
             (pivot := pivot) (i := i) (j := j);
        auto; try lia.
    + assert (Hlen_l1 : Zlength l1_2 = n_pre).
      {
        rewrite <- Hlen.
        repeat rewrite Zlength_replace_Znth.
        reflexivity.
      }
      apply partition_scan_inv_final_swap_partitioned_at__partition_scan
        with (l := l) (l1 := l1_2) (low := low_pre) (high := high_pre)
             (pivot := pivot) (i := i) (j := j);
        auto; try lia.
Qed.

Lemma proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre l1_4).
  Intros.
  Exists l1_4.
  entailer!.
  - pose proof PreH2 as Hsame34_len.
    destruct Hsame34_len as [Hlen34 _].
    assert (Hlen4 : Zlength l1_4 = n_pre).
    { match goal with
      | Hlen : Z.of_nat (length l1_4) = n_pre |- _ =>
          rewrite Zlength_correct; exact Hlen
      end. }
    assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
    {
      pose proof PreH6 as Hsame23_len.
      destruct Hsame23_len as [Hlen23 _].
      eapply partitioned_at_preserved_by_left__quicksort_range.
      - exact PreH5.
      - exact PreH16.
      - exact PreH6.
      - rewrite Hlen23, Hlen34, Hlen4. lia.
      - exact PreH13.
    }
    assert (Hpart : partitioned_at l1_4 left_pre right_pre retval).
    {
      eapply partitioned_at_preserved_by_right__quicksort_range.
      - exact PreH1.
      - exact PreH16.
      - exact PreH2.
      - rewrite Hlen34, Hlen4. lia.
      - exact Hpart3.
    }
    assert (Hsorted_left4 : sorted_range l1_4 left_pre (retval - 1)).
    {
      eapply (sorted_range_ext__quicksort_range l1_3 l1_4 left_pre (retval - 1)).
      - exact PreH16.
      - rewrite Hlen34, Hlen4. lia.
      - exact Hlen34.
      - intros k Hk.
        destruct PreH2 as [_ Heq34].
        apply Heq34.
        + rewrite Hlen34, Hlen4. lia.
        + left. lia.
      - exact PreH7.
    }
    apply sorted_range_from_both with (p := retval).
    + lia.
    + exact Hpart.
    + exact Hsorted_left4.
    + exact PreH3.
  - assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
    {
      eapply (same_outside_range_weaken__quicksort_range
                l1_2 l1_3 left_pre (retval - 1) left_pre right_pre).
      - lia.
      - lia.
      - exact PreH6.
    }
    assert (Hsame34_full : same_outside_range l1_3 l1_4 left_pre right_pre).
    {
      eapply (same_outside_range_weaken__quicksort_range
                l1_3 l1_4 (retval + 1) right_pre left_pre right_pre).
      - lia.
      - lia.
      - exact PreH2.
    }
    eapply same_outside_range_trans__quicksort_range.
    + exact PreH12.
    + eapply same_outside_range_trans__quicksort_range.
      * exact Hsame23_full.
      * exact Hsame34_full.
  - eapply Permutation_trans.
    + exact PreH11.
    + eapply Permutation_trans.
      * exact PreH5.
      * exact PreH1.
Qed. 

Lemma proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre l1_3).
  Intros.
  Exists l1_3.
  entailer!.
  - assert (Hlen3 : Zlength l1_3 = n_pre).
    { match goal with
      | Hlen : Z.of_nat (length l1_3) = n_pre |- _ =>
          rewrite Zlength_correct; exact Hlen
      end. }
    assert (Hpart : partitioned_at l1_3 left_pre right_pre retval).
    {
      pose proof PreH2 as Hsame23_len.
      destruct Hsame23_len as [Hlen23 _].
      eapply partitioned_at_preserved_by_right__quicksort_range; eauto.
      rewrite Hlen23, Hlen3. lia.
    }
    apply sorted_range_from_right with (p := retval).
    + lia.
    + exact Hpart.
    + exact PreH3.
  - assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
    {
      eapply (same_outside_range_weaken__quicksort_range
                l1_2 l1_3 (retval + 1) right_pre left_pre right_pre).
      - lia.
      - lia.
      - exact PreH2.
    }
    eapply same_outside_range_trans__quicksort_range.
    + exact PreH9.
    + exact Hsame23_full.
  - eapply Permutation_trans.
    + exact PreH8.
    + exact PreH1.
Qed. 

Lemma proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre l1_3).
  Intros.
  Exists l1_3.
  entailer!.
  - pose proof PreH3 as Hsame23_len.
    destruct Hsame23_len as [Hlen23 _].
    assert (Hlen3 : Zlength l1_3 = n_pre).
    { match goal with
      | Hlen : Z.of_nat (length l1_3) = n_pre |- _ =>
          rewrite Zlength_correct; exact Hlen
      end. }
    assert (Hpart : partitioned_at l1_3 left_pre right_pre retval).
    {
      assert (Hrightlen : right_pre < Zlength l1_2).
      { rewrite Hlen23, Hlen3. lia. }
      eapply (partitioned_at_preserved_by_left__quicksort_range
                l1_2 l1_3 left_pre right_pre retval).
      - exact PreH2.
      - exact PreH13.
      - exact PreH3.
      - exact Hrightlen.
      - exact PreH10.
    }
    apply sorted_range_from_left with (p := retval).
    + lia.
    + exact Hpart.
    + exact PreH4.
  - assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
    {
      eapply (same_outside_range_weaken__quicksort_range
                l1_2 l1_3 left_pre (retval - 1) left_pre right_pre).
      - lia.
      - lia.
      - exact PreH3.
    }
    eapply same_outside_range_trans__quicksort_range.
    + exact PreH9.
    + exact Hsame23_full.
  - eapply Permutation_trans.
    + exact PreH8.
    + exact PreH2.
Qed. 

Lemma proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4.
Proof.
  pre_process.
  Exists l.
  entailer!.
  - apply sorted_range_base. lia.
  - apply same_outside_range_refl__quicksort_range.
Qed. 

Lemma proof_of_int_array_quicksort_return_wit_1 : int_array_quicksort_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre l1_2).
  Intros.
  Exists l1_2.
  entailer!.
  eapply sorted_range_implies_increasing__quicksort_range.
  rewrite Zlength_correct.
  match goal with
  | Hlen : Z.of_nat (length l1_2) = n_pre |- _ =>
      rewrite Hlen
  end.
  exact PreH3.
Qed. 

Lemma proof_of_discretize_safety_wit_8 : discretize_safety_wit_8.
Proof.
  pre_process.
  unfold discretize_result in PreH4.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_discretize_entail_wit_1 : discretize_entail_wit_1.
Proof.
  pre_process.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg dest_map_pre n_pre).
  change (sublist 0 0 src_l) with (@nil Z).
  rewrite (IntArray.full_empty dest_map_pre 0).
  split_pure_spatial.
  - cancel (IntArray.undef_seg dest_map_pre 0 n_pre).
    cancel (IntArray.full src_pre n_pre src_l).
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_discretize_entail_wit_2 : discretize_entail_wit_2.
Proof.
  pre_process.
  replace (sublist 0 (i + 1) src_l)
    with (sublist 0 i src_l ++ Znth i src_l 0 :: nil).
  2: {
    rewrite (sublist_split 0 (i + 1) i src_l) by lia.
    rewrite (sublist_single 0 i src_l) by lia.
    reflexivity.
  }
  split_pure_spatial.
  - cancel (IntArray.full dest_map_pre (i + 1)
      (sublist 0 i src_l ++ Znth i src_l 0 :: nil)).
    cancel (IntArray.undef_seg dest_map_pre (i + 1) n_pre).
    cancel (IntArray.full src_pre n_pre src_l).
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_discretize_entail_wit_3 : discretize_entail_wit_3.
Proof.
  pre_process.
  assert (Hi : i = n_pre) by lia.
  subst i.
  rewrite (sublist_self src_l n_pre) by exact (eq_sym PreH2).
  rewrite IntArray.undef_seg_empty.
  split_pure_spatial.
  - cancel (IntArray.full src_pre n_pre src_l).
    cancel (IntArray.full dest_map_pre n_pre src_l).
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_discretize_entail_wit_4 : discretize_entail_wit_4.
Proof.
  pre_process.
  Exists l1. Exists l1.
  split_pure_spatial.
  - cancel (IntArray.full src_pre n_pre src_l).
    cancel (IntArray.full dest_map_pre n_pre l1).
  - split_pures; dump_pre_spatial; auto; try lia.
    eapply dedup_scan_inv_init__discretize_dedup; eauto.
Qed. 

Lemma proof_of_discretize_entail_wit_5_1 : discretize_entail_wit_5_1.
Proof.
  pre_process.
  Exists sorted_l_2.
  Exists (replace_Znth (slow + 1) (Znth fast cur_l_2 0) cur_l_2).
  split_pure_spatial.
  - cancel (IntArray.full src_pre n_pre src_l).
    cancel (IntArray.full dest_map_pre n_pre
      (replace_Znth (slow + 1) (Znth fast cur_l_2 0) cur_l_2)).
  - split_pures; dump_pre_spatial; auto; try lia.
    pose proof PreH10 as Hinv.
    unfold dedup_scan_inv in Hinv.
    destruct Hinv as [Hsrc_sorted_len _].
    eapply dedup_scan_inv_step_new__discretize_dedup; eauto; lia.
Qed. 

Lemma proof_of_discretize_entail_wit_5_2 : discretize_entail_wit_5_2.
Proof.
  pre_process.
  Exists sorted_l_2. Exists cur_l_2.
  split_pure_spatial.
  - cancel (IntArray.full src_pre n_pre src_l).
    cancel (IntArray.full dest_map_pre n_pre cur_l_2).
  - split_pures; dump_pre_spatial; auto; try lia.
    pose proof PreH10 as Hinv.
    unfold dedup_scan_inv in Hinv.
    destruct Hinv as [Hsrc_sorted_len _].
    eapply dedup_scan_inv_step_duplicate__discretize_dedup; eauto; lia.
Qed. 

Lemma proof_of_discretize_entail_wit_6 : discretize_entail_wit_6.
Proof.
  pre_process.
  Exists cur_l.
  split_pure_spatial.
  - cancel (IntArray.full src_pre n_pre src_l).
    cancel (IntArray.full dest_map_pre n_pre cur_l).
  - split_pures; dump_pre_spatial; auto; try lia.
    replace fast with n_pre in * by lia.
    eapply dedup_scan_inv_to_discretize_result__discretize_dedup; eauto.
Qed. 

Lemma proof_of_query_forward_safety_wit_4 : query_forward_safety_wit_4.
Proof.
  left.
  pre_process.
  pose proof (midpoint_between_bounds__query_forward_search low high PreH1) as Hmid.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_query_forward_entail_wit_1 : query_forward_entail_wit_1.
Proof.
  left.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full map_pre map_size_pre map_l).
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      apply query_forward_search_inv_init__query_forward_search; lia.
Qed.

Lemma proof_of_query_forward_entail_wit_2 : query_forward_entail_wit_2.
Proof.
  left.
  pre_process.
  pose proof (midpoint_between_bounds__query_forward_search low high PreH1) as Hmid.
  split_pure_spatial.
  - cancel (IntArray.full map_pre map_size_pre map_l).
  - split_pures.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
Qed.

Lemma proof_of_query_forward_entail_wit_3_1 : query_forward_entail_wit_3_1.
Proof.
  left.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full map_pre map_size_pre map_l).
  - split_pures.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial.
      apply query_forward_search_inv_step_right__query_forward_search
        with (low := low);
        try eassumption; lia.
Qed.

Lemma proof_of_query_forward_entail_wit_3_2 : query_forward_entail_wit_3_2.
Proof.
  left.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full map_pre map_size_pre map_l).
  - split_pures.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      apply query_forward_search_inv_step_left__query_forward_search
        with (high := high);
        try eassumption; lia.
Qed.

Lemma proof_of_query_forward_entail_wit_4 : query_forward_entail_wit_4.
Proof.
  left.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full map_pre map_size_pre map_l).
  - split_pures.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial.
      apply query_forward_result_not_found__query_forward_search
        with (low := low) (high := high); try assumption.
Qed.

Lemma proof_of_query_forward_return_wit_2 : query_forward_return_wit_2.
Proof.
  left.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full map_pre map_size_pre map_l).
  - dump_pre_spatial.
    apply query_forward_result_found_unique__query_forward_search;
      try eassumption; lia.
Qed.
