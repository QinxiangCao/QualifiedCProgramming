Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index Require Import quicksort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_lib.
Local Open Scope sac.

Lemma proof_of_partition_entail_wit_1 : partition_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  entailer!.
  unfold partition_scan_inv.
  split.
  - apply Permutation_refl.
  - split.
    + apply same_outside_range_refl.
    + split.
      * reflexivity.
      * split.
        -- intros k Hk. lia.
        -- intros k Hk. lia.
Qed.

Lemma proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre
                (replace_Znth j (Znth (i + 1) l1_2 0)
                   (replace_Znth (i + 1) (Znth j l1_2 0) l1_2))).
  Intros.
  Exists (replace_Znth j (Znth (i + 1) l1_2 0)
            (replace_Znth (i + 1) (Znth j l1_2 0) l1_2)).
  entailer!.
  eapply partition_scan_inv_swap; eauto.
  - match goal with
    | Hlen_swapped : Z.of_nat (length _) = n_pre |- _ =>
        rewrite <- Zlength_correct in Hlen_swapped;
        rewrite !Zlength_replace_Znth in Hlen_swapped;
        lia
    end.
Qed.

Lemma proof_of_partition_entail_wit_2_2 : partition_entail_wit_2_2.
Proof.
  pre_process.
  Exists l1_2.
  entailer!.
  unfold partition_scan_inv in *.
  destruct PreH10 as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  split.
  - exact Hperm.
  - split.
    + exact Hsame.
    + split.
      * exact Hpivot.
      * split.
        -- intros k Hk. apply Hle. lia.
        -- intros k Hk.
           destruct (Z.eq_dec k j) as [-> | Hneq].
           ++ lia.
           ++ apply Hgt. lia.
Qed.

Lemma proof_of_partition_return_wit_1 : partition_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre
                (replace_Znth high_pre (Znth (i + 1) l1_2 0)
                   (replace_Znth (i + 1) (Znth high_pre l1_2 0) l1_2))).
  Intros.
  Exists (replace_Znth high_pre (Znth (i + 1) l1_2 0)
            (replace_Znth (i + 1) (Znth high_pre l1_2 0) l1_2)).
  entailer!.
  - assert (Hj : j = high_pre) by lia.
    subst j.
    assert (Hlenarr : high_pre < Zlength l1_2).
    {
      match goal with
      | Hlen_swapped : Z.of_nat (length _) = n_pre |- _ =>
          rewrite <- Zlength_correct in Hlen_swapped;
          rewrite !Zlength_replace_Znth in Hlen_swapped;
          lia
      end.
    }
    eapply partitioned_at_after_final_swap; eauto; lia.
  - destruct PreH9 as [_ [Hsame _]].
    assert (Hlenarr : high_pre < Zlength l1_2).
    {
      match goal with
      | Hlen_swapped : Z.of_nat (length _) = n_pre |- _ =>
          rewrite <- Zlength_correct in Hlen_swapped;
          rewrite !Zlength_replace_Znth in Hlen_swapped;
          lia
      end.
    }
    eapply same_outside_range_trans.
    + exact Hsame.
    + apply same_outside_range_swap_inside; lia.
  - destruct PreH9 as [Hperm _].
    assert (Hlenarr : high_pre < Zlength l1_2).
    {
      match goal with
      | Hlen_swapped : Z.of_nat (length _) = n_pre |- _ =>
          rewrite <- Zlength_correct in Hlen_swapped;
          rewrite !Zlength_replace_Znth in Hlen_swapped;
          lia
      end.
    }
    eapply Permutation_trans.
    + exact Hperm.
    + apply permutation_swap_Znth; lia.
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
      eapply partitioned_at_preserved_by_right; eauto.
      rewrite Hlen23, Hlen3. lia.
    }
    apply sorted_range_from_right with (p := retval).
    + lia.
    + exact Hpart.
    + exact PreH3.
  - assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
    {
      eapply (same_outside_range_weaken
                l1_2 l1_3 (retval + 1) right_pre left_pre right_pre).
      - lia.
      - lia.
      - exact PreH2.
    }
    eapply same_outside_range_trans.
    + exact PreH9.
    + exact Hsame23_full.
  - eapply Permutation_trans.
    + exact PreH8.
    + exact PreH1.
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
      eapply partitioned_at_preserved_by_left.
      - exact PreH5.
      - exact PreH16.
      - exact PreH6.
      - rewrite Hlen23, Hlen34, Hlen4. lia.
      - exact PreH13.
    }
    assert (Hpart : partitioned_at l1_4 left_pre right_pre retval).
    {
      eapply partitioned_at_preserved_by_right.
      - exact PreH1.
      - exact PreH16.
      - exact PreH2.
      - rewrite Hlen34, Hlen4. lia.
      - exact Hpart3.
    }
    assert (Hsorted_left4 : sorted_range l1_4 left_pre (retval - 1)).
    {
      eapply (sorted_range_ext l1_3 l1_4 left_pre (retval - 1)).
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
      eapply (same_outside_range_weaken
                l1_2 l1_3 left_pre (retval - 1) left_pre right_pre).
      - lia.
      - lia.
      - exact PreH6.
    }
    assert (Hsame34_full : same_outside_range l1_3 l1_4 left_pre right_pre).
    {
      eapply (same_outside_range_weaken
                l1_3 l1_4 (retval + 1) right_pre left_pre right_pre).
      - lia.
      - lia.
      - exact PreH2.
    }
    eapply same_outside_range_trans.
    + exact PreH12.
    + eapply same_outside_range_trans.
      * exact Hsame23_full.
      * exact Hsame34_full.
  - eapply Permutation_trans.
    + exact PreH11.
    + eapply Permutation_trans.
      * exact PreH5.
      * exact PreH1.
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
      eapply (partitioned_at_preserved_by_left
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
      eapply (same_outside_range_weaken
                l1_2 l1_3 left_pre (retval - 1) left_pre right_pre).
      - lia.
      - lia.
      - exact PreH3.
    }
    eapply same_outside_range_trans.
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
  - apply same_outside_range_refl.
Qed.

Lemma proof_of_quicksort_return_wit_1 : quicksort_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length arr_pre n_pre l1_2).
  Intros.
  Exists l1_2.
  entailer!.
  eapply sorted_range_implies_increasing.
  rewrite Zlength_correct.
  match goal with
  | Hlen : Z.of_nat (length l1_2) = n_pre |- _ =>
      rewrite Hlen
  end.
  exact PreH3.
Qed.
