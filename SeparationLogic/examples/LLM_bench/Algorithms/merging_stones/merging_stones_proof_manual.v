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
From SimpleC.EE.LLM_bench.Algorithms.merging_stones Require Import merging_stones_goal.
From SimpleC.EE.LLM_bench.Algorithms.merging_stones Require Import merging_stones_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib.
Local Open Scope sac.

Lemma proof_of_mergingStones_safety_wit_6 : mergingStones_safety_wit_6.
Proof.
  left.
  pre_process.
  entailer!; replace (i - 0) with i by lia; lia.
Qed.

Lemma proof_of_mergingStones_safety_wit_20 : mergingStones_safety_wit_20.
Proof.
  aggressive_pre_process.
  all: pose proof
    (StonePrefixDone_interval_bounds__prefix_math
       stones_l prefix_l n_pre left (left + len - 1 + 1)
       PreH10 PreH11 ltac:(lia) ltac:(lia)) as Hinterval.
  all: destruct Hinterval as [Hinterval_low Hinterval_high].
  all: entailer!.
Qed.

Lemma proof_of_mergingStones_entail_wit_1 : mergingStones_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - sep_apply (IntArray.seg_single prefix_pre 0 0).
    replace (0 + 1) with 1 by lia.
    cancel (IntArray.full stones_pre n_pre stones_l).
    cancel (IntArray.seg prefix_pre 0 1 (0 :: nil)).
    cancel (IntArray.undef_seg prefix_pre 1 (n_pre + 1)).
    cancel (IntArray2.full dp_pre n_pre n_pre dp_init).
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia).
    unfold StonePrefixProgress.
    repeat split; simpl; try assumption; try lia.
    intros k Hk.
    assert (k = 0) by lia.
    subst k.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_mergingStones_entail_wit_2 : mergingStones_entail_wit_2.
Proof.
  pre_process.
  Exists (0 :: nil).
  split_pure_spatial.
  - replace (0 + 1) with 1 by lia.
    cancel (IntArray.full stones_pre n_pre stones_l).
    cancel (IntArray.seg prefix_pre 0 1 (0 :: nil)).
    cancel (IntArray.undef_seg prefix_pre 1 (n_pre + 1)).
    cancel (IntArray2.full dp_pre n_pre n_pre dp_init).
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia).
Qed.

Lemma proof_of_mergingStones_entail_wit_3 : mergingStones_entail_wit_3.
Proof.
  aggressive_pre_process.
  all: pose proof
    (StoneMassesBounded_Znth__prefix_math
       stones_l n_pre i PreH7 ltac:(lia)) as Hstone.
  all: pose proof
    (StonePrefixProgress_value_bounds__prefix_math
       stones_l prefix_l_2 n_pre i i
       PreH7 PreH3 PreH9 ltac:(lia)) as Hprefix.
  all: destruct Hstone as [Hstone_low Hstone_high].
  all: destruct Hprefix as [Hprefix_low Hprefix_high].
  all: entailer!.
Qed.

Lemma proof_of_mergingStones_entail_wit_4 : mergingStones_entail_wit_4.
Proof.
  aggressive_pre_process.
  replace (i - 0) with i by lia.
  apply StonePrefixProgress_extend__prefix_math.
  - exact PreH8.
  - lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_5 : mergingStones_entail_wit_5.
Proof.
  pre_process.
  assert (i = n_pre) by lia.
  subst i.
  Exists prefix_l_2.
  split_pure_spatial.
  - cancel.
    unfold IntArray.full, IntArray.undef_seg, store_array.
    replace (Z.to_nat (n_pre + 1 - (n_pre + 1))) with O by lia.
    simpl.
    Intros.
    reflexivity.
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia).
    unfold StonePrefixDone, StonePrefixProgress in *.
    intuition.
Qed.

Lemma proof_of_mergingStones_entail_wit_6 : mergingStones_entail_wit_6.
Proof.
  pre_process.
  Exists dp_init prefix_l_2.
  split_pure_spatial.
  - cancel (IntArray.full stones_pre n_pre stones_l).
    cancel (IntArray.full prefix_pre (n_pre + 1) prefix_l_2).
    cancel (IntArray2.full dp_pre n_pre n_pre dp_init).
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia).
    unfold StoneZeroRows.
    split.
    + exact PreH7.
    + split.
      * lia.
      * intros r c Hr Hc.
        lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_7 : mergingStones_entail_wit_7.
Proof.
  aggressive_pre_process.
  unfold StoneZeroRows in PreH10.
  unfold StoneZeroProgress.
  destruct PreH10 as [Hshape [Hrow Hzero]].
  unfold StoneTableShape in Hshape.
  destruct Hshape as [Htable_len Hrow_len].
  repeat split; try lia; auto.
Qed.

Lemma proof_of_mergingStones_entail_wit_8 : mergingStones_entail_wit_8.
Proof.
  aggressive_pre_process.
  Exists (replace_Znth row
    (replace_Znth col 0 (Znth row dp_l_2 __default__List_Z)) dp_l_2).
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_pre + row * n_pre * sizeof (INT)) col n_pre 0
      (Znth row dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      dp_pre + row * n_pre * sizeof (INT) + col * sizeof (INT) =
      dp_pre + (row * n_pre + col) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_pre row n_pre n_pre dp_l_2
      (replace_Znth col 0 (Znth row dp_l_2 __default__List_Z))) as Hmerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_pre n_pre row) n_pre
      (replace_Znth col 0 (Znth row dp_l_2 __default__List_Z))) with
      (IntArray.full (dp_pre + row * n_pre * sizeof (INT)) n_pre
        (replace_Znth col 0 (Znth row dp_l_2 __default__List_Z))) in Hmerge.
    sep_apply Hmerge; try lia.
    cancel.
  - split_pures.
    all: try (dump_pre_spatial; lia).
    all: try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    apply StoneZeroProgress_store__zero_table; assumption.
Qed.

Lemma proof_of_mergingStones_entail_wit_9 : mergingStones_entail_wit_9.
Proof.
  aggressive_pre_process.
  unfold StoneZeroProgress in PreH12.
  destruct PreH12 as
    [Hshape [Hrow [Hcol [Hzero_rows Hzero_current]]]].
  unfold StoneTableShape in Hshape.
  destruct Hshape as [Htable_len Hrow_len].
  unfold StoneZeroRows, StoneTableShape.
  repeat split; try assumption; try lia.
  intros r c Hr Hc.
  assert (r < row \/ r = row) by lia.
  destruct H as [Hlt | Heq].
  - apply Hzero_rows; lia.
  - subst r. apply Hzero_current. lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_11 : mergingStones_entail_wit_11.
Proof.
  aggressive_pre_process.
  - assert (row = n_pre) by lia.
    subst row.
    apply StoneLenDone_two_of_zero__zero_table; assumption.
  - assert (row = n_pre) by lia.
    subst row.
    exact PreH10.
Qed.

Lemma proof_of_mergingStones_entail_wit_13 : mergingStones_entail_wit_13.
Proof.
  pre_process.
  Exists dp_l_2 prefix_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    eapply StoneLenDone_to_initial_left_progress__table_progress; eauto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_14 : mergingStones_entail_wit_14.
Proof.
  aggressive_pre_process.
  all: pose proof
    (StoneSplitProgress_initial__prefix_math
       stones_l dp_l_2 n_pre len left PreH12 PreH4) as Hsplit.
  all: pose proof
    (StonePrefixDone_interval_bounds__prefix_math
       stones_l prefix_l n_pre left (left + len - 1 + 1)
       PreH10 PreH11 ltac:(lia) ltac:(lia)) as Hinterval.
  all: destruct Hinterval as [Hinterval_low Hinterval_high].
  all: pose proof
    (StonePrefixDone_interval_sum__prefix_math
       stones_l prefix_l n_pre left (left + len - 1 + 1)
       PreH11 ltac:(lia) ltac:(lia)) as Hsum.
  all: entailer!.
Qed.

Lemma proof_of_mergingStones_entail_wit_16 : mergingStones_entail_wit_16.
Proof.
  aggressive_pre_process.
  all: entailer!.
  all: pose proof
         (StoneSplitProgress_child_bounds__interval_min_core
            stones_l dp_l_2 n_pre len left split right best __default__List_Z
            PreH20 PreH3 PreH22 PreH8 ltac:(lia) PreH10) as Hchildren;
       destruct Hchildren as [[Hleft_low Hleft_high]
                              [Hright_low Hright_high]];
       first [exact Hleft_low | exact Hleft_high |
              exact Hright_low | exact Hright_high].
Qed.

Lemma proof_of_mergingStones_entail_wit_17 : mergingStones_entail_wit_17.
Proof.
  aggressive_pre_process.
  pose proof
    (StoneSplitProgress_table_shape__interval_min_core
       stones_l dp_l n_pre len left split best PreH22) as Htable_shape.
  unfold StoneTableShape in Htable_shape.
  destruct Htable_shape as [Htable_length Hrow_length].
  assert (Hrow_length_left :
    Zlength (Znth left dp_l __default__List_Z) = n_pre).
  {
    rewrite (Znth_indep dp_l left __default__List_Z nil)
      by (rewrite Htable_length; lia).
    apply Hrow_length.
    lia.
  }
  Exists dp_l.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_pre + left * n_pre * sizeof (INT)) split n_pre
      (Znth split (Znth left dp_l __default__List_Z) 0)
      (Znth left dp_l __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      dp_pre + left * n_pre * sizeof (INT) + split * sizeof (INT) =
      dp_pre + (left * n_pre + split) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    try rewrite replace_Znth_Znth by lia.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_pre left n_pre n_pre dp_l
      (Znth left dp_l __default__List_Z)) as Hmerge.
    change
      (IntArray2.ElemArray.full
        (IntArray2.row_addr dp_pre n_pre left) n_pre
        (Znth left dp_l __default__List_Z))
      with
      (IntArray.full
        (dp_pre + left * n_pre * sizeof(INT)) n_pre
        (Znth left dp_l __default__List_Z))
      in Hmerge.
    sep_apply Hmerge; try lia.
    try rewrite replace_Znth_Znth by lia.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_18 : mergingStones_entail_wit_18.
Proof.
  right.
  pre_process.
  pose proof
    (StoneSplitProgress_candidate_facts__interval_min_core
       stones_l dp_l n_pre len left split right best interval_sum
       __default__List_Z PreH21 PreH4 PreH23 PreH9 ltac:(lia)
       PreH12 PreH14) as Hcandidate.
  cbn in Hcandidate.
  rewrite <- PreH13 in Hcandidate.
  destruct Hcandidate as [Hcandidate_bounds Hcandidate_split].
  Exists dp_l.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_pre + (split + 1) * n_pre * sizeof (INT)) right n_pre
      (Znth right (Znth (split + 1) dp_l __default__List_Z) 0)
      (Znth (split + 1) dp_l __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      dp_pre + (((split + 1) * n_pre + right) * sizeof (INT)) =
      dp_pre + (split + 1) * n_pre * sizeof (INT) + right * sizeof (INT)) by lia.
    rewrite Hcell_addr.
    sep_apply Hrowmerge; try lia.
    try rewrite replace_Znth_Znth by lia.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_pre (split + 1) n_pre n_pre dp_l
      (Znth (split + 1) dp_l __default__List_Z)) as Hmerge.
    change
      (IntArray2.ElemArray.full
        (IntArray2.row_addr dp_pre n_pre (split + 1)) n_pre
        (Znth (split + 1) dp_l __default__List_Z))
      with
      (IntArray.full
        (dp_pre + (split + 1) * n_pre * sizeof(INT)) n_pre
        (Znth (split + 1) dp_l __default__List_Z))
      in Hmerge.
    sep_apply Hmerge; try lia.
    try rewrite replace_Znth_Znth by lia.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_19_1 : mergingStones_entail_wit_19_1.
Proof.
  aggressive_pre_process.
  entailer!.
  eapply StoneSplitProgress_replace_best__split_loop_step; eauto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_19_2 : mergingStones_entail_wit_19_2.
Proof.
  aggressive_pre_process.
  entailer!.
  - eapply StoneSplitProgress_keep_best__split_loop_step; eauto; lia.
  - unfold StoneSplitProgress in PreH21.
    cbn in PreH21.
    lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_20 : mergingStones_entail_wit_20.
Proof.
  right.
  pre_process.
  assert (Hinterval : 2 <= interval_sum <= 8000).
  {
    subst interval_sum.
    eapply stone_interval_sum_bounds__arithmetic_safety; eauto; lia.
  }
  unfold StonePrefixDone, StonePrefixProgress in PreH21.
  unfold StoneMassesBounded in PreH20.
  entailer!; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_21 : mergingStones_entail_wit_21.
Proof.
  aggressive_pre_process.
  all: assert (Hsplit_right : split = right) by lia;
       subst split.
  all: pose proof
         (StoneSplitProgress_complete__interval_min_core
            stones_l dp_l_2 n_pre len left right best
            PreH8 PreH9 PreH10 PreH22) as Hminimum.
  all: pose proof
         (StoneIntervalMin_bounds__interval_min_core
            stones_l n_pre left right best PreH20 PreH3 ltac:(lia)
            PreH10 Hminimum) as Hminimum_bounds.
  all: destruct Hminimum_bounds as [Hminimum_low Hminimum_high].
  all: entailer!.
  all: first [exact Hminimum | exact PreH22 | exact Hminimum_high | lia].
Qed.

Lemma proof_of_mergingStones_entail_wit_22 : mergingStones_entail_wit_22.
Proof.
  pre_process.
  Exists dp_l
    (replace_Znth left
      (replace_Znth right best (Znth left dp_l __default__List_Z))
      dp_l)
    prefix_l_2.
  split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      (dp_pre + left * n_pre * sizeof (INT)) right n_pre best
      (Znth left dp_l __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      dp_pre + (left * n_pre + right) * sizeof (INT) =
      dp_pre + left * n_pre * sizeof (INT) + right * sizeof (INT)) by lia.
    rewrite Hcell_addr.
    sep_apply Hrowmerge; try lia.
    pose proof (IntArray2.missing_i_merge_to_full
      dp_pre left n_pre n_pre dp_l
      (replace_Znth right best (Znth left dp_l __default__List_Z)))
      as Hmerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_pre n_pre left) n_pre
      (replace_Znth right best (Znth left dp_l __default__List_Z)))
      with (IntArray.full
        (dp_pre + left * n_pre * sizeof(INT)) n_pre
        (replace_Znth right best (Znth left dp_l __default__List_Z)))
      in Hmerge.
    sep_apply Hmerge; try lia.
    repeat cancel.
  - split_pures;
      try solve [dump_pre_spatial; eauto; try lia].
    + dump_pre_spatial.
      unfold StoneUpdatedCell.
      unfold StoneSplitProgress in PreH17.
      destruct PreH17 as (Hleft_progress & _).
      unfold StoneLeftProgress in Hleft_progress.
      destruct Hleft_progress as (Hdone & _).
      unfold StoneLenDone in Hdone.
      destruct Hdone as (_ & Hshape & _).
      unfold StoneTableShape in Hshape.
      destruct Hshape as (Htable_len & Hrow_len).
      repeat split.
      * exact PreH5.
      * rewrite Htable_len. lia.
      * lia.
      * rewrite (Hrow_len left) by lia. lia.
      * rewrite (Znth_indep dp_l left __default__List_Z (@nil Z)) by
            (rewrite Htable_len; lia).
        reflexivity.
      * exact PreH18.
    + dump_pre_spatial.
      unfold StoneSplitProgress in PreH17.
      destruct PreH17 as (Hleft_progress & _).
      pose proof Hleft_progress as Hleft_shape.
      unfold StoneLeftProgress in Hleft_shape.
      destruct Hleft_shape as (Hdone & _).
      unfold StoneLenDone in Hdone.
      destruct Hdone as (_ & Hshape & _).
      unfold StoneTableShape in Hshape.
      destruct Hshape as (Htable_len & Hrow_len).
      rewrite (Znth_indep dp_l left __default__List_Z (@nil Z)) by
          (rewrite Htable_len; lia).
      eapply StoneUpdatedCell_to_next_left_progress__table_progress.
      * exact Hleft_progress.
      * exact PreH7.
      * exact PreH6.
      * unfold StoneUpdatedCell.
        repeat split.
        -- exact PreH5.
        -- rewrite Htable_len. lia.
        -- lia.
        -- rewrite (Hrow_len left) by lia. lia.
        -- exact PreH18.
Qed.

Lemma proof_of_mergingStones_entail_wit_23 : mergingStones_entail_wit_23.
Proof.
  pre_process.
  Exists dp_new prefix_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!;
      unfold StonePrefixDone, StonePrefixProgress in PreH14;
      unfold StoneMassesBounded in PreH13;
      tauto.
Qed.

Lemma proof_of_mergingStones_entail_wit_24 : mergingStones_entail_wit_24.
Proof.
  pre_process.
  Exists dp_l_2 prefix_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    eapply StoneLeftProgress_to_next_len_done__table_progress; eauto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_25 : mergingStones_entail_wit_25.
Proof.
  pre_process.
  Exists dp_l_2 prefix_l_2.
  unfold StoneMassesBounded in PreH5.
  unfold StonePrefixDone, StonePrefixProgress in PreH6.
  entailer!.
Qed.

Lemma proof_of_mergingStones_entail_wit_26 : mergingStones_entail_wit_26.
Proof.
  aggressive_pre_process.
  all: entailer!.
  all: pose proof
         (StoneLenDone_final_facts__interval_min_core
            stones_l dp_l_2 n_pre len __default__List_Z
            PreH2 PreH3 PreH8 PreH1 PreH5 PreH10) as Hfinal;
       cbn in Hfinal;
       destruct Hfinal as
         [Hdone_final [Hminimum [Hanswer_low Hanswer_high]]];
       first [exact Hdone_final | exact Hminimum |
              exact Hanswer_low | exact Hanswer_high | lia].
Qed.

Lemma proof_of_mergingStones_return_wit_1 : mergingStones_return_wit_1.
Proof.
  pre_process.
  Exists dp_l_2 prefix_l_2.
  pose proof (IntArray.missing_i_merge_to_full
    (dp_pre + 0 * n_pre * sizeof (INT)) (n_pre - 1) n_pre
    (Znth (n_pre - 1) (Znth 0 dp_l_2 __default__List_Z) 0)
    (Znth 0 dp_l_2 __default__List_Z)) as Hrowmerge.
  assert (Hcell_addr :
    dp_pre + (0 * n_pre + (n_pre - 1)) * sizeof (INT) =
    dp_pre + 0 * n_pre * sizeof (INT) + (n_pre - 1) * sizeof (INT)) by lia.
  rewrite Hcell_addr.
  sep_apply Hrowmerge; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_pre 0 n_pre n_pre dp_l_2
    (replace_Znth (n_pre - 1)
       (Znth (n_pre - 1) (Znth 0 dp_l_2 __default__List_Z) 0)
       (Znth 0 dp_l_2 __default__List_Z))) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr dp_pre n_pre 0) n_pre
    (replace_Znth (n_pre - 1)
       (Znth (n_pre - 1) (Znth 0 dp_l_2 __default__List_Z) 0)
       (Znth 0 dp_l_2 __default__List_Z))) with
    (IntArray.full (dp_pre + 0 * n_pre * sizeof (INT)) n_pre
      (replace_Znth (n_pre - 1)
         (Znth (n_pre - 1) (Znth 0 dp_l_2 __default__List_Z) 0)
         (Znth 0 dp_l_2 __default__List_Z))) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth.
  rewrite replace_Znth_Znth.
  entailer!.
Qed.
