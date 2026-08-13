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

Lemma proof_of_mergingStones_safety_wit_6_split_goal_1 : mergingStones_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  replace (i - 0) with i by lia.
  lia.
Qed.

Lemma proof_of_mergingStones_safety_wit_6_split_goal_2 : mergingStones_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  replace (i - 0) with i by lia.
  lia.
Qed.

Lemma proof_of_mergingStones_safety_wit_6 : mergingStones_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_mergingStones_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_mergingStones_safety_wit_20_split_goal_1 : mergingStones_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof
    (StonePrefixDone_interval_bounds__prefix_math
       stones_l prefix_l n_pre left (left + len)
       PreH10 PreH11 ltac:(lia) ltac:(lia)) as Hbounds.
  replace (((left + len) - 1) + 1) with (left + len) by lia.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_mergingStones_safety_wit_20_split_goal_2 : mergingStones_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof
    (StonePrefixDone_interval_bounds__prefix_math
       stones_l prefix_l n_pre left (left + len)
       PreH10 PreH11 ltac:(lia) ltac:(lia)) as Hbounds.
  replace (((left + len) - 1) + 1) with (left + len) by lia.
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_mergingStones_safety_wit_20 : mergingStones_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_mergingStones_safety_wit_20_split_goal_2.
Qed.

Lemma proof_of_mergingStones_entail_wit_1_split_goal_1 : mergingStones_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold StonePrefixProgress.
  repeat split; try assumption; try lia.
  intros k Hk.
  assert (k = 0) by lia.
  subst k.
  reflexivity.
Qed.

Lemma proof_of_mergingStones_entail_wit_1_split_goal_spatial : mergingStones_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply_l_atomic (IntArray.seg_single prefix_pre 0 0).
  change (0 + 1) with 1.
  cancel (IntArray.seg prefix_pre 0 1 (0 :: nil)).
Qed.

Lemma proof_of_mergingStones_entail_wit_1 : mergingStones_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_mergingStones_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_mergingStones_entail_wit_2 : mergingStones_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia).
  Exists (0 :: nil).
  split_pure_spatial.
  - change (0 + 1) with 1.
    repeat cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_3_split_goal_1 : mergingStones_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StoneMassesBounded_Znth__prefix_math
       stones_l n_pre i PreH7 ltac:(lia)) as Hmass.
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_3_split_goal_2 : mergingStones_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StoneMassesBounded_Znth__prefix_math
       stones_l n_pre i PreH7 ltac:(lia)) as Hmass.
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_3_split_goal_3 : mergingStones_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StonePrefixProgress_value_bounds__prefix_math
       stones_l prefix_l_2 n_pre i i PreH7 PreH3 PreH9 ltac:(lia))
    as Hprefix.
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_3_split_goal_4 : mergingStones_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StonePrefixProgress_value_bounds__prefix_math
       stones_l prefix_l_2 n_pre i i PreH7 PreH3 PreH9 ltac:(lia))
    as Hprefix.
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_3 : mergingStones_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_mergingStones_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_mergingStones_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_mergingStones_entail_wit_4_split_goal_1 : mergingStones_entail_wit_4_split_goal_1.
Proof.
  intros n_pre dp_init stones_l prefix_l_2 i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    PreH9 PreH10 PreH11 PreH12.
  replace (i - 0) with i by lia.
  apply StonePrefixProgress_extend__prefix_math.
  - exact PreH8.
  - lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_4 : mergingStones_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mergingStones_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_mergingStones_entail_wit_5_split_goal_1 : mergingStones_entail_wit_5_split_goal_1.
Proof.
  intros n_pre dp_init stones_l prefix_l_2 i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  assert (i = n_pre) by lia.
  subst i.
  unfold StonePrefixDone.
  exact PreH9.
Qed.

Lemma proof_of_mergingStones_entail_wit_5_split_goal_2 : mergingStones_entail_wit_5_split_goal_2.
Proof.
  intros n_pre dp_init stones_l prefix_l_2 i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  unfold StonePrefixProgress in PreH9.
  destruct PreH9 as [_ [Hprefix_len _]].
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_5 : mergingStones_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_mergingStones_entail_wit_6_split_goal_1 : mergingStones_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold StoneZeroRows.
  split; [exact PreH7 |].
  split; [lia |].
  intros r c Hr Hc.
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_6 : mergingStones_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mergingStones_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_mergingStones_entail_wit_7_split_goal_1 : mergingStones_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold StoneZeroRows in PreH10.
  destruct PreH10 as [Hshape [Hrow_bounds Hzero_rows]].
  unfold StoneZeroProgress.
  split; [exact Hshape |].
  split; [lia |].
  split; [lia |].
  split; [exact Hzero_rows |].
  intros c Hc.
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_7 : mergingStones_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mergingStones_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_mergingStones_entail_wit_8 : mergingStones_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia).
  Exists
    (replace_Znth row
      (replace_Znth col 0 (Znth row dp_l_2 __default__List_Z))
      dp_l_2)
    prefix_l_2.
  repeat (split_pure_spatial || split_pures).
  all: try solve [dump_pre_spatial; lia].
  all: try solve [dump_pre_spatial; assumption].
  all: try solve [
    dump_pre_spatial;
    eapply StoneZeroProgress_store__zero_table;
    eauto
  ].
  pose proof (IntArray.missing_i_merge_to_full
    (dp_pre + row * n_pre * sizeof (INT)) col n_pre 0
    (Znth row dp_l_2 __default__List_Z)) as Hrow_merge.
  simpl in Hrow_merge.
  assert (Haddr :
    dp_pre + row * n_pre * sizeof (INT) + col * sizeof (INT) =
    dp_pre + (row * n_pre + col) * sizeof (INT)) by lia.
  rewrite <- Haddr.
  sep_apply Hrow_merge; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    dp_pre row n_pre n_pre dp_l_2
    (replace_Znth col 0 (Znth row dp_l_2 __default__List_Z)))
    as Htable_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr dp_pre n_pre row) n_pre
      (replace_Znth col 0 (Znth row dp_l_2 __default__List_Z)))
    with
    (IntArray.full
      (dp_pre + row * n_pre * 4) n_pre
      (replace_Znth col 0 (Znth row dp_l_2 __default__List_Z)))
    in Htable_merge.
  sep_apply Htable_merge; try lia.
  cancel.
Qed.

Lemma proof_of_mergingStones_entail_wit_9_split_goal_1 : mergingStones_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold StoneZeroProgress in PreH12.
  destruct PreH12 as
    [Hshape [Hrow_bounds [Hcol_bounds [Hzero_rows Hzero_current]]]].
  assert (Hcol : col = n_pre) by lia.
  subst col.
  unfold StoneZeroRows.
  split; [exact Hshape |].
  split; [lia |].
  intros r c Hr Hc.
  destruct (Z_lt_ge_dec r row) as [Hbefore | Hcurrent].
  - apply Hzero_rows; lia.
  - assert (r = row) by lia.
    subst r.
    apply Hzero_current; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_9 : mergingStones_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mergingStones_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_mergingStones_entail_wit_11_split_goal_1 : mergingStones_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hrow : row = n_pre) by lia.
  subst row.
  apply StoneLenDone_two_of_zero__zero_table; assumption.
Qed.

Lemma proof_of_mergingStones_entail_wit_11_split_goal_2 : mergingStones_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hrow : row = n_pre) by lia.
  subst row.
  exact PreH10.
Qed.

Lemma proof_of_mergingStones_entail_wit_11 : mergingStones_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_11_split_goal_2.
Qed.

Lemma proof_of_mergingStones_entail_wit_13_split_goal_1 : mergingStones_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply StoneLenDone_to_initial_left_progress__table_progress.
  - exact PreH10.
  - lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_13 : mergingStones_entail_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mergingStones_entail_wit_13_split_goal_1.
Qed.

Lemma proof_of_mergingStones_entail_wit_14_split_goal_1 : mergingStones_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply StoneSplitProgress_initial__prefix_math.
  - exact PreH12.
  - lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_14_split_goal_2 : mergingStones_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StonePrefixDone_interval_bounds__prefix_math
       stones_l prefix_l n_pre left (left + len)
       PreH10 PreH11 ltac:(lia) ltac:(lia)) as Hbounds.
  replace (((left + len) - 1) + 1) with (left + len) by lia.
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_14_split_goal_3 : mergingStones_entail_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StonePrefixDone_interval_bounds__prefix_math
       stones_l prefix_l n_pre left (left + len)
       PreH10 PreH11 ltac:(lia) ltac:(lia)) as Hbounds.
  replace (((left + len) - 1) + 1) with (left + len) by lia.
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_14_split_goal_4 : mergingStones_entail_wit_14_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StonePrefixDone_interval_sum__prefix_math
       stones_l prefix_l n_pre left (left + len)
       PreH11 ltac:(lia) ltac:(lia)) as Hsum.
  replace (((left + len) - 1) + 1) with (left + len) by lia.
  exact Hsum.
Qed.

Lemma proof_of_mergingStones_entail_wit_14 : mergingStones_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_14_split_goal_2.
  - Goal_apply proof_of_mergingStones_entail_wit_14_split_goal_3.
  - Goal_apply proof_of_mergingStones_entail_wit_14_split_goal_4.
Qed.

Lemma proof_of_mergingStones_entail_wit_16_split_goal_1 : mergingStones_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StoneSplitProgress_child_bounds__interval_min_core
       stones_l dp_l_2 n_pre len left split right best __default__List_Z
       PreH20 PreH3 PreH22 PreH8 ltac:(lia) PreH10) as Hbounds.
  destruct Hbounds as [_ [_ Hright_bound]].
  rewrite <- PreH8.
  exact Hright_bound.
Qed.

Lemma proof_of_mergingStones_entail_wit_16_split_goal_2 : mergingStones_entail_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StoneSplitProgress_child_bounds__interval_min_core
       stones_l dp_l_2 n_pre len left split right best __default__List_Z
       PreH20 PreH3 PreH22 PreH8 ltac:(lia) PreH10) as Hbounds.
  destruct Hbounds as [_ [Hright_nonneg _]].
  rewrite <- PreH8.
  exact Hright_nonneg.
Qed.

Lemma proof_of_mergingStones_entail_wit_16_split_goal_3 : mergingStones_entail_wit_16_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StoneSplitProgress_child_bounds__interval_min_core
       stones_l dp_l_2 n_pre len left split right best __default__List_Z
       PreH20 PreH3 PreH22 PreH8 ltac:(lia) PreH10) as Hbounds.
  destruct Hbounds as [[_ Hleft_bound] _].
  exact Hleft_bound.
Qed.

Lemma proof_of_mergingStones_entail_wit_16_split_goal_4 : mergingStones_entail_wit_16_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StoneSplitProgress_child_bounds__interval_min_core
       stones_l dp_l_2 n_pre len left split right best __default__List_Z
       PreH20 PreH3 PreH22 PreH8 ltac:(lia) PreH10) as Hbounds.
  destruct Hbounds as [[Hleft_nonneg _] _].
  exact Hleft_nonneg.
Qed.

Lemma proof_of_mergingStones_entail_wit_16 : mergingStones_entail_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_16_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_16_split_goal_2.
  - Goal_apply proof_of_mergingStones_entail_wit_16_split_goal_3.
  - Goal_apply proof_of_mergingStones_entail_wit_16_split_goal_4.
Qed.

Lemma proof_of_mergingStones_entail_wit_17 : mergingStones_entail_wit_17.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof
    (StoneSplitProgress_table_shape__interval_min_core
       stones_l dp_l n_pre len left split best PreH20) as Hshape.
  destruct Hshape as [Htable_len Hrow_len].
  Exists prefix_l_2 dp_l.
  split_pure_spatial.
  - replace (dp_pre + (left * n_pre + split) * sizeof (INT)) with
      (dp_pre + left * n_pre * sizeof (INT) + split * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_pre + left * n_pre * sizeof (INT)) split n_pre
         (Znth split (Znth left dp_l __default__List_Z) 0)
         (Znth left dp_l __default__List_Z)).
    + dump_pre_spatial.
      lia.
    + rewrite replace_Znth_Znth by
        (pose proof (Hrow_len left ltac:(lia)); lia).
      change (IntArray.full
        (dp_pre + left * n_pre * sizeof (INT)) n_pre
        (Znth left dp_l __default__List_Z)) with
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_pre n_pre left) n_pre
          (Znth left dp_l __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_pre left n_pre n_pre dp_l
           (Znth left dp_l __default__List_Z)).
      * dump_pre_spatial.
        lia.
      * rewrite replace_Znth_Znth by lia.
        cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_18 : mergingStones_entail_wit_18.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof
    (StoneSplitProgress_table_shape__interval_min_core
       stones_l dp_l n_pre len left split best PreH21) as Hshape.
  destruct Hshape as [Htable_len Hrow_len].
  pose proof
    (StoneSplitProgress_candidate_facts__interval_min_core
       stones_l dp_l n_pre len left split right best interval_sum
       __default__List_Z PreH19 PreH2 PreH21 PreH7 ltac:(lia) PreH10
       PreH12) as Hcandidate.
  cbn in Hcandidate.
  destruct Hcandidate as [Hcandidate_bounds Hcandidate_spec].
  Exists prefix_l_2 dp_l.
  split_pure_spatial.
  - replace (dp_pre + ((split + 1) * n_pre + right) * sizeof (INT)) with
      (dp_pre + (split + 1) * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_pre + (split + 1) * n_pre * sizeof (INT)) right n_pre
         (Znth right (Znth (split + 1) dp_l __default__List_Z) 0)
         (Znth (split + 1) dp_l __default__List_Z)).
    + dump_pre_spatial.
      lia.
    + rewrite replace_Znth_Znth by
        (pose proof (Hrow_len (split + 1) ltac:(lia)); lia).
      change (IntArray.full
        (dp_pre + (split + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (split + 1) dp_l __default__List_Z)) with
        (IntArray2.ElemArray.full
          (IntArray2.row_addr dp_pre n_pre (split + 1)) n_pre
          (Znth (split + 1) dp_l __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           dp_pre (split + 1) n_pre n_pre dp_l
           (Znth (split + 1) dp_l __default__List_Z)).
      * dump_pre_spatial.
        lia.
      * rewrite replace_Znth_Znth by lia.
        cancel.
  - split_pures; dump_pre_spatial;
      try solve [auto | lia | rewrite PreH11; exact Hcandidate_spec].
Qed.

Lemma proof_of_mergingStones_entail_wit_19_1_split_goal_1 : mergingStones_entail_wit_19_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH15.
  eapply StoneSplitProgress_replace_best__split_loop_step;
    [ exact PreH8 | exact PreH10 | exact PreH16 | lia | exact PreH1
    | exact PreH18 | exact PreH21 ].
Qed.

Lemma proof_of_mergingStones_entail_wit_19_1 : mergingStones_entail_wit_19_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mergingStones_entail_wit_19_1_split_goal_1.
Qed.

Lemma proof_of_mergingStones_entail_wit_19_2_split_goal_1 : mergingStones_entail_wit_19_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply StoneSplitProgress_keep_best__split_loop_step;
    [ exact PreH8 | exact PreH10 | exact PreH17 | lia
    | exact PreH18 | exact PreH21 ].
Qed.

Lemma proof_of_mergingStones_entail_wit_19_2_split_goal_2 : mergingStones_entail_wit_19_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold StoneSplitProgress in PreH21.
  cbn in PreH21.
  destruct PreH21 as [_ [_ [[Hbest_nonneg _] _]]].
  exact Hbest_nonneg.
Qed.

Lemma proof_of_mergingStones_entail_wit_19_2 : mergingStones_entail_wit_19_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_19_2_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_19_2_split_goal_2.
Qed.

Lemma proof_of_mergingStones_entail_wit_20_split_goal_1 : mergingStones_entail_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold StonePrefixDone, StonePrefixProgress in PreH21.
  destruct PreH21 as [_ [Hprefix_length _]].
  exact Hprefix_length.
Qed.

Lemma proof_of_mergingStones_entail_wit_20_split_goal_2 : mergingStones_entail_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold StoneMassesBounded in PreH20.
  destruct PreH20 as [Hstones_length _].
  exact Hstones_length.
Qed.

Lemma proof_of_mergingStones_entail_wit_20_split_goal_3 : mergingStones_entail_wit_20_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH13.
  pose proof
    (stone_interval_sum_bounds__arithmetic_safety
       stones_l n_pre left right PreH2 PreH5 ltac:(lia) PreH10 PreH20)
    as Hbounds.
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_20_split_goal_4 : mergingStones_entail_wit_20_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH13.
  pose proof
    (stone_interval_sum_bounds__arithmetic_safety
       stones_l n_pre left right PreH2 PreH5 ltac:(lia) PreH10 PreH20)
    as Hbounds.
  lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_20 : mergingStones_entail_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_20_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_20_split_goal_2.
  - Goal_apply proof_of_mergingStones_entail_wit_20_split_goal_3.
  - Goal_apply proof_of_mergingStones_entail_wit_20_split_goal_4.
Qed.

Lemma proof_of_mergingStones_entail_wit_21_split_goal_1 : mergingStones_entail_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (split = right) by lia.
  subst split.
  rewrite <- PreH8.
  eapply StoneSplitProgress_complete__interval_min_core;
    [ exact PreH8 | exact PreH9 | exact PreH10 | exact PreH22 ].
Qed.

Lemma proof_of_mergingStones_entail_wit_21_split_goal_2 : mergingStones_entail_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (split = right) by lia.
  subst split.
  rewrite <- PreH8.
  exact PreH22.
Qed.

Lemma proof_of_mergingStones_entail_wit_21_split_goal_3 : mergingStones_entail_wit_21_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (split = right) by lia.
  subst split.
  assert (Hminimum : StoneIntervalMin stones_l left right best).
  {
    eapply StoneSplitProgress_complete__interval_min_core;
      [ exact PreH8 | exact PreH9 | exact PreH10 | exact PreH22 ].
  }
  pose proof
    (StoneIntervalMin_bounds__interval_min_core
       stones_l n_pre left right best PreH20 PreH3
       ltac:(lia) PreH10 Hminimum) as Hbounds.
  destruct Hbounds as [_ Hbest_bound].
  exact Hbest_bound.
Qed.

Lemma proof_of_mergingStones_entail_wit_21 : mergingStones_entail_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_21_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_21_split_goal_2.
  - Goal_apply proof_of_mergingStones_entail_wit_21_split_goal_3.
Qed.

Lemma proof_of_mergingStones_entail_wit_22 : mergingStones_entail_wit_22.
Proof.
  LLM_pre_process ltac:(lia).
  set (dp_new :=
    replace_Znth left
      (replace_Znth right best (Znth left dp_l __default__List_Z))
      dp_l).
  pose proof
    (StoneSplitProgress_table_shape__interval_min_core
       stones_l dp_l n_pre len left right best PreH17) as Hshape.
  unfold StoneTableShape in Hshape.
  destruct Hshape as [Htable_len Hrow_len].
  assert (Hleft_index : 0 <= left < Zlength dp_l) by
    (rewrite Htable_len; lia).
  pose proof (Hrow_len left ltac:(lia)) as Hrow_length.
  assert (Hright_index :
    0 <= right < Zlength (Znth left dp_l (@nil Z))).
  {
    split; [lia |].
    rewrite Hrow_length.
    exact PreH9.
  }
  assert (Hupdated :
    StoneUpdatedCell stones_l dp_l dp_new left right best).
  {
    unfold StoneUpdatedCell, dp_new.
    split; [exact Hleft_index |].
    split; [exact Hright_index |].
    split.
    - rewrite (Znth_indep dp_l left __default__List_Z (@nil Z) Hleft_index).
      reflexivity.
    - exact PreH18.
  }
  pose proof PreH17 as Hleft_progress.
  unfold StoneSplitProgress in Hleft_progress.
  cbn in Hleft_progress.
  destruct Hleft_progress as [Hleft_progress _].
  pose proof
    (StoneUpdatedCell_to_next_left_progress__table_progress
       stones_l dp_l dp_new n_pre len left right best
       Hleft_progress PreH7 PreH6 Hupdated) as Hnext.
  Exists dp_l dp_new prefix_l_2.
  split_pure_spatial.
  - replace (dp_pre + (left * n_pre + right) * sizeof (INT))
      with (dp_pre + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         (dp_pre + left * n_pre * sizeof (INT)) right n_pre best
         (Znth left dp_l __default__List_Z)).
    + dump_pre_spatial. lia.
    + pose proof
        (IntArray2.missing_i_merge_to_full
           dp_pre left n_pre n_pre dp_l
           (replace_Znth right best (Znth left dp_l __default__List_Z))
           ltac:(lia)) as Hmerge.
      change
        (IntArray2.ElemArray.full
           (IntArray2.row_addr dp_pre n_pre left) n_pre
           (replace_Znth right best (Znth left dp_l __default__List_Z)))
        with
        (IntArray.full (dp_pre + left * n_pre * sizeof (INT)) n_pre
           (replace_Znth right best (Znth left dp_l __default__List_Z)))
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      unfold dp_new.
      cancel.
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mergingStones_entail_wit_23_split_goal_1 : mergingStones_entail_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold StonePrefixDone, StonePrefixProgress in PreH14.
  tauto.
Qed.

Lemma proof_of_mergingStones_entail_wit_23_split_goal_2 : mergingStones_entail_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold StoneMassesBounded in PreH13.
  tauto.
Qed.

Lemma proof_of_mergingStones_entail_wit_23 : mergingStones_entail_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_23_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_23_split_goal_2.
Qed.

Lemma proof_of_mergingStones_entail_wit_24_split_goal_1 : mergingStones_entail_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply StoneLeftProgress_to_next_len_done__table_progress; eauto.
Qed.

Lemma proof_of_mergingStones_entail_wit_24 : mergingStones_entail_wit_24.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mergingStones_entail_wit_24_split_goal_1.
Qed.

Lemma proof_of_mergingStones_entail_wit_25_split_goal_1 : mergingStones_entail_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold StonePrefixDone, StonePrefixProgress in PreH6.
  destruct PreH6 as [_ [Hprefix _]].
  exact Hprefix.
Qed.

Lemma proof_of_mergingStones_entail_wit_25_split_goal_2 : mergingStones_entail_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  exact (proj1 PreH5).
Qed.

Lemma proof_of_mergingStones_entail_wit_25 : mergingStones_entail_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_25_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_25_split_goal_2.
Qed.

Lemma proof_of_mergingStones_entail_wit_26_split_goal_1 : mergingStones_entail_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StoneLenDone_final_facts__interval_min_core
       stones_l dp_l_2 n_pre len __default__List_Z
       PreH2 PreH3 PreH8 PreH1 PreH5 PreH10)
    as Hfinal.
  cbn in Hfinal.
  tauto.
Qed.

Lemma proof_of_mergingStones_entail_wit_26_split_goal_2 : mergingStones_entail_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StoneLenDone_final_facts__interval_min_core
       stones_l dp_l_2 n_pre len __default__List_Z
       PreH2 PreH3 PreH8 PreH1 PreH5 PreH10)
    as Hfinal.
  cbn in Hfinal.
  tauto.
Qed.

Lemma proof_of_mergingStones_entail_wit_26_split_goal_3 : mergingStones_entail_wit_26_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (StoneLenDone_final_facts__interval_min_core
       stones_l dp_l_2 n_pre len __default__List_Z
       PreH2 PreH3 PreH8 PreH1 PreH5 PreH10)
    as Hfinal.
  cbn in Hfinal.
  tauto.
Qed.

Lemma proof_of_mergingStones_entail_wit_26_split_goal_4 : mergingStones_entail_wit_26_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (len = n_pre + 1) by lia.
  subst len.
  exact PreH10.
Qed.

Lemma proof_of_mergingStones_entail_wit_26 : mergingStones_entail_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergingStones_entail_wit_26_split_goal_1.
  - Goal_apply proof_of_mergingStones_entail_wit_26_split_goal_2.
  - Goal_apply proof_of_mergingStones_entail_wit_26_split_goal_3.
  - Goal_apply proof_of_mergingStones_entail_wit_26_split_goal_4.
Qed.

Lemma proof_of_mergingStones_return_wit_1 : mergingStones_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  Exists dp_l_2 prefix_l_2.
  repeat (split_pure_spatial || split_pures);
    try solve [dump_pre_spatial; auto].
  pose proof PreH5 as Hdone.
  unfold StoneLenDone in Hdone.
  destruct Hdone as [Hstones_len [Hshape [Hlen Hinterval]]].
  destruct Hshape as [Htable_len Hrow_length].
  assert (Hrow0 :
    Zlength (Znth 0 dp_l_2 __default__List_Z) = n_pre).
  {
    rewrite (Znth_indep dp_l_2 0 __default__List_Z (@nil Z)) by lia.
    apply Hrow_length; lia.
  }
  pose proof
    (IntArray.missing_i_merge_to_full
       (dp_pre + 0 * n_pre * sizeof (INT))
       (n_pre - 1) n_pre
       (Znth (n_pre - 1) (Znth 0 dp_l_2 __default__List_Z) 0)
       (Znth 0 dp_l_2 __default__List_Z)) as Hcell.
  replace
    (dp_pre + (0 * n_pre + (n_pre - 1)) * sizeof (INT))
    with
    ((dp_pre + 0 * n_pre * sizeof (INT)) +
       (n_pre - 1) * sizeof (INT)) by lia.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  pose proof
    (IntArray2.missing_i_merge_to_full
       dp_pre 0 n_pre n_pre dp_l_2
       (Znth 0 dp_l_2 __default__List_Z)) as Htable.
  change
    (IntArray2.ElemArray.full
       (IntArray2.row_addr dp_pre n_pre 0) n_pre
       (Znth 0 dp_l_2 __default__List_Z))
    with
    (IntArray.full (dp_pre + 0 * n_pre * sizeof (INT)) n_pre
       (Znth 0 dp_l_2 __default__List_Z)) in Htable.
  sep_apply Htable; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
