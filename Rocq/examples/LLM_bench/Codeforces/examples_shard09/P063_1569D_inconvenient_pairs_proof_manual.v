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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P063_1569D_inconvenient_pairs_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P063_1569D_inconvenient_pairs_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P063_1569D_inconvenient_pairs_lib.
Require Import AUXLib.MonotonicList.
Local Open Scope sac.

Lemma proof_of_strip_safety_wit_4_split_goal_1 : strip_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (hi - lo + 1) / 2) by (apply Z.div_pos; lia).
  assert ((hi - lo + 1) / 2 <= hi - lo + 1) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_strip_safety_wit_4_split_goal_2 : strip_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (hi - lo + 1) / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_strip_safety_wit_4 : strip_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strip_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_strip_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_strip_safety_wit_10_split_goal_1 : strip_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (hi - lo + 1) / 2) by (apply Z.div_pos; lia).
  assert ((hi - lo + 1) / 2 <= hi - lo + 1) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_strip_safety_wit_10_split_goal_2 : strip_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (hi - lo + 1) / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_strip_safety_wit_10 : strip_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strip_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_strip_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_strip_safety_wit_16_split_goal_1 : strip_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (hi - lo + 1) / 2) by (apply Z.div_pos; lia).
  assert ((hi - lo + 1) / 2 <= hi - lo + 1) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_strip_safety_wit_16_split_goal_2 : strip_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= (hi - lo + 1) / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_strip_safety_wit_16 : strip_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_strip_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_strip_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_strip_entail_wit_2_1 : strip_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hhalf_nonneg : 0 <= (hi - lo + 1) / 2)
    by (apply Z.div_pos; lia).
  assert (Hhalf_le : (hi - lo + 1) / 2 <= hi - lo)
    by (apply Z.div_le_upper_bound; lia).
  Left.
  Left.
  repeat apply _derivable1_andp_intros.
  all: try (dump_pre_spatial; (assumption || lia || nia || int_auto)).
  cancel.
Qed.

Lemma proof_of_strip_entail_wit_2_2 : strip_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hhalf_nonneg : 0 <= (hi_2 - lo_2 + 1) / 2)
    by (apply Z.div_pos; lia).
  assert (Hhalf_le : (hi_2 - lo_2 + 1) / 2 <= hi_2 - lo_2)
    by (apply Z.div_le_upper_bound; lia).
  Left.
  Right.
  repeat apply _derivable1_andp_intros.
  all: try (dump_pre_spatial; (assumption || lia || nia || int_auto)).
  cancel.
Qed.

Lemma proof_of_strip_entail_wit_2_3 : strip_entail_wit_2_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hhalf_nonneg : 0 <= (hi_3 - lo_3 + 1) / 2)
    by (apply Z.div_pos; lia).
  assert (Hhalf_le : (hi_3 - lo_3 + 1) / 2 <= hi_3 - lo_3)
    by (apply Z.div_le_upper_bound; lia).
  Right.
  repeat apply _derivable1_andp_intros.
  all: try (dump_pre_spatial; (assumption || lia || nia || int_auto)).
  cancel.
Qed.

Lemma proof_of_strip_entail_wit_3_1 : strip_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  assert (Hhalf_nonneg : 0 <= (hi - lo + 1) / 2)
    by (apply Z.div_pos; lia).
  assert (Hhalf_le : (hi - lo + 1) / 2 <= hi - lo)
    by (apply Z.div_le_upper_bound; lia).
  Left.
  Left.
  repeat apply _derivable1_andp_intros.
  all: try (dump_pre_spatial; (assumption || lia || nia || int_auto)).
  cancel.
Qed.

Lemma proof_of_strip_entail_wit_3_3 : strip_entail_wit_3_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  assert (Hhalf_nonneg : 0 <= (hi - lo + 1) / 2)
    by (apply Z.div_pos; lia).
  assert (Hhalf_le : (hi - lo + 1) / 2 <= hi - lo)
    by (apply Z.div_le_upper_bound; lia).
  Right.
  repeat apply _derivable1_andp_intros.
  all: try (dump_pre_spatial; (assumption || lia || nia || int_auto)).
  cancel.
Qed.

Lemma proof_of_strip_entail_wit_3_4 : strip_entail_wit_3_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  assert (Hhalf_pos : 1 <= (hi - lo + 1) / 2)
    by (apply Z.div_le_lower_bound; lia).
  assert (Hhalf_le : (hi - lo + 1) / 2 <= hi - lo)
    by (apply Z.div_le_upper_bound; lia).
  Right.
  replace ((lo + (hi - lo + 1) / 2 - 1) + 1)
    with (lo + (hi - lo + 1) / 2) by lia.
  repeat apply _derivable1_andp_intros.
  all: try (dump_pre_spatial; (assumption || lia || nia || int_auto)).
  cancel.
Qed.

Lemma proof_of_strip_entail_wit_3_5 : strip_entail_wit_3_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  assert (Hhalf_pos : 1 <= (hi - lo + 1) / 2)
    by (apply Z.div_le_lower_bound; lia).
  assert (Hhalf_le : (hi - lo + 1) / 2 <= hi - lo)
    by (apply Z.div_le_upper_bound; lia).
  Right.
  replace ((lo + (hi - lo + 1) / 2 - 1) + 1)
    with (lo + (hi - lo + 1) / 2) by lia.
  repeat apply _derivable1_andp_intros.
  all: try (dump_pre_spatial; (assumption || lia || nia || int_auto)).
  cancel.
Qed.

Lemma proof_of_strip_entail_wit_3_6 : strip_entail_wit_3_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg in * by lia.
  assert (Hhalf_pos : 1 <= (hi - lo + 1) / 2)
    by (apply Z.div_le_lower_bound; lia).
  assert (Hhalf_le : (hi - lo + 1) / 2 <= hi - lo)
    by (apply Z.div_le_upper_bound; lia).
  Right.
  replace ((lo + (hi - lo + 1) / 2 - 1) + 1)
    with (lo + (hi - lo + 1) / 2) by lia.
  repeat apply _derivable1_andp_intros.
  all: try (dump_pre_spatial; (assumption || lia || nia || int_auto)).
  cancel.
Qed.

Lemma proof_of_strip_return_wit_1_split_goal_1 : strip_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StripIndex.
  left.
  split.
  - lia.
  - rewrite <- PreH1.
    unfold Znth.
    apply nth_In.
    assert (Hlo : 0 <= lo < Zlength streets) by
      (rewrite PreH5; lia).
    rewrite Zlength_correct in Hlo.
    lia.
Qed.

Lemma proof_of_strip_return_wit_1 : strip_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_strip_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_strip_return_wit_2_split_goal_1 : strip_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StripIndex.
  left.
  split.
  - lia.
  - rewrite <- PreH1.
    unfold Znth.
    apply nth_In.
    assert (Hlo : 0 <= lo < Zlength streets) by
      (rewrite PreH5; lia).
    rewrite Zlength_correct in Hlo.
    lia.
Qed.

Lemma proof_of_strip_return_wit_2 : strip_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_strip_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_strip_return_wit_3_split_goal_1 : strip_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StripIndex.
  left.
  split.
  - lia.
  - rewrite PreH15.
    unfold Znth.
    apply nth_In.
    assert (Hhi : 0 <= hi < Zlength streets) by
      (rewrite PreH5; lia).
    rewrite Zlength_correct in Hhi.
    lia.
Qed.

Lemma proof_of_strip_return_wit_3 : strip_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_strip_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_strip_return_wit_4_split_goal_1 : strip_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold StripIndex.
  right.
  assert (Hlo : lo < n_pre - 1).
  {
    destruct (Z.eq_dec lo (n_pre - 1)) as [Heq | Hneq].
    - rewrite Heq, PreH8 in PreH1, PreH14.
      lia.
    - lia.
  }
  split.
  - rewrite PreH5.
    lia.
  - split.
    + lia.
    + replace (hi + 1) with (lo + 1) in PreH15 by lia.
      exact PreH15.
Qed.

Lemma proof_of_strip_return_wit_4 : strip_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_strip_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_strip_return_wit_5_split_goal_1 : strip_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  assert (Hlo : lo = n_pre - 1) by lia.
  rewrite Hlo, PreH8 in PreH1, PreH14.
  lia.
Qed.

Lemma proof_of_strip_return_wit_5 : strip_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_strip_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_strip_return_wit_6_split_goal_1 : strip_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  apply PreH1.
  rewrite PreH15.
  f_equal.
  lia.
Qed.

Lemma proof_of_strip_return_wit_6 : strip_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_strip_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_item_less_return_wit_1 : item_less_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; unfold ItemLe4; lia.
Qed.

Lemma proof_of_item_less_return_wit_2_split_goal_1 : item_less_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold ItemLe4 in *; lia).
Qed.

Lemma proof_of_item_less_return_wit_2 : item_less_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_item_less_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_item_less_return_wit_3_split_goal_1 : item_less_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold ItemLe4 in *; lia).
Qed.

Lemma proof_of_item_less_return_wit_3 : item_less_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_item_less_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_item_less_return_wit_4_split_goal_1 : item_less_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold ItemLe4 in *; lia).
Qed.

Lemma proof_of_item_less_return_wit_4 : item_less_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_item_less_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_sift_items_entail_wit_1_split_goal_1 : sift_items_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SiftChildrenBelowParentItems.
  left. reflexivity.
Qed.

Lemma proof_of_sift_items_entail_wit_1_split_goal_2 : sift_items_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ParallelPermutation.
  apply Permutation_refl.
Qed.

Lemma proof_of_sift_items_entail_wit_1 : sift_items_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_items_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_sift_items_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_sift_items_entail_wit_4_1_split_goal_1 : sift_items_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SelectedLargerChildItems.
  split.
  - right. lia.
  - split.
    + lia.
    + split.
      * intros _.
        rewrite (Znth_combine__sift_swap groups_now_2 keys_now_2
          (2 * root + 1) 0 0) by lia.
        rewrite (Znth_combine__sift_swap groups_now_2 keys_now_2
          (2 * root + 1 + 1) 0 0) by lia.
        unfold ItemLe4 in PreH3.
        unfold ItemLe. simpl. exact PreH3.
      * intros _.
        replace (2 * root + 2) with (2 * root + 1 + 1) by lia.
        unfold ItemLe. simpl. right. split; [reflexivity | lia].
Qed.

Lemma proof_of_sift_items_entail_wit_4_1 : sift_items_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sift_items_entail_wit_4_1_split_goal_1.
Qed.

Lemma proof_of_sift_items_entail_wit_4_2_split_goal_1 : sift_items_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SelectedLargerChildItems.
  split.
  - right. lia.
  - split.
    + lia.
    + split.
      * intros _.
        rewrite (Znth_combine__sift_swap groups_now_2 keys_now_2
          (2 * root + 1) 0 0) by lia.
        rewrite (Znth_combine__sift_swap groups_now_2 keys_now_2
          (2 * root + 1 + 1) 0 0) by lia.
        unfold ItemLe4 in PreH3.
        unfold ItemLe. simpl. exact PreH3.
      * intros _.
        replace (2 * root + 2) with (2 * root + 1 + 1) by lia.
        unfold ItemLe. simpl. right. split; [reflexivity | lia].
Qed.

Lemma proof_of_sift_items_entail_wit_4_2 : sift_items_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sift_items_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_sift_items_entail_wit_4_3_split_goal_1 : sift_items_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SelectedLargerChildItems.
  split.
  - left. lia.
  - split.
    + lia.
    + split.
      * intros _. unfold ItemLe. simpl. right. split; [reflexivity | lia].
      * intros Hright. lia.
Qed.

Lemma proof_of_sift_items_entail_wit_4_3 : sift_items_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sift_items_entail_wit_4_3_split_goal_1.
Qed.

Lemma proof_of_sift_items_entail_wit_4_4_split_goal_1 : sift_items_entail_wit_4_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SelectedLargerChildItems.
  split.
  - left. lia.
  - split.
    + lia.
    + split.
      * intros _. unfold ItemLe. simpl. right. split; [reflexivity | lia].
      * intros _.
        rewrite (Znth_combine__sift_swap groups_now_2 keys_now_2
          (2 * root + 2) 0 0) by lia.
        rewrite (Znth_combine__sift_swap groups_now_2 keys_now_2
          (2 * root + 1) 0 0) by lia.
        replace (2 * root + 1 + 1) with (2 * root + 2) in PreH3 by lia.
        unfold ItemLe4 in PreH3.
        unfold ItemLe. simpl. exact PreH3.
Qed.

Lemma proof_of_sift_items_entail_wit_4_4 : sift_items_entail_wit_4_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sift_items_entail_wit_4_4_split_goal_1.
Qed.

Lemma proof_of_sift_items_entail_wit_5_1_split_goal_1 : sift_items_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  etransitivity.
  - apply sublist_two_swap_below_cut__sift_swap; lia.
  - exact PreH22.
Qed.

Lemma proof_of_sift_items_entail_wit_5_1_split_goal_2 : sift_items_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  etransitivity.
  - apply sublist_two_swap_below_cut__sift_swap; lia.
  - exact PreH21.
Qed.

Lemma proof_of_sift_items_entail_wit_5_1_split_goal_3 : sift_items_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply extraction_frame_two_swap__sift_swap.
  - lia.
  - destruct PreH16 as [[-> | ->] _]; lia.
  - lia.
  - lia.
  - exact PreH20.
Qed.

Lemma proof_of_sift_items_entail_wit_5_1_split_goal_4 : sift_items_entail_wit_5_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SiftChildrenBelowParentItems.
  right. intros descendant Hdesc Hdesc_hi.
  rewrite combine_two_swap__sift_swap by lia.
  unfold HeapOrderedExceptAtFromItems in PreH18.
  destruct PreH16 as [Hshape [Hchild_hi [Hleft Hright]]].
  eapply (selected_swap_descendant_edge_items__sift_swap
    (combine groups_now_2 keys_now_2) root_pre root upper_pre child
    descendant); eauto; try lia.
  rewrite Zlength_combine_eq__sift_swap by lia. lia.
Qed.

Lemma proof_of_sift_items_entail_wit_5_1_split_goal_5 : sift_items_entail_wit_5_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold HeapOrderedExceptAtFromItems.
  rewrite combine_two_swap__sift_swap by lia.
  destruct PreH16 as [Hshape [Hchild_hi [Hleft Hright]]].
  assert (Hrise :
    ItemLe (Znth root (combine groups_now_2 keys_now_2) (0, 0))
           (Znth child (combine groups_now_2 keys_now_2) (0, 0))).
  {
    unfold ItemLe.
    rewrite !Znth_combine__sift_swap by lia. simpl.
    unfold ItemLe4 in PreH3. exact PreH3.
  }
  assert (Henter : 1 <= root -> root_pre <= (root - 1) / 2 ->
    ItemLe (Znth child (combine groups_now_2 keys_now_2) (0, 0))
           (Znth ((root - 1) / 2)
             (combine groups_now_2 keys_now_2) (0, 0))).
  {
    intros Hroot_pos Hparent_lo.
    unfold SiftChildrenBelowParentItems in PreH19.
    destruct PreH19 as [Heq | Hbelow].
    - subst root.
      pose proof (heap_parent_bounds_items__sift_swap root_pre ltac:(lia)).
      lia.
    - apply Hbelow; [exact Hshape | exact Hchild_hi].
  }
  unfold HeapOrderedExceptAtFromItems in PreH18.
  eapply (heap_except_after_selected_swap_items__sift_swap
    (combine groups_now_2 keys_now_2) root_pre root upper_pre child);
    eauto; try lia.
  rewrite Zlength_combine_eq__sift_swap by lia. lia.
Qed.

Lemma proof_of_sift_items_entail_wit_5_1_split_goal_6 : sift_items_entail_wit_5_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply parallel_permutation_two_swap__sift_swap; try assumption; try lia.
  destruct PreH16 as [[-> | ->] _]; lia.
Qed.

Lemma proof_of_sift_items_entail_wit_5_1_split_goal_7 : sift_items_entail_wit_5_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH16 as [[-> | ->] _]; lia.
Qed.

Lemma proof_of_sift_items_entail_wit_5_1_split_goal_8 : sift_items_entail_wit_5_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite replace_Znth_two_swap_length__sift_swap. exact PreH10.
Qed.

Lemma proof_of_sift_items_entail_wit_5_1_split_goal_9 : sift_items_entail_wit_5_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite replace_Znth_two_swap_length__sift_swap. exact PreH9.
Qed.

Lemma proof_of_sift_items_entail_wit_5_1 : sift_items_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_items_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_sift_items_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_sift_items_entail_wit_5_1_split_goal_3.
  - Goal_apply proof_of_sift_items_entail_wit_5_1_split_goal_4.
  - Goal_apply proof_of_sift_items_entail_wit_5_1_split_goal_5.
  - Goal_apply proof_of_sift_items_entail_wit_5_1_split_goal_6.
  - Goal_apply proof_of_sift_items_entail_wit_5_1_split_goal_7.
  - Goal_apply proof_of_sift_items_entail_wit_5_1_split_goal_8.
  - Goal_apply proof_of_sift_items_entail_wit_5_1_split_goal_9.
Qed.

Lemma proof_of_sift_items_entail_wit_5_2_split_goal_1 : sift_items_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  etransitivity.
  - apply sublist_two_swap_below_cut__sift_swap; lia.
  - exact PreH22.
Qed.

Lemma proof_of_sift_items_entail_wit_5_2_split_goal_2 : sift_items_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  etransitivity.
  - apply sublist_two_swap_below_cut__sift_swap; lia.
  - exact PreH21.
Qed.

Lemma proof_of_sift_items_entail_wit_5_2_split_goal_3 : sift_items_entail_wit_5_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply extraction_frame_two_swap__sift_swap.
  - lia.
  - destruct PreH16 as [[-> | ->] _]; lia.
  - lia.
  - lia.
  - exact PreH20.
Qed.

Lemma proof_of_sift_items_entail_wit_5_2_split_goal_4 : sift_items_entail_wit_5_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SiftChildrenBelowParentItems.
  right. intros descendant Hdesc Hdesc_hi.
  rewrite combine_two_swap__sift_swap by lia.
  unfold HeapOrderedExceptAtFromItems in PreH18.
  destruct PreH16 as [Hshape [Hchild_hi [Hleft Hright]]].
  eapply (selected_swap_descendant_edge_items__sift_swap
    (combine groups_now_2 keys_now_2) root_pre root upper_pre child
    descendant); eauto; try lia.
  rewrite Zlength_combine_eq__sift_swap by lia. lia.
Qed.

Lemma proof_of_sift_items_entail_wit_5_2_split_goal_5 : sift_items_entail_wit_5_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold HeapOrderedExceptAtFromItems.
  rewrite combine_two_swap__sift_swap by lia.
  destruct PreH16 as [Hshape [Hchild_hi [Hleft Hright]]].
  assert (Hrise :
    ItemLe (Znth root (combine groups_now_2 keys_now_2) (0, 0))
           (Znth child (combine groups_now_2 keys_now_2) (0, 0))).
  {
    unfold ItemLe.
    rewrite !Znth_combine__sift_swap by lia. simpl.
    unfold ItemLe4 in PreH3. exact PreH3.
  }
  assert (Henter : 1 <= root -> root_pre <= (root - 1) / 2 ->
    ItemLe (Znth child (combine groups_now_2 keys_now_2) (0, 0))
           (Znth ((root - 1) / 2)
             (combine groups_now_2 keys_now_2) (0, 0))).
  {
    intros Hroot_pos Hparent_lo.
    unfold SiftChildrenBelowParentItems in PreH19.
    destruct PreH19 as [Heq | Hbelow].
    - subst root.
      pose proof (heap_parent_bounds_items__sift_swap root_pre ltac:(lia)).
      lia.
    - apply Hbelow; [exact Hshape | exact Hchild_hi].
  }
  unfold HeapOrderedExceptAtFromItems in PreH18.
  eapply (heap_except_after_selected_swap_items__sift_swap
    (combine groups_now_2 keys_now_2) root_pre root upper_pre child);
    eauto; try lia.
  rewrite Zlength_combine_eq__sift_swap by lia. lia.
Qed.

Lemma proof_of_sift_items_entail_wit_5_2_split_goal_6 : sift_items_entail_wit_5_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply parallel_permutation_two_swap__sift_swap; try assumption; try lia.
  destruct PreH16 as [[-> | ->] _]; lia.
Qed.

Lemma proof_of_sift_items_entail_wit_5_2_split_goal_7 : sift_items_entail_wit_5_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH16 as [[-> | ->] _]; lia.
Qed.

Lemma proof_of_sift_items_entail_wit_5_2_split_goal_8 : sift_items_entail_wit_5_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite replace_Znth_two_swap_length__sift_swap. exact PreH10.
Qed.

Lemma proof_of_sift_items_entail_wit_5_2_split_goal_9 : sift_items_entail_wit_5_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite replace_Znth_two_swap_length__sift_swap. exact PreH9.
Qed.

Lemma proof_of_sift_items_entail_wit_5_2 : sift_items_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_items_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_sift_items_entail_wit_5_2_split_goal_2.
  - Goal_apply proof_of_sift_items_entail_wit_5_2_split_goal_3.
  - Goal_apply proof_of_sift_items_entail_wit_5_2_split_goal_4.
  - Goal_apply proof_of_sift_items_entail_wit_5_2_split_goal_5.
  - Goal_apply proof_of_sift_items_entail_wit_5_2_split_goal_6.
  - Goal_apply proof_of_sift_items_entail_wit_5_2_split_goal_7.
  - Goal_apply proof_of_sift_items_entail_wit_5_2_split_goal_8.
  - Goal_apply proof_of_sift_items_entail_wit_5_2_split_goal_9.
Qed.

Lemma proof_of_sift_items_return_wit_1_split_goal_1 : sift_items_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (heap_parents_after_selected_stop_items__sift_exit
    groups_now keys_now root_pre upper_pre root child
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH15 PreH3 PreH17).
Qed.

Lemma proof_of_sift_items_return_wit_1 : sift_items_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sift_items_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sift_items_return_wit_2_split_goal_1 : sift_items_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (heap_parents_after_leaf_stop_items__sift_exit
    groups_now keys_now root_pre upper_pre root PreH1 PreH14).
Qed.

Lemma proof_of_sift_items_return_wit_2 : sift_items_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sift_items_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_sort_items_safety_wit_1_split_goal_1 : sort_items_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (cnt_pre / 2 <= cnt_pre) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_sort_items_safety_wit_1_split_goal_2 : sort_items_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (0 <= cnt_pre / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_sort_items_safety_wit_1 : sort_items_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_items_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_items_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_sort_items_entail_wit_1_split_goal_1 : sort_items_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold HeapParentsFromItems.
  intros child Hchild Hparent.
  rewrite zdiv_equiv in Hparent by lia.
  exfalso.
  pose proof (Z.div_mod cnt_pre 2 ltac:(lia)) as Hdiv_cnt.
  pose proof (Z.mod_pos_bound cnt_pre 2 ltac:(lia)) as Hmod_cnt.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hdiv_child.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hmod_child.
  lia.
Qed.

Lemma proof_of_sort_items_entail_wit_1_split_goal_2 : sort_items_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ParallelPermutation.
  apply Permutation_refl.
Qed.

Lemma proof_of_sort_items_entail_wit_1_split_goal_3 : sort_items_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite zdiv_equiv by lia.
  assert (0 <= cnt_pre / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_sort_items_entail_wit_1 : sort_items_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_items_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_items_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_sort_items_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_sort_items_entail_wit_2_split_goal_1 : sort_items_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (root - 1 + 1) with root by lia.
  exact PreH4.
Qed.

Lemma proof_of_sort_items_entail_wit_2_split_goal_2 : sort_items_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ParallelPermutation in *.
  eapply Permutation_trans; eauto.
Qed.

Lemma proof_of_sort_items_entail_wit_2 : sort_items_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_items_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_sort_items_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_sort_items_entail_wit_3_split_goal_1 : sort_items_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (root = -1) by lia. subst root.
  unfold HeapSortItemsState.
  repeat split.
  - lia.
  - lia.
  - exact PreH11.
  - replace 0 with (-1 + 1) by lia.
    exact PreH12.
  - rewrite !Zlength_sublist by lia. lia.
  - intros i j Hij.
    rewrite Zlength_sublist in Hij by lia. lia.
  - intros p q Hp Hq. lia.
Qed.

Lemma proof_of_sort_items_entail_wit_3 : sort_items_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_items_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_sort_items_entail_wit_4_split_goal_1 : sort_items_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ExtractionFrameItems.
  repeat rewrite replace_Znth_length_one__sift_swap.
  rewrite PreH7, PreH8.
  split.
  - eapply heap_extract_suffix_items__sort_extract_transition; eauto; lia.
  - intros p q Hp Hq.
    eapply heap_extract_cross_items__sort_extract_transition; eauto; lia.
Qed.

Lemma proof_of_sort_items_entail_wit_4_split_goal_2 : sort_items_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold HeapSortItemsState in PreH11.
  destruct PreH11 as [Hgl [Hkl [Hperm [Hheap Hrest]]]].
  eapply heap_extract_except_items__sort_extract_transition; eauto; lia.
Qed.

Lemma proof_of_sort_items_entail_wit_4_split_goal_3 : sort_items_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold HeapSortItemsState in PreH11.
  destruct PreH11 as [Hgl [Hkl [Hperm Hrest]]].
  apply parallel_permutation_two_swap__sift_swap.
  - exact Hperm.
  - lia.
  - lia.
  - lia.
Qed.

Lemma proof_of_sort_items_entail_wit_4_split_goal_4 : sort_items_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_length_one__sift_swap.
  exact PreH8.
Qed.

Lemma proof_of_sort_items_entail_wit_4_split_goal_5 : sort_items_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_length_one__sift_swap.
  exact PreH7.
Qed.

Lemma proof_of_sort_items_entail_wit_4 : sort_items_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_items_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_sort_items_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_sort_items_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_sort_items_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_sort_items_entail_wit_4_split_goal_5.
Qed.

Lemma proof_of_sort_items_entail_wit_5_split_goal_1 : sort_items_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold HeapSortItemsState.
  split; [lia |].
  split; [lia |].
  split; [eapply Permutation_trans; eauto |].
  split; [exact PreH4 |].
  split.
  - destruct PreH5 as [Hinc Hcross].
    exact Hinc.
  - intros p q Hp Hq.
    destruct PreH5 as [Hinc Hcross].
    apply Hcross; lia.
Qed.

Lemma proof_of_sort_items_entail_wit_5 : sort_items_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_items_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_sort_items_return_wit_1_split_goal_1 : sort_items_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold HeapSortItemsState in PreH11.
  destruct PreH11 as
    (Hgroups_len & Hkeys_len & Hperm & Hheap & Hsuffix & Hcross).
  assert (Hupper : upper = -1 \/ upper = 0) by lia.
  destruct Hupper as [-> | ->].
  - replace (-1 + 1) with 0 in Hsuffix by lia.
    rewrite !sublist_self in Hsuffix by reflexivity.
    exact Hsuffix.
  - replace (0 + 1) with 1 in Hsuffix by lia.
    unfold ItemsIncreasing in Hsuffix |- *.
    destruct Hsuffix as [Hsuffix_len Hsuffix_inc].
    assert (Hnow_len : Zlength groups_now = Zlength keys_now) by lia.
    split.
    + lia.
    + intros i j (Hi & Hij & Hj).
      destruct (Z.eq_dec i 0) as [-> | Hi0].
      * destruct (Z.eq_dec j 0) as [-> | Hj0].
        -- unfold ItemLe. right. split; [reflexivity | lia].
        -- apply Hcross; lia.
      * specialize (Hsuffix_inc (i - 1) (j - 1) ltac:(
          rewrite Zlength_sublist by lia; lia)).
        rewrite (Znth_combine__count_result
          (sublist 1 (Zlength groups_now) groups_now)
          (sublist 1 (Zlength keys_now) keys_now)
          (i - 1) 0 0 Hsuffix_len) in Hsuffix_inc by
          (rewrite Zlength_sublist by lia; lia).
        rewrite (Znth_combine__count_result
          (sublist 1 (Zlength groups_now) groups_now)
          (sublist 1 (Zlength keys_now) keys_now)
          (j - 1) 0 0 Hsuffix_len) in Hsuffix_inc by
          (rewrite Zlength_sublist by lia; lia).
        rewrite !Znth_sublist in Hsuffix_inc by lia.
        replace (i - 1 + 1) with i in Hsuffix_inc by lia.
        replace (j - 1 + 1) with j in Hsuffix_inc by lia.
        rewrite (Znth_combine__count_result groups_now keys_now i 0 0 Hnow_len)
          by lia.
        rewrite (Znth_combine__count_result groups_now keys_now j 0 0 Hnow_len)
          by lia.
        exact Hsuffix_inc.
Qed.

Lemma proof_of_sort_items_return_wit_1_split_goal_2 : sort_items_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold HeapSortItemsState in PreH11.
  tauto.
Qed.

Lemma proof_of_sort_items_return_wit_1 : sort_items_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_items_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_items_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_sort_items_partial_solve_wit_1_pure_split_goal_1 : sort_items_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in PreH14 by lia.
  pose proof (Z.div_mod cnt_pre 2 ltac:(lia)) as Hdiv_cnt.
  pose proof (Z.mod_pos_bound cnt_pre 2 ltac:(lia)) as Hmod_cnt.
  lia.
Qed.

Lemma proof_of_sort_items_partial_solve_wit_1_pure_split_goal_2 : sort_items_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv in PreH14 by lia.
  pose proof (Z.div_mod cnt_pre 2 ltac:(lia)) as Hdiv_cnt.
  pose proof (Z.mod_pos_bound cnt_pre 2 ltac:(lia)) as Hmod_cnt.
  lia.
Qed.

Lemma proof_of_sort_items_partial_solve_wit_1_pure_split_goal_3 : sort_items_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold HeapOrderedExceptAtFromItems.
  intros child Hchild Hparent Hneq.
  apply PreH16.
  - exact Hchild.
  - lia.
Qed.

Lemma proof_of_sort_items_partial_solve_wit_1_pure_split_goal_4 : sort_items_partial_solve_wit_1_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold ExtractionFrameItems.
  rewrite !Zsublist_nil by lia.
  split.
  - unfold ItemsIncreasing.
    split.
    + reflexivity.
    + intros i j Hij. rewrite Zlength_nil in Hij. lia.
  - intros p q Hp Hq. lia.
Qed.

Lemma proof_of_sort_items_partial_solve_wit_1_pure : sort_items_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_items_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_sort_items_partial_solve_wit_1_pure_split_goal_2.
  - Goal_apply proof_of_sort_items_partial_solve_wit_1_pure_split_goal_3.
  - Goal_apply ((ltac:(
      sep_apply (proof_of_sort_items_partial_solve_wit_1_pure_split_goal_4
        cnt_pre key_pre grp_pre cap keys groups root keys_now groups_now
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
        PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16);
      cancel)) :
      ((( &( "grp" ) )) # Ptr |-> grp_pre) **
      (((( &( "key" ) )) # Ptr |-> key_pre) **
       (((( &( "cnt" ) )) # Int |-> cnt_pre) **
        (((( &( "root" ) )) # Int |-> root) **
         ((IntArray.full grp_pre cnt_pre groups_now) **
          (IntArray.full key_pre cnt_pre keys_now))))) |--
      “ ExtractionFrameItems groups_now keys_now ((cnt_pre - 1) + 1) ”).
Qed.

Lemma proof_of_sort_items_partial_solve_wit_10_pure_split_goal_1 : sort_items_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (upper - 1 + 1) with upper by lia.
  dump_pre_spatial.
  exact PreH16.
Qed.

Lemma proof_of_sort_items_partial_solve_wit_10_pure : sort_items_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply
      ((ltac:(
        sep_apply
          (proof_of_sort_items_partial_solve_wit_10_pure_split_goal_1
            cnt_pre key_pre grp_pre cap keys groups groups_now keys_now upper
            PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
            PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16);
        cancel)) :
        ((( &( "grp" ) )) # Ptr |-> grp_pre) **
        (((( &( "key" ) )) # Ptr |-> key_pre) **
        (((( &( "cnt" ) )) # Int |-> cnt_pre) **
        (((( &( "upper" ) )) # Int |-> upper) **
        ((IntArray.full grp_pre cnt_pre groups_now) **
        ((IntArray.full key_pre cnt_pre keys_now) **
        ((( &( "t" ) )) # Int |->_)))))) |--
        “ (ExtractionFrameItems groups_now keys_now (upper - 1 + 1)) ”).
Qed.

Lemma proof_of_count_pairs_safety_wit_6_split_goal_1 : count_pairs_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
  dump_pre_spatial.
  destruct (Z.eq_dec (j - i) 0) as [Hd | Hd].
  - rewrite Hd. cbn. nia.
  - assert (Hdpos : 1 <= j - i) by lia.
    rewrite Z.quot_div_nonneg by nia.
    assert (Hdiv_bound :
      (j - i) * (j - i - 1) / 2 <= (j - i) * (j - i - 1))
      by (apply Z.div_le_upper_bound; nia).
    assert (Hprod_bound : (j - i) * (j - i - 1) <= 90000000000)
      by nia.
    nia.
Qed.

Lemma proof_of_count_pairs_safety_wit_6_split_goal_2 : count_pairs_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
  dump_pre_spatial.
  destruct (Z.eq_dec (j - i) 0) as [Hd | Hd].
  - rewrite Hd. cbn. nia.
  - assert (Hdpos : 1 <= j - i) by lia.
    rewrite Z.quot_div_nonneg by nia.
    assert (Hdiv_nonneg : 0 <= (j - i) * (j - i - 1) / 2)
      by (apply Z_div_nonneg_nonneg; nia).
    nia.
Qed.

Lemma proof_of_count_pairs_safety_wit_6 : count_pairs_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_pairs_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_count_pairs_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_count_pairs_safety_wit_12_split_goal_1 : count_pairs_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
  dump_pre_spatial.
  destruct (Z.eq_dec (j - i) 0) as [Hd | Hd].
  - rewrite Hd. cbn. nia.
  - assert (Hdpos : 1 <= j - i) by lia.
    rewrite Z.quot_div_nonneg by nia.
    assert (Hdiv_bound :
      (j - i) * (j - i - 1) / 2 <= (j - i) * (j - i - 1))
      by (apply Z.div_le_upper_bound; nia).
    assert (Hprod_bound : (j - i) * (j - i - 1) <= 90000000000)
      by nia.
    nia.
Qed.

Lemma proof_of_count_pairs_safety_wit_12_split_goal_2 : count_pairs_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
  dump_pre_spatial.
  destruct (Z.eq_dec (j - i) 0) as [Hd | Hd].
  - rewrite Hd. cbn. nia.
  - assert (Hdpos : 1 <= j - i) by lia.
    rewrite Z.quot_div_nonneg by nia.
    assert (Hdiv_nonneg : 0 <= (j - i) * (j - i - 1) / 2)
      by (apply Z_div_nonneg_nonneg; nia).
    nia.
Qed.

Lemma proof_of_count_pairs_safety_wit_12 : count_pairs_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_pairs_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_count_pairs_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_count_pairs_safety_wit_23_split_goal_1 : count_pairs_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
  dump_pre_spatial.
  destruct (Z.eq_dec (q - p) 0) as [Hd | Hd].
  - rewrite Hd. cbn. nia.
  - assert (Hdpos : 1 <= q - p) by lia.
    rewrite Z.quot_div_nonneg by nia.
    assert (Hdiv_nonneg : 0 <= (q - p) * (q - p - 1) / 2)
      by (apply Z_div_nonneg_nonneg; nia).
    nia.
Qed.

Lemma proof_of_count_pairs_safety_wit_23_split_goal_2 : count_pairs_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
  dump_pre_spatial.
  destruct (Z.eq_dec (q - p) 0) as [Hd | Hd].
  - rewrite Hd. cbn. nia.
  - assert (Hdpos : 1 <= q - p) by lia.
    rewrite Z.quot_div_nonneg by nia.
    assert (Hdiv_bound :
      (q - p) * (q - p - 1) / 2 <= (q - p) * (q - p - 1))
      by (apply Z.div_le_upper_bound; nia).
    assert (Hprod_bound : (q - p) * (q - p - 1) <= 90000000000)
      by nia.
    nia.
Qed.

Lemma proof_of_count_pairs_safety_wit_23 : count_pairs_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_pairs_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_count_pairs_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_count_pairs_safety_wit_29_split_goal_1 : count_pairs_safety_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
  dump_pre_spatial.
  destruct (Z.eq_dec (q - p) 0) as [Hd | Hd].
  - rewrite Hd. cbn. nia.
  - assert (Hdpos : 1 <= q - p) by lia.
    rewrite Z.quot_div_nonneg by nia.
    assert (Hdiv_nonneg : 0 <= (q - p) * (q - p - 1) / 2)
      by (apply Z_div_nonneg_nonneg; nia).
    nia.
Qed.

Lemma proof_of_count_pairs_safety_wit_29_split_goal_2 : count_pairs_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
  dump_pre_spatial.
  destruct (Z.eq_dec (q - p) 0) as [Hd | Hd].
  - rewrite Hd. cbn. nia.
  - assert (Hdpos : 1 <= q - p) by lia.
    rewrite Z.quot_div_nonneg by nia.
    assert (Hdiv_bound :
      (q - p) * (q - p - 1) / 2 <= (q - p) * (q - p - 1))
      by (apply Z.div_le_upper_bound; nia).
    assert (Hprod_bound : (q - p) * (q - p - 1) <= 90000000000)
      by nia.
    nia.
Qed.

Lemma proof_of_count_pairs_safety_wit_29 : count_pairs_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_pairs_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_count_pairs_safety_wit_29_split_goal_2.
Qed.

Lemma proof_of_count_pairs_entail_wit_1_split_goal_1 : count_pairs_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ValueRunBoundary.
  auto.
Qed.

Lemma proof_of_count_pairs_entail_wit_1_split_goal_2 : count_pairs_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_count_pairs_entail_wit_1 : count_pairs_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_pairs_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_count_pairs_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_count_pairs_entail_wit_2_split_goal_1 : count_pairs_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SameValueRange.
  intros q Hq.
  lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_2 : count_pairs_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_count_pairs_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_count_pairs_entail_wit_3_split_goal_1 : count_pairs_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SameValueRange in *.
  intros q Hq.
  destruct (Z.eq_dec q j) as [-> | Hneq].
  - assumption.
  - apply PreH18. lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_3 : count_pairs_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_count_pairs_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_1_split_goal_1 : count_pairs_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by nia.
  apply CountGroupPhase_initial__count_group_close; try assumption; lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_1_split_goal_2 : count_pairs_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RangeRunBoundary. left. reflexivity.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_1_split_goal_3 : count_pairs_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ValueRunBoundary. right. left. lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_1_split_goal_4 : count_pairs_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by nia.
  eapply PairCountPrefix_plus_run_cap__count_group_close; eauto; lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_1_split_goal_5 : count_pairs_entail_wit_4_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.quot_div_nonneg by nia.
  pose proof (choose_two_nonnegative__count_group_close (j - i) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_1 : count_pairs_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_pairs_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_count_pairs_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_count_pairs_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_count_pairs_entail_wit_4_1_split_goal_4.
  - Goal_apply proof_of_count_pairs_entail_wit_4_1_split_goal_5.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_2_split_goal_1 : count_pairs_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i < j) by
    (destruct (Z.eq_dec i j) as [-> | Hneq]; [contradiction | lia]).
  rewrite Z.quot_div_nonneg by nia.
  apply CountGroupPhase_initial__count_group_close; try assumption; lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_2_split_goal_2 : count_pairs_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold RangeRunBoundary. left. reflexivity.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_2_split_goal_3 : count_pairs_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i < j) by
    (destruct (Z.eq_dec i j) as [-> | Hneq]; [contradiction | lia]).
  unfold ValueRunBoundary. right. right. split; [lia |].
  intro Heq.
  apply PreH1.
  rewrite <- Heq.
  apply PreH18. lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_2_split_goal_4 : count_pairs_entail_wit_4_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i < j) by
    (destruct (Z.eq_dec i j) as [-> | Hneq]; [contradiction | lia]).
  rewrite Z.quot_div_nonneg by nia.
  eapply PairCountPrefix_plus_run_cap__count_group_close; eauto; lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_2_split_goal_5 : count_pairs_entail_wit_4_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i < j) by
    (destruct (Z.eq_dec i j) as [-> | Hneq]; [contradiction | lia]).
  rewrite Z.quot_div_nonneg by nia.
  pose proof (choose_two_nonnegative__count_group_close (j - i) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_4_2_split_goal_6 : count_pairs_entail_wit_4_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec i j) as [-> | Hneq]; [contradiction | lia].
Qed.

Lemma proof_of_count_pairs_entail_wit_4_2 : count_pairs_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_pairs_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_count_pairs_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_count_pairs_entail_wit_4_2_split_goal_3.
  - Goal_apply proof_of_count_pairs_entail_wit_4_2_split_goal_4.
  - Goal_apply proof_of_count_pairs_entail_wit_4_2_split_goal_5.
  - Goal_apply proof_of_count_pairs_entail_wit_4_2_split_goal_6.
Qed.

Lemma proof_of_count_pairs_entail_wit_5 : count_pairs_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Right.
  Exists total_3 g_3 p_3 p_3 j_3 i_3 keys_sorted_2 groups_sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    unfold SameValueRange. intros q Hq. lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_6 : count_pairs_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsame : SameValueRange keys_sorted_2 p_3 (q_3 + 1)).
  { apply SameValueRange_extend_right__count_group_close; try assumption; lia. }
  destruct (Z.eq_dec (q_3 + 1) j_3) as [Heq | Hneq].
  - Left.
    Exists total_3 g_3 (q_3 + 1) p_3 j_3 i_3 keys_sorted_2 groups_sorted_2.
    split_pure_spatial.
    + repeat cancel.
    + split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
      all: exact Hsame.
  - Right.
    Exists total_3 g_3 (q_3 + 1) p_3 j_3 i_3 keys_sorted_2 groups_sorted_2.
    split_pure_spatial.
    + repeat cancel.
    + split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
      all: first [exact Hsame | change (q_3 + 1 < j_3); lia].
Qed.

Lemma proof_of_count_pairs_entail_wit_7_1_split_goal_1 : count_pairs_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j.
  assert (Hprod : 0 <= (q - p) * (q - p - 1)) by nia.
  rewrite Z.quot_div_nonneg by nia.
  apply CountGroupPhase_advance_complete_key_run__count_same_key
    with (p := p).
  - lia.
  - lia.
  - lia.
  - eassumption.
  - eassumption.
  - eassumption.
  - eassumption.
  - eassumption.
Qed.

Lemma proof_of_count_pairs_entail_wit_7_1_split_goal_2 : count_pairs_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j.
  unfold RangeRunBoundary. right. left. lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_7_1_split_goal_3 : count_pairs_entail_wit_7_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j.
  assert (Hprod : 0 <= (q - p) * (q - p - 1)) by nia.
  assert (Hchoose : 0 <= ((q - p) * (q - p - 1)) ÷ 2).
  { rewrite Z.quot_div_nonneg by nia.
    apply Z_div_nonneg_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_7_1_split_goal_4 : count_pairs_entail_wit_7_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j.
  assert (Hprod : 0 <= (q - p) * (q - p - 1)) by nia.
  rewrite Z.quot_div_nonneg by nia.
  eapply CountGroupPhase_nonnegative__count_same_key
    with (groups := groups_sorted_2) (keys := keys_sorted_2)
         (i := i) (j := q) (p := q).
  - lia.
  - apply CountGroupPhase_advance_complete_key_run__count_same_key
      with (p := p).
    + lia.
    + lia.
    + lia.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
Qed.

Lemma proof_of_count_pairs_entail_wit_7_1 : count_pairs_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_pairs_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_count_pairs_entail_wit_7_1_split_goal_2.
  - Goal_apply proof_of_count_pairs_entail_wit_7_1_split_goal_3.
  - Goal_apply proof_of_count_pairs_entail_wit_7_1_split_goal_4.
Qed.

Lemma proof_of_count_pairs_entail_wit_7_2_split_goal_1 : count_pairs_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hpq : p < q).
  { destruct (Z.eq_dec p q) as [Heq | Hneq]; [subst q; congruence | lia]. }
  assert (Hprod : 0 <= (q - p) * (q - p - 1)) by nia.
  rewrite Z.quot_div_nonneg by nia.
  apply CountGroupPhase_advance_complete_key_run__count_same_key
    with (p := p).
  - lia.
  - lia.
  - lia.
  - eassumption.
  - eassumption.
  - eassumption.
  - eassumption.
  - eassumption.
Qed.

Lemma proof_of_count_pairs_entail_wit_7_2_split_goal_2 : count_pairs_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hpq : p < q).
  { destruct (Z.eq_dec p q) as [Heq | Hneq]; [subst q; congruence | lia]. }
  unfold RangeRunBoundary. right. right. split; [lia |].
  assert (Hprev := PreH29 (q - 1) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_7_2_split_goal_3 : count_pairs_entail_wit_7_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hpq : p < q).
  { destruct (Z.eq_dec p q) as [Heq | Hneq]; [subst q; congruence | lia]. }
  assert (Hprod : 0 <= (q - p) * (q - p - 1)) by nia.
  assert (Hchoose : 0 <= ((q - p) * (q - p - 1)) ÷ 2).
  { rewrite Z.quot_div_nonneg by nia.
    apply Z_div_nonneg_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_count_pairs_entail_wit_7_2_split_goal_4 : count_pairs_entail_wit_7_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hpq : p < q).
  { destruct (Z.eq_dec p q) as [Heq | Hneq]; [subst q; congruence | lia]. }
  assert (Hprod : 0 <= (q - p) * (q - p - 1)) by nia.
  rewrite Z.quot_div_nonneg by nia.
  eapply CountGroupPhase_nonnegative__count_same_key
    with (groups := groups_sorted_2) (keys := keys_sorted_2)
         (i := i) (j := j) (p := q).
  - lia.
  - apply CountGroupPhase_advance_complete_key_run__count_same_key
      with (p := p).
    + lia.
    + lia.
    + lia.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
Qed.

Lemma proof_of_count_pairs_entail_wit_7_2 : count_pairs_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_pairs_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_count_pairs_entail_wit_7_2_split_goal_2.
  - Goal_apply proof_of_count_pairs_entail_wit_7_2_split_goal_3.
  - Goal_apply proof_of_count_pairs_entail_wit_7_2_split_goal_4.
Qed.

Lemma proof_of_count_pairs_entail_wit_8_split_goal_1 : count_pairs_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hpj : p = j) by lia. subst p.
  apply CountGroupPhase_complete__count_result with (i := i).
  - lia.
  - lia.
  - eassumption.
  - eassumption.
  - eassumption.
  - eassumption.
Qed.

Lemma proof_of_count_pairs_entail_wit_8 : count_pairs_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_count_pairs_entail_wit_8_split_goal_1.
Qed.

Lemma proof_of_count_pairs_return_wit_1_split_goal_1 : count_pairs_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply (PairCountPrefix_parallel_permutation__count_final
    groups keys groups_sorted keys_sorted cnt_pre total).
  - exact PreH5.
  - exact PreH6.
  - exact PreH11.
  - replace cnt_pre with i by lia. exact PreH13.
Qed.

Lemma proof_of_count_pairs_return_wit_1 : count_pairs_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_count_pairs_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg vg) as Hnv_nonneg.
  pose proof (Zlength_nonneg hg) as Hnh_nonneg.
  pose proof (Zlength_nonneg vg_tail) as Hnv_tail.
  pose proof (Zlength_nonneg hg_tail) as Hnh_tail.
  pose proof (PairCountPrefix_bounds__solver_bounds_safety
    vg vk nv retval ltac:(lia) PreH8) as Hv.
  pose proof (PairCountPrefix_bounds__solver_bounds_safety
    hg hk nh retval_2 ltac:(lia) PreH4) as Hh.
  dump_pre_spatial.
  change INT64_MAX with 9223372036854775807.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg vg) as Hnv_nonneg.
  pose proof (Zlength_nonneg hg) as Hnh_nonneg.
  pose proof (Zlength_nonneg vg_tail) as Hnv_tail.
  pose proof (Zlength_nonneg hg_tail) as Hnh_tail.
  pose proof (PairCountPrefix_bounds__solver_bounds_safety
    vg vk nv retval ltac:(lia) PreH8) as Hv.
  pose proof (PairCountPrefix_bounds__solver_bounds_safety
    hg hk nh retval_2 ltac:(lia) PreH4) as Hh.
  dump_pre_spatial.
  change INT64_MIN with (-9223372036854775808).
  nia.
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsegshape__solver_init : forall x lo hi,
    lo <= hi -> IntArray.seg_shape x lo hi |--
      EX l : list Z, IntArray.seg x lo hi l).
  {
    intros x lo hi Hrange.
    unfold IntArray.seg_shape, IntArray.seg.
    remember (Z.to_nat (hi - lo)) as n eqn:Hn.
    assert (Hdiff : Z.of_nat n = hi - lo).
    { subst n. rewrite Z2Nat.id; lia. }
    clear Hn Hrange.
    revert lo hi Hdiff.
    induction n as [|n IH]; intros lo hi Hdiff; simpl.
    - Intros_p Hlohi.
      Exists (@nil Z).
      simpl.
      split_pure_spatial.
      + cancel emp.
      + split_pures; dump_pre_spatial; auto; lia.
    - Intros a.
      sep_apply_l_atomic (IH (lo + 1) hi ltac:(lia)).
      Intros l.
      Exists (a :: l).
      simpl.
      cancel.
  }
  assert (Hxbounds : StreetCoordinateBounds x_lines).
  { unfold StreetCoordinateBounds. intros i Hi. apply PreH7. lia. }
  assert (Hybounds : StreetCoordinateBounds y_lines).
  { unfold StreetCoordinateBounds. intros i Hi. apply PreH8. lia. }
  assert (Hpbounds : PeopleCoordinateBounds people).
  { unfold PeopleCoordinateBounds. intros i Hi.
    specialize (PreH9 i ltac:(lia)).
    rewrite (Znth_indep people i __default__Prod_Z_Z (0, 0)) in PreH9
      by exact Hi.
    destruct PreH9 as [[[Ha Hb] Hc] Hd].
    exact (conj (conj Ha Hb) (conj Hc Hd)). }
  sep_apply_l_atomic (IntArray.full_shape_to_seg_shape va_grp_pre k_pre).
  sep_apply_l_atomic
    (Hsegshape__solver_init va_grp_pre 0 k_pre ltac:(lia)).
  Intros vg_tail.
  sep_apply_l_atomic (IntArray.full_shape_to_seg_shape va_key_pre k_pre).
  sep_apply_l_atomic
    (Hsegshape__solver_init va_key_pre 0 k_pre ltac:(lia)).
  Intros vk_tail.
  sep_apply_l_atomic (IntArray.full_shape_to_seg_shape ha_grp_pre k_pre).
  sep_apply_l_atomic
    (Hsegshape__solver_init ha_grp_pre 0 k_pre ltac:(lia)).
  Intros hg_tail.
  sep_apply_l_atomic (IntArray.full_shape_to_seg_shape ha_key_pre k_pre).
  sep_apply_l_atomic
    (Hsegshape__solver_init ha_key_pre 0 k_pre ltac:(lia)).
  Intros hk_tail.
  prop_apply_p (IntArray.seg_Zlength va_grp_pre 0 k_pre vg_tail).
  Intros_p Hvglen.
  prop_apply_p (IntArray.seg_Zlength va_key_pre 0 k_pre vk_tail).
  Intros_p Hvklen.
  prop_apply_p (IntArray.seg_Zlength ha_grp_pre 0 k_pre hg_tail).
  Intros_p Hhglen.
  prop_apply_p (IntArray.seg_Zlength ha_key_pre 0 k_pre hk_tail).
  Intros_p Hhklen.
  Exists hk_tail hg_tail vk_tail vg_tail
    (@nil Z) (@nil Z) (@nil Z) (@nil Z).
  split_pure_spatial.
  - rewrite (IntArray.full_empty va_grp_pre 0).
    rewrite (IntArray.full_empty va_key_pre 0).
    rewrite (IntArray.full_empty ha_grp_pre 0).
    rewrite (IntArray.full_empty ha_key_pre 0).
    split_pure_spatial.
    + cancel (IntArray.full xs_pre n_pre x_lines).
      cancel (IntArray.full ys_pre m_pre y_lines).
      cancel (IntArray.full px_pre k_pre person_x).
      cancel (IntArray.full py_pre k_pre person_y).
      cancel (IntArray.seg va_grp_pre 0 k_pre vg_tail).
      cancel (IntArray.seg va_key_pre 0 k_pre vk_tail).
      cancel (IntArray.seg ha_grp_pre 0 k_pre hg_tail).
      cancel (IntArray.seg ha_key_pre 0 k_pre hk_tail).
    + split_pures; dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial;
      try assumption;
      try apply ClassifiedPrefix_nil__solver_init;
      try apply ClassifiedCountsCorrect_nil__solver_init;
      try lia.
    all: rewrite Zlength_nil; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmap := PreH20 p ltac:(lia)). destruct Hmap as [Hx Hy].
  assert (Hvert : VerticalEntry x_lines y_lines
      (Znth p people __default__Prod_Z_Z) retval (Znth p person_x 0)).
  { unfold VerticalEntry. rewrite <- Hy. split; [exact PreH3 |].
    split; [lia |]. rewrite Hx. reflexivity. }
  assert (Hmono_y : mono_inc y_lines) by (unfold Pre in PreH16; tauto).
  assert (Hno_h : forall g k,
      ~ HorizontalEntry x_lines y_lines
          (Znth p people __default__Prod_Z_Z) g k).
  { intros g k Hh. unfold HorizontalEntry in Hh.
    destruct Hh as [Hminus _]. rewrite <- Hy in Hminus.
    exact (StripIndex_nonnegative_not_minus_one__solver_classify_append
      y_lines (Znth p person_y 0) retval Hmono_y ltac:(lia) PreH3 Hminus). }
  assert (Hperson : Znth p people __default__Prod_Z_Z = Znth p people (0, 0)).
  { apply Znth_indep. rewrite <- PreH13. lia. }
  rewrite Hperson in Hvert, Hno_h.
  destruct PreH35 as [Hvenum Hhenum].
  assert (Hprefixnext : ClassifiedPrefix x_lines y_lines people (p + 1)
      (vg_2 ++ retval :: nil) (vk_2 ++ Znth p person_x 0 :: nil) hg_2 hk_2).
  { split.
    - eapply EnumeratesEntries_append__solver_classify_append.
      + exact Hvenum.
      + lia.
      + exact Hvert.
    - eapply EnumeratesEntries_skip__solver_classify_append; eauto. }
  assert (Hcountnext : ClassifiedCountsCorrect x_lines y_lines people (p + 1)
      (vg_2 ++ retval :: nil) (vk_2 ++ Znth p person_x 0 :: nil) hg_2 hk_2).
  { eapply ClassifiedCountsCorrect_vertical_extend__classification.
    - exact PreH16.
    - rewrite <- PreH13. lia.
    - split; assumption.
    - exact PreH36.
    - exact Hvert. }
  assert (Hprefixold : ClassifiedPrefix x_lines y_lines people p
      vg_2 vk_2 hg_2 hk_2) by (split; assumption).
  Exists vg_2 vk_2 hg_2 hk_2 hk_tail_2 hg_tail_2
    (sublist 1 (k_pre - nv)
      (replace_Znth 0 (Znth p person_x 0) vk_tail_2))
    (sublist 1 (k_pre - nv) (replace_Znth 0 retval vg_tail_2))
    hk_2 hg_2 (vk_2 ++ Znth p person_x 0 :: nil) (vg_2 ++ retval :: nil).
  split_pure_spatial.
  - replace (nv - nv) with 0 by lia.
    sep_apply (IntArray.seg_split_to_seg va_grp_pre nv (nv + 1) k_pre
      (replace_Znth 0 retval vg_tail_2)); try lia.
    sep_apply (IntArray.seg_split_to_seg va_key_pre nv (nv + 1) k_pre
      (replace_Znth 0 (Znth p person_x 0) vk_tail_2)); try lia.
    assert (Hvgone : sublist 0 1 (replace_Znth 0 retval vg_tail_2) =
        retval :: nil).
    { pose proof (sublist_single 0 0 (replace_Znth 0 retval vg_tail_2)
        ltac:(rewrite Zlength_replace_Znth, PreH31; lia)) as Hsingle.
      simpl in Hsingle.
      rewrite Znth_replace_Znth_Same in Hsingle by (rewrite PreH31; lia).
      exact Hsingle. }
    assert (Hvkone : sublist 0 1
        (replace_Znth 0 (Znth p person_x 0) vk_tail_2) =
        Znth p person_x 0 :: nil).
    { pose proof (sublist_single 0 0
        (replace_Znth 0 (Znth p person_x 0) vk_tail_2)
        ltac:(rewrite Zlength_replace_Znth, PreH32; lia)) as Hsingle.
      simpl in Hsingle.
      rewrite Znth_replace_Znth_Same in Hsingle by (rewrite PreH32; lia).
      exact Hsingle. }
    replace (nv + 1 - nv) with 1 by lia.
    rewrite Hvgone, Hvkone.
    sep_apply (IntArray.full_to_seg va_grp_pre nv vg_2).
    sep_apply (IntArray.seg_merge_to_full va_grp_pre 0 nv (nv + 1)
      vg_2 (retval :: nil)); try lia.
    sep_apply (IntArray.full_to_seg va_key_pre nv vk_2).
    sep_apply (IntArray.seg_merge_to_full va_key_pre 0 nv (nv + 1)
      vk_2 (Znth p person_x 0 :: nil)); try lia.
    replace (va_grp_pre + 0 * sizeof(INT)) with va_grp_pre by lia.
    replace (va_key_pre + 0 * sizeof(INT)) with va_key_pre by lia.
    replace (nv + 1 - 0) with (nv + 1) by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
    all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    all: rewrite Zlength_sublist by
      (rewrite ?Zlength_replace_Znth, ?PreH31, ?PreH32; lia); lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmap := PreH21 p ltac:(lia)). destruct Hmap as [Hx Hy].
  assert (Hminus_y : StripIndex y_lines (Znth p person_y 0) (-1)).
  { pose proof PreH4 as Hstrip. unfold StripIndex in Hstrip |- *.
    destruct Hstrip as [[Heq Hin] | [Hbad _]].
    - left. split; [reflexivity | exact Hin].
    - lia. }
  assert (Hhoriz : HorizontalEntry x_lines y_lines
      (Znth p people __default__Prod_Z_Z) retval_2 (Znth p person_y 0)).
  { unfold HorizontalEntry. rewrite <- Hy. split; [exact Hminus_y |].
    split; [rewrite <- Hx; exact PreH3 |].
    split; [lia |]. rewrite Hy. reflexivity. }
  assert (Hmono_y : mono_inc y_lines) by (unfold Pre in PreH17; tauto).
  assert (Hno_v : forall g k,
      ~ VerticalEntry x_lines y_lines
          (Znth p people __default__Prod_Z_Z) g k).
  { intros g k Hv. unfold VerticalEntry in Hv.
    destruct Hv as [Hstrip [Hg _]]. rewrite <- Hy in Hstrip.
    exact (StripIndex_nonnegative_not_minus_one__solver_classify_append
      y_lines (Znth p person_y 0) g Hmono_y Hg Hstrip Hminus_y). }
  assert (Hperson : Znth p people __default__Prod_Z_Z = Znth p people (0, 0)).
  { apply Znth_indep. rewrite <- PreH14. lia. }
  rewrite Hperson in Hhoriz, Hno_v.
  destruct PreH36 as [Hvenum Hhenum].
  assert (Hprefixnext : ClassifiedPrefix x_lines y_lines people (p + 1)
      vg_2 vk_2 (hg_2 ++ retval_2 :: nil) (hk_2 ++ Znth p person_y 0 :: nil)).
  { split.
    - eapply EnumeratesEntries_skip__solver_classify_append; eauto.
    - eapply EnumeratesEntries_append__solver_classify_append.
      + exact Hhenum.
      + lia.
      + exact Hhoriz. }
  assert (Hcountnext : ClassifiedCountsCorrect x_lines y_lines people (p + 1)
      vg_2 vk_2 (hg_2 ++ retval_2 :: nil) (hk_2 ++ Znth p person_y 0 :: nil)).
  { eapply ClassifiedCountsCorrect_horizontal_extend__classification.
    - exact PreH17.
    - rewrite <- PreH14. lia.
    - split; assumption.
    - exact PreH37.
    - exact Hhoriz. }
  assert (Hprefixold : ClassifiedPrefix x_lines y_lines people p
      vg_2 vk_2 hg_2 hk_2) by (split; assumption).
  Exists vg_2 vk_2 hg_2 hk_2
    (sublist 1 (k_pre - nh)
      (replace_Znth 0 (Znth p person_y 0) hk_tail_2))
    (sublist 1 (k_pre - nh) (replace_Znth 0 retval_2 hg_tail_2))
    vk_tail_2 vg_tail_2
    (hk_2 ++ Znth p person_y 0 :: nil) (hg_2 ++ retval_2 :: nil) vk_2 vg_2.
  split_pure_spatial.
  - replace (nh - nh) with 0 by lia.
    sep_apply (IntArray.seg_split_to_seg ha_grp_pre nh (nh + 1) k_pre
      (replace_Znth 0 retval_2 hg_tail_2)); try lia.
    sep_apply (IntArray.seg_split_to_seg ha_key_pre nh (nh + 1) k_pre
      (replace_Znth 0 (Znth p person_y 0) hk_tail_2)); try lia.
    assert (Hhgone : sublist 0 1 (replace_Znth 0 retval_2 hg_tail_2) =
        retval_2 :: nil).
    { pose proof (sublist_single 0 0 (replace_Znth 0 retval_2 hg_tail_2)
        ltac:(rewrite Zlength_replace_Znth, PreH34; lia)) as Hsingle.
      simpl in Hsingle.
      rewrite Znth_replace_Znth_Same in Hsingle by (rewrite PreH34; lia).
      exact Hsingle. }
    assert (Hhkone : sublist 0 1
        (replace_Znth 0 (Znth p person_y 0) hk_tail_2) =
        Znth p person_y 0 :: nil).
    { pose proof (sublist_single 0 0
        (replace_Znth 0 (Znth p person_y 0) hk_tail_2)
        ltac:(rewrite Zlength_replace_Znth, PreH35; lia)) as Hsingle.
      simpl in Hsingle.
      rewrite Znth_replace_Znth_Same in Hsingle by (rewrite PreH35; lia).
      exact Hsingle. }
    replace (nh + 1 - nh) with 1 by lia.
    rewrite Hhgone, Hhkone.
    sep_apply (IntArray.full_to_seg ha_grp_pre nh hg_2).
    sep_apply (IntArray.seg_merge_to_full ha_grp_pre 0 nh (nh + 1)
      hg_2 (retval_2 :: nil)); try lia.
    sep_apply (IntArray.full_to_seg ha_key_pre nh hk_2).
    sep_apply (IntArray.seg_merge_to_full ha_key_pre 0 nh (nh + 1)
      hk_2 (Znth p person_y 0 :: nil)); try lia.
    replace (ha_grp_pre + 0 * sizeof(INT)) with ha_grp_pre by lia.
    replace (ha_key_pre + 0 * sizeof(INT)) with ha_key_pre by lia.
    replace (nh + 1 - 0) with (nh + 1) by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
    all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    all: rewrite Zlength_sublist by
      (rewrite ?Zlength_replace_Znth, ?PreH34, ?PreH35; lia); lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmap := PreH21 p ltac:(lia)). destruct Hmap as [Hx Hy].
  assert (Hxin : In (Znth p person_x 0) x_lines).
  { pose proof PreH3 as Hstrip. unfold StripIndex in Hstrip.
    destruct Hstrip as [[_ Hin] | [Hbad _]]; [exact Hin | lia]. }
  assert (Hyin : In (Znth p person_y 0) y_lines).
  { pose proof PreH4 as Hstrip. unfold StripIndex in Hstrip.
    destruct Hstrip as [[_ Hin] | [Hbad _]]; [exact Hin | lia]. }
  assert (Hperson : Znth p people __default__Prod_Z_Z = Znth p people (0, 0)).
  { apply Znth_indep. rewrite <- PreH14. lia. }
  rewrite Hperson in Hx, Hy.
  eapply ClassifiedCountsCorrect_intersection_extend__classification.
  - exact PreH17.
  - rewrite <- PreH14. lia.
  - exact PreH37.
  - rewrite <- Hx. exact Hxin.
  - rewrite <- Hy. exact Hyin.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmap := PreH21 p ltac:(lia)). destruct Hmap as [Hx Hy].
  assert (Hminus_x : StripIndex x_lines (Znth p person_x 0) (-1)).
  { pose proof PreH3 as Hstrip. unfold StripIndex in Hstrip |- *.
    destruct Hstrip as [[_ Hin] | [Hbad _]].
    - left. split; [reflexivity | exact Hin].
    - lia. }
  assert (Hminus_y : StripIndex y_lines (Znth p person_y 0) (-1)).
  { pose proof PreH4 as Hstrip. unfold StripIndex in Hstrip |- *.
    destruct Hstrip as [[_ Hin] | [Hbad _]].
    - left. split; [reflexivity | exact Hin].
    - lia. }
  assert (Hmono_x : mono_inc x_lines) by (unfold Pre in PreH17; tauto).
  assert (Hmono_y : mono_inc y_lines) by (unfold Pre in PreH17; tauto).
  assert (Hno_v : forall g k,
      ~ VerticalEntry x_lines y_lines
          (Znth p people __default__Prod_Z_Z) g k).
  { intros g k Hv. unfold VerticalEntry in Hv.
    destruct Hv as [Hstrip [Hg _]]. rewrite <- Hy in Hstrip.
    exact (StripIndex_nonnegative_not_minus_one__solver_classify_append
      y_lines (Znth p person_y 0) g Hmono_y Hg Hstrip Hminus_y). }
  assert (Hno_h : forall g k,
      ~ HorizontalEntry x_lines y_lines
          (Znth p people __default__Prod_Z_Z) g k).
  { intros g k Hh. unfold HorizontalEntry in Hh.
    destruct Hh as [_ [Hstrip [Hg _]]]. rewrite <- Hx in Hstrip.
    exact (StripIndex_nonnegative_not_minus_one__solver_classify_append
      x_lines (Znth p person_x 0) g Hmono_x Hg Hstrip Hminus_x). }
  assert (Hperson : Znth p people __default__Prod_Z_Z = Znth p people (0, 0)).
  { apply Znth_indep. rewrite <- PreH14. lia. }
  rewrite Hperson in Hno_v, Hno_h.
  destruct PreH36 as [Hvenum Hhenum].
  split.
  - eapply EnumeratesEntries_skip__solver_classify_append; eauto.
  - eapply EnumeratesEntries_skip__solver_classify_append; eauto.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_3 : solver_entail_wit_2_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH21. assumption.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_1 : solver_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH16 q H).
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_1 : solver_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH16 q H).
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_3_split_goal_1 : solver_entail_wit_3_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH16 q H).
Qed.

Lemma proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace k_pre with p by lia.
  exact PreH33.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace k_pre with p by lia.
  exact PreH32.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (PreH17 q H).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Spec.
  unfold ClassifiedCountsCorrect in PreH34.
  specialize (PreH34 retval retval_2).
  dump_pre_spatial.
  rewrite <- PreH17.
  apply PreH34.
  - rewrite PreH25. exact PreH8.
  - rewrite PreH27. exact PreH4.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg groups_after) as Hgroups_after_nonneg.
  pose proof (Zlength_nonneg groups_after_2) as Hgroups_after_2_nonneg.
  pose proof (Zlength_nonneg vg_tail) as Hvg_tail_nonneg.
  pose proof (Zlength_nonneg hg_tail) as Hhg_tail_nonneg.
  assert (Hnv : 0 <= nv <= k_pre) by lia.
  assert (Hnh : 0 <= nh <= k_pre) by lia.
  sep_apply_l_atomic (IntArray.full_to_seg va_grp_pre nv groups_after).
  sep_apply_l_atomic (IntArray.seg_merge_to_full va_grp_pre 0 nv k_pre groups_after vg_tail Hnv).
  replace (va_grp_pre + 0 * sizeof(INT)) with va_grp_pre by lia.
  replace (k_pre - 0) with k_pre by lia.
  sep_apply_l_atomic (IntArray.full_to_full_shape va_grp_pre k_pre (groups_after ++ vg_tail)).
  sep_apply_l_atomic (IntArray.full_to_seg va_key_pre nv keys_after).
  sep_apply_l_atomic (IntArray.seg_merge_to_full va_key_pre 0 nv k_pre keys_after vk_tail Hnv).
  replace (va_key_pre + 0 * sizeof(INT)) with va_key_pre by lia.
  replace (k_pre - 0) with k_pre by lia.
  sep_apply_l_atomic (IntArray.full_to_full_shape va_key_pre k_pre (keys_after ++ vk_tail)).
  sep_apply_l_atomic (IntArray.full_to_seg ha_grp_pre nh groups_after_2).
  sep_apply_l_atomic (IntArray.seg_merge_to_full ha_grp_pre 0 nh k_pre groups_after_2 hg_tail Hnh).
  replace (ha_grp_pre + 0 * sizeof(INT)) with ha_grp_pre by lia.
  replace (k_pre - 0) with k_pre by lia.
  sep_apply_l_atomic (IntArray.full_to_full_shape ha_grp_pre k_pre (groups_after_2 ++ hg_tail)).
  sep_apply_l_atomic (IntArray.full_to_seg ha_key_pre nh keys_after_2).
  sep_apply_l_atomic (IntArray.seg_merge_to_full ha_key_pre 0 nh k_pre keys_after_2 hk_tail Hnh).
  replace (ha_key_pre + 0 * sizeof(INT)) with ha_key_pre by lia.
  replace (k_pre - 0) with k_pre by lia.
  sep_apply_l_atomic (IntArray.full_to_full_shape ha_key_pre k_pre (keys_after_2 ++ hk_tail)).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH25.
  destruct PreH25 as [_ [_ [Hmono _]]].
  dump_pre_spatial.
  exact Hmono.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_2 : solver_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH25.
  destruct PreH25 as [_ [_ [_ [_ [_ [Hy0 _]]]]]].
  dump_pre_spatial.
  exact Hy0.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_3 : solver_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH25.
  destruct PreH25 as [_ [_ [_ [_ [_ [_ [Hylast _]]]]]]].
  dump_pre_spatial.
  rewrite PreH21.
  exact Hylast.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_4 : solver_partial_solve_wit_2_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH29 p ltac:(lia)).
  unfold PeopleCoordinateBounds in PreH28.
  specialize (PreH28 p ltac:(rewrite <- PreH22; lia)).
  rewrite (Znth_indep people p __default__Prod_Z_Z (0, 0)) in PreH29
    by (rewrite <- PreH22; lia).
  destruct PreH29 as [_ Hy].
  destruct PreH28 as [_ [Hylo Hyhi]].
  dump_pre_spatial.
  rewrite Hy. exact Hylo.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_5 : solver_partial_solve_wit_2_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH29 p ltac:(lia)).
  unfold PeopleCoordinateBounds in PreH28.
  specialize (PreH28 p ltac:(rewrite <- PreH22; lia)).
  rewrite (Znth_indep people p __default__Prod_Z_Z (0, 0)) in PreH29
    by (rewrite <- PreH22; lia).
  destruct PreH29 as [_ Hy].
  destruct PreH28 as [_ [Hylo Hyhi]].
  dump_pre_spatial.
  rewrite Hy. exact Hyhi.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_5.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_1 : solver_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH28.
  destruct PreH28 as [_ [Hmono _]].
  dump_pre_spatial.
  exact Hmono.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_2 : solver_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH28.
  destruct PreH28 as [_ [_ [_ [Hx0 _]]]].
  dump_pre_spatial.
  exact Hx0.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_3 : solver_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold Pre in PreH28.
  destruct PreH28 as [_ [_ [_ [_ [Hxlast _]]]]].
  dump_pre_spatial.
  rewrite PreH23.
  exact Hxlast.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_4 : solver_partial_solve_wit_4_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH32 p ltac:(lia)).
  unfold PeopleCoordinateBounds in PreH31.
  specialize (PreH31 p ltac:(rewrite <- PreH25; lia)).
  rewrite (Znth_indep people p __default__Prod_Z_Z (0, 0)) in PreH32
    by (rewrite <- PreH25; lia).
  destruct PreH32 as [Hx _].
  destruct PreH31 as [[Hxlo Hxhi] _].
  dump_pre_spatial.
  rewrite Hx. exact Hxlo.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_5 : solver_partial_solve_wit_4_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH32 p ltac:(lia)).
  unfold PeopleCoordinateBounds in PreH31.
  specialize (PreH31 p ltac:(rewrite <- PreH25; lia)).
  rewrite (Znth_indep people p __default__Prod_Z_Z (0, 0)) in PreH32
    by (rewrite <- PreH25; lia).
  destruct PreH32 as [Hx _].
  destruct PreH31 as [[Hxlo Hxhi] _].
  dump_pre_spatial.
  rewrite Hx. exact Hxhi.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_5.
Qed.

Lemma proof_of_solver_partial_solve_wit_11_pure_split_goal_1 : solver_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg vg) as Hlen.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_11_pure_split_goal_2 : solver_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg vg_tail) as Hlen.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_11_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_11_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_12_pure_split_goal_1 : solver_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg hg) as Hlen.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_12_pure_split_goal_2 : solver_partial_solve_wit_12_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg hg_tail) as Hlen.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_12_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_12_pure_split_goal_2.
Qed.
