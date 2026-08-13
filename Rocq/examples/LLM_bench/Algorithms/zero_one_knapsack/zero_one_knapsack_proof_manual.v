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
From SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack Require Import zero_one_knapsack_goal.
From SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack Require Import zero_one_knapsack_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_lib.
Local Open Scope sac.

Lemma proof_of_zeroOneKnapsack_safety_wit_22_split_goal_1 : zeroOneKnapsack_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  unfold KnapsackRowAnnotationState in PreH42.
  destruct PreH42 as [Hstatic [_ [_ [_ [Hshape [Hdp_bounds _]]]]]].
  unfold KnapsackStaticSafety in Hstatic.
  destruct Hstatic as [_ [_ [_ [_ Hinputs]]]].
  unfold KnapsackInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ Hvalues_bounds]]].
  unfold KnapsackTablePrefixShape in Hshape.
  destruct Hshape as [_ Hdp_len].
  unfold KnapsackTableValuesBounded in Hdp_bounds.
  specialize (Hdp_bounds
    ((i - 1) * width + (j - Znth (i - 1) weights_l 0) - 0)).
  specialize (Hvalues_bounds (i - 1)).
  rewrite Hdp_len in Hdp_bounds.
  lia.
Qed.

Lemma proof_of_zeroOneKnapsack_safety_wit_22_split_goal_2 : zeroOneKnapsack_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  unfold KnapsackRowAnnotationState in PreH42.
  destruct PreH42 as [Hstatic [_ [_ [_ [Hshape [Hdp_bounds _]]]]]].
  unfold KnapsackStaticSafety in Hstatic.
  destruct Hstatic as [_ [_ [_ [_ Hinputs]]]].
  unfold KnapsackInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ Hvalues_bounds]]].
  unfold KnapsackTablePrefixShape in Hshape.
  destruct Hshape as [_ Hdp_len].
  unfold KnapsackTableValuesBounded in Hdp_bounds.
  specialize (Hdp_bounds
    ((i - 1) * width + (j - Znth (i - 1) weights_l 0) - 0)).
  specialize (Hvalues_bounds (i - 1)).
  rewrite Hdp_len in Hdp_bounds.
  lia.
Qed.

Lemma proof_of_zeroOneKnapsack_safety_wit_22 : zeroOneKnapsack_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_zeroOneKnapsack_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_zeroOneKnapsack_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_zeroOneKnapsack_safety_wit_29_split_goal_1 : zeroOneKnapsack_safety_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (IntArray.full_length_range dp_pre
    ((n_pre + 1) * (capacity_pre + 1)) dp_l).
  Intros_p Hdp_range.
  dump_pre_spatial.
  change (0 <= (n_pre + 1) * (capacity_pre + 1) * 4 <= 4294967296)
    in Hdp_range.
  lia.
Qed.

Lemma proof_of_zeroOneKnapsack_safety_wit_29_split_goal_2 : zeroOneKnapsack_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_zeroOneKnapsack_safety_wit_29 : zeroOneKnapsack_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_zeroOneKnapsack_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_zeroOneKnapsack_safety_wit_29_split_goal_2.
Qed.

Lemma proof_of_zeroOneKnapsack_safety_wit_30_split_goal_1 : zeroOneKnapsack_safety_wit_30_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (IntArray.full_length_range weights_pre n_pre weights_l).
  prop_apply_p (IntArray.full_length_range dp_pre
    ((n_pre + 1) * (capacity_pre + 1)) dp_l).
  Intros_p Hn_range.
  Intros_p Hdp_range.
  dump_pre_spatial.
  change (0 <= n_pre * 4 <= 4294967296) in Hn_range.
  change (0 <= (n_pre + 1) * (capacity_pre + 1) * 4 <= 4294967296)
    in Hdp_range.
  nia.
Qed.

Lemma proof_of_zeroOneKnapsack_safety_wit_30_split_goal_2 : zeroOneKnapsack_safety_wit_30_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (IntArray.full_length_range weights_pre n_pre weights_l).
  prop_apply_p (IntArray.full_length_range dp_pre
    ((n_pre + 1) * (capacity_pre + 1)) dp_l).
  Intros_p Hn_range.
  Intros_p Hdp_range.
  dump_pre_spatial.
  change (0 <= n_pre * 4 <= 4294967296) in Hn_range.
  change (0 <= (n_pre + 1) * (capacity_pre + 1) * 4 <= 4294967296)
    in Hdp_range.
  nia.
Qed.

Lemma proof_of_zeroOneKnapsack_safety_wit_30 : zeroOneKnapsack_safety_wit_30.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_zeroOneKnapsack_safety_wit_30_split_goal_1.
  - Goal_apply proof_of_zeroOneKnapsack_safety_wit_30_split_goal_2.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_1 : zeroOneKnapsack_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  Exists (@nil Z).
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    sep_apply (IntArray.undef_full_split_to_undef_seg
      dp_pre 0 ((n_pre + 1) * (capacity_pre + 1))).
    + cancel (IntArray.undef_seg dp_pre 0
        ((n_pre + 1) * (capacity_pre + 1))).
      rewrite IntArray.undef_seg_empty.
      rewrite IntArray.seg_empty.
      replace (0 * (capacity_pre + 1)) with 0 by lia.
      cancel (IntArray.undef_seg dp_pre 0
        ((n_pre + 1) * (capacity_pre + 1))).
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial; lia.
    + nia.
  - split_pures; dump_pre_spatial; try lia.
    unfold KnapsackRowsAnnotationState.
    split.
    + unfold KnapsackStaticSafety.
      split; [lia|].
      split; [lia|].
      split; [lia|].
      split; [lia|].
      exact PreH5.
    + split; [lia|].
      split; [nia|].
      split.
      * unfold KnapsackTablePrefixShape.
        constructor.
        -- apply Z.le_refl.
        -- reflexivity.
      * split.
        -- unfold KnapsackTableValuesBounded.
           intros k Hk.
           exfalso.
           rewrite Zlength_nil in Hk.
           lia.
        -- unfold KnapsackRowsDone, KnapsackTablePrefix.
           intros row col Hrow Hcol Hidx.
           exfalso.
           unfold KnapsackCellIndex in Hidx.
           nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_2 : zeroOneKnapsack_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia).
  Exists dp_l_2.
  split_pure_spatial.
  - replace (i * width + 0) with (i * width) by lia.
    cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.seg dp_pre 0 (i * width) dp_l_2).
    derivable1_refl_tac.
  - split_pures; dump_pre_spatial; try lia.
    unfold KnapsackRowsAnnotationState in PreH9.
    unfold KnapsackRowAnnotationState.
    destruct PreH9 as
      [Hstatic [Hrows [Htotal [Hshape [Hbounded Hdone]]]]].
    split; [exact Hstatic|].
    split; [lia|].
    split; [lia|].
    split; [nia|].
    split.
    + unfold KnapsackTablePrefixShape in *.
      destruct Hshape as [Hwritten Hlength].
      constructor; nia.
    + split; [exact Hbounded|].
      apply KnapsackRowsDone_to_RowProgress0; try exact Hdone; lia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_3_split_goal_1 : zeroOneKnapsack_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (i < n_pre + 1) by lia.
  nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_3 : zeroOneKnapsack_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_zeroOneKnapsack_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_5_split_goal_1 : zeroOneKnapsack_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_5 : zeroOneKnapsack_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_zeroOneKnapsack_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_6_split_goal_1 : zeroOneKnapsack_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold KnapsackRowAnnotationState in PreH40.
  destruct PreH40 as [Hstatic _].
  unfold KnapsackStaticSafety in Hstatic.
  destruct Hstatic as [_ [_ [Hwidth [_ Hinputs]]]].
  unfold KnapsackInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [Hweights _]]].
  pose proof (Hweights (i - 1) ltac:(lia)) as Hweight_pos.
  assert (1 <= width) by lia.
  clear - Hweight_pos H.
  nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_6 : zeroOneKnapsack_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_zeroOneKnapsack_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_7_1 : zeroOneKnapsack_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: assert (Hcell : KnapsackCellCorrect weights_l values_l i j 0) by
    (subst i;
     apply KnapsackCellCorrect_row0_zero; try lia;
     unfold KnapsackRowAnnotationState in PreH24;
     destruct PreH24 as [Hsafety _];
     unfold KnapsackStaticSafety in Hsafety;
     destruct Hsafety as [_ [_ [_ [_ Hinputs]]]];
     unfold KnapsackInputsBounded in Hinputs;
     destruct Hinputs as [Hweights_len [Hvalues_len _]];
     lia).
  all: Exists (dp_l_2 ++ 0 :: nil).
  all: split_pure_spatial.
  all: try (replace (i * width + (j + 1)) with
              (i * width + j + 1) by lia;
            repeat cancel).
  all: split_pures; dump_pre_spatial; try lia; try assumption.
  all: apply KnapsackRowAnnotationState_append_cell__row_state_result_refactor;
       try assumption; try lia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_7_2 : zeroOneKnapsack_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: assert (Hcell : KnapsackCellCorrect weights_l values_l i j 0) by
    (subst j;
     apply KnapsackCellCorrect_col0_zero;
     unfold KnapsackRowAnnotationState in PreH25;
     destruct PreH25 as [Hsafety _];
     unfold KnapsackStaticSafety in Hsafety;
     destruct Hsafety as [_ [_ [_ [_ Hinputs]]]];
     unfold KnapsackInputsBounded in Hinputs;
     destruct Hinputs as
       [Hweights_len [Hvalues_len [Hweights_bound Hvalues_bound]]];
     try lia;
     intros k Hk;
     apply Hweights_bound;
     lia).
  all: Exists (dp_l_2 ++ 0 :: nil).
  all: split_pure_spatial.
  all: try (replace (i * width + (j + 1)) with
              (i * width + j + 1) by lia;
            repeat cancel).
  all: split_pures; dump_pre_spatial; try lia; try assumption.
  all: apply KnapsackRowAnnotationState_append_cell__row_state_result_refactor;
       try assumption; try lia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_7_3 : zeroOneKnapsack_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(lia).
  all: pose proof PreH43 as Hstate_facts.
  all: unfold KnapsackRowAnnotationState in Hstate_facts.
  all: destruct Hstate_facts as
    [Hsafety [_ [_ [_ [_ [_ Hprogress]]]]]].
  all: unfold KnapsackStaticSafety in Hsafety.
  all: destruct Hsafety as [_ [_ [Hwidth [_ Hinputs]]]].
  all: unfold KnapsackInputsBounded in Hinputs.
  all: destruct Hinputs as
    [Hweights_len [Hvalues_len [Hweights_bound Hvalues_bound]]].
  all: assert (Hweight_positive :
      1 <= Znth (i - 1) weights_l 0) by
    (apply Hweights_bound; lia).
  all: assert (Hwithout :
      KnapsackCellCorrect weights_l values_l (i - 1) j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (replace ((((i - 1) * width) + j) - 0) with
       (KnapsackCellIndex capacity_pre (i - 1) j) by
       (unfold KnapsackCellIndex; lia);
     eapply KnapsackRowProgress_lookup_cell; try eassumption;
     try lia;
     unfold KnapsackCellIndex;
     nia).
  all: assert (Hprevious :
      KnapsackCellCorrect weights_l values_l (i - 1)
        (j - Znth (i - 1) weights_l 0)
        (Znth ((((i - 1) * width) +
          (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0)) by
    (replace ((((i - 1) * width) +
          (j - Znth (i - 1) weights_l 0)) - 0) with
       (KnapsackCellIndex capacity_pre (i - 1)
          (j - Znth (i - 1) weights_l 0)) by
       (unfold KnapsackCellIndex; lia);
     eapply KnapsackRowProgress_lookup_cell; try eassumption;
     try lia;
     unfold KnapsackCellIndex;
     nia).
  all: assert (Hcell_step :
      KnapsackCellCorrect weights_l values_l ((i - 1) + 1) j
        (Znth ((((i - 1) * width) +
           (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0 +
         Znth (i - 1) values_l 0)) by
    (eapply KnapsackCellCorrect_take_better
       with (item := i - 1)
            (w := Znth (i - 1) weights_l 0)
            (v := Znth (i - 1) values_l 0)
            (without := Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)
            (prev := Znth ((((i - 1) * width) +
              (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0);
     try eassumption; try reflexivity; try lia;
     intros k Hk;
     assert (Hk_n : 0 <= k < n_pre) by
       (rewrite <- Hweights_len; exact Hk);
     pose proof (Hweights_bound k Hk_n);
     lia).
  all: assert (Hcell :
      KnapsackCellCorrect weights_l values_l i j
        (Znth ((((i - 1) * width) +
           (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0 +
         Znth (i - 1) values_l 0)) by
    (replace ((i - 1) + 1) with i in Hcell_step by lia;
     exact Hcell_step).
  all: assert (Hcell_bound :
      0 <= Znth ((((i - 1) * width) +
           (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0 +
           Znth (i - 1) values_l 0 <= 4000000) by
    (eapply KnapsackCellCorrect_value_bound with (n := n_pre);
     try eassumption; try lia;
     intros k Hk;
     apply Hvalues_bound;
     lia).
  all: Exists (dp_l_2 ++
    (Znth ((((i - 1) * width) +
       (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0 +
     Znth (i - 1) values_l 0) :: nil).
  all: split_pure_spatial.
  all: try (replace (i * width + (j + 1)) with
              (i * width + j + 1) by lia;
            repeat cancel).
  all: split_pures; dump_pre_spatial; try lia; try assumption.
  all: apply KnapsackRowAnnotationState_append_cell__row_state_result_refactor;
       try assumption; try lia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_7_4 : zeroOneKnapsack_entail_wit_7_4.
Proof.
  LLM_pre_process ltac:(lia).
  all: pose proof PreH43 as Hstate_facts.
  all: unfold KnapsackRowAnnotationState in Hstate_facts.
  all: destruct Hstate_facts as
    [Hsafety [_ [_ [_ [_ [_ Hprogress]]]]]].
  all: unfold KnapsackStaticSafety in Hsafety.
  all: destruct Hsafety as [_ [_ [Hwidth [_ Hinputs]]]].
  all: unfold KnapsackInputsBounded in Hinputs.
  all: destruct Hinputs as
    [Hweights_len [Hvalues_len [Hweights_bound Hvalues_bound]]].
  all: assert (Hweight_positive :
      1 <= Znth (i - 1) weights_l 0) by
    (apply Hweights_bound; lia).
  all: assert (Hwithout :
      KnapsackCellCorrect weights_l values_l (i - 1) j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (replace ((((i - 1) * width) + j) - 0) with
       (KnapsackCellIndex capacity_pre (i - 1) j) by
       (unfold KnapsackCellIndex; lia);
     eapply KnapsackRowProgress_lookup_cell; try eassumption;
     try lia;
     unfold KnapsackCellIndex;
     nia).
  all: assert (Hprevious :
      KnapsackCellCorrect weights_l values_l (i - 1)
        (j - Znth (i - 1) weights_l 0)
        (Znth ((((i - 1) * width) +
          (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0)) by
    (replace ((((i - 1) * width) +
          (j - Znth (i - 1) weights_l 0)) - 0) with
       (KnapsackCellIndex capacity_pre (i - 1)
          (j - Znth (i - 1) weights_l 0)) by
       (unfold KnapsackCellIndex; lia);
     eapply KnapsackRowProgress_lookup_cell; try eassumption;
     try lia;
     unfold KnapsackCellIndex;
     nia).
  all: assert (Hcell_step :
      KnapsackCellCorrect weights_l values_l ((i - 1) + 1) j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (eapply KnapsackCellCorrect_keep_without_when_better_or_equal
       with (item := i - 1)
            (w := Znth (i - 1) weights_l 0)
            (v := Znth (i - 1) values_l 0)
            (prev := Znth ((((i - 1) * width) +
              (j - Znth (i - 1) weights_l 0)) - 0) dp_l_2 0);
     try eassumption; try reflexivity; try lia;
     intros k Hk;
     assert (Hk_n : 0 <= k < n_pre) by
       (rewrite <- Hweights_len; exact Hk);
     pose proof (Hweights_bound k Hk_n);
     lia).
  all: assert (Hcell :
      KnapsackCellCorrect weights_l values_l i j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (replace ((i - 1) + 1) with i in Hcell_step by lia;
     exact Hcell_step).
  all: assert (Hcell_bound :
      0 <= Znth ((((i - 1) * width) + j) - 0) dp_l_2 0 <= 4000000) by
    (eapply KnapsackCellCorrect_value_bound with (n := n_pre);
     try eassumption; try lia;
     intros k Hk;
     apply Hvalues_bound;
     lia).
  all: Exists (dp_l_2 ++
    Znth ((((i - 1) * width) + j) - 0) dp_l_2 0 :: nil).
  all: split_pure_spatial.
  all: try (replace (i * width + (j + 1)) with
              (i * width + j + 1) by lia;
            repeat cancel).
  all: split_pures; dump_pre_spatial; try lia; try assumption.
  all: apply KnapsackRowAnnotationState_append_cell__row_state_result_refactor;
       try assumption; try lia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_7_5 : zeroOneKnapsack_entail_wit_7_5.
Proof.
  LLM_pre_process ltac:(lia).
  all: pose proof PreH38 as Hstate_facts.
  all: unfold KnapsackRowAnnotationState in Hstate_facts.
  all: destruct Hstate_facts as
    [Hsafety [_ [_ [_ [_ [_ Hprogress]]]]]].
  all: unfold KnapsackStaticSafety in Hsafety.
  all: destruct Hsafety as [_ [_ [Hwidth [_ Hinputs]]]].
  all: unfold KnapsackInputsBounded in Hinputs.
  all: destruct Hinputs as
    [Hweights_len [Hvalues_len [Hweights_bound Hvalues_bound]]].
  all: assert (Hwithout :
      KnapsackCellCorrect weights_l values_l (i - 1) j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (replace ((((i - 1) * width) + j) - 0) with
       (KnapsackCellIndex capacity_pre (i - 1) j) by
       (unfold KnapsackCellIndex; lia);
     eapply KnapsackRowProgress_lookup_cell; try eassumption;
     try lia;
     unfold KnapsackCellIndex;
     nia).
  all: assert (Hcell_step :
      KnapsackCellCorrect weights_l values_l ((i - 1) + 1) j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (eapply KnapsackCellCorrect_too_heavy
       with (item := i - 1)
            (w := Znth (i - 1) weights_l 0)
            (v := Znth (i - 1) values_l 0);
     try eassumption; try reflexivity; try lia;
     intros k Hk;
     assert (Hk_n : 0 <= k < n_pre) by
       (rewrite <- Hweights_len; exact Hk);
     pose proof (Hweights_bound k Hk_n);
     lia).
  all: assert (Hcell :
      KnapsackCellCorrect weights_l values_l i j
        (Znth ((((i - 1) * width) + j) - 0) dp_l_2 0)) by
    (replace ((i - 1) + 1) with i in Hcell_step by lia;
     exact Hcell_step).
  all: assert (Hcell_bound :
      0 <= Znth ((((i - 1) * width) + j) - 0) dp_l_2 0 <= 4000000) by
    (eapply KnapsackCellCorrect_value_bound with (n := n_pre);
     try eassumption; try lia;
     intros k Hk;
     apply Hvalues_bound;
     lia).
  all: Exists (dp_l_2 ++
    Znth ((((i - 1) * width) + j) - 0) dp_l_2 0 :: nil).
  all: split_pure_spatial.
  all: try (replace (i * width + (j + 1)) with
              (i * width + j + 1) by lia;
            repeat cancel).
  all: split_pures; dump_pre_spatial; try lia; try assumption.
  all: apply KnapsackRowAnnotationState_append_cell__row_state_result_refactor;
       try assumption; try lia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_8 : zeroOneKnapsack_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia).
  all: assert (Hj_end : j = capacity_pre + 1) by lia.
  all: assert (Hrows_state :
      KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width
        dp_l_2 (i + 1)) by
    (unfold KnapsackRowAnnotationState in PreH11;
     destruct PreH11 as
       [Hsafety [Hrow [Hcol [Hwritten [Hshape [Hbounded Hprogress]]]]]];
     unfold KnapsackRowsAnnotationState;
     split; [exact Hsafety|];
     split; [lia|];
     split; [nia|];
     split;
     [ unfold KnapsackTablePrefixShape in *;
       destruct Hshape as [Hnonnegative Hlength];
       split; [nia|];
       rewrite Hlength;
       nia
     | split; [exact Hbounded|];
       eapply KnapsackRowProgress_end_to_RowsDone;
       [exact Hj_end|exact Hprogress] ]).
  all: Exists dp_l_2.
  all: split_pure_spatial.
  all: try (replace ((i + 1) * width) with
              (i * width + j) by nia;
            repeat cancel).
  all: split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_9 : zeroOneKnapsack_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia).
  all: assert (Hi_end : i = n_pre + 1) by lia.
  all: assert (Hresult :
      KnapsackResultState weights_l values_l n_pre capacity_pre dp_l_2
        (Znth (n_pre * width + capacity_pre) dp_l_2 0)) by
    (subst i;
     apply KnapsackRowsAnnotationState_to_Result__row_state_result_refactor;
     exact PreH9).
  all: Exists dp_l_2.
  all: split_pure_spatial.
  all: try (subst i;
            replace ((n_pre + 1) * width) with
              ((n_pre + 1) * (capacity_pre + 1)) by nia;
            rewrite IntArray.undef_seg_empty;
            sep_apply (IntArray.seg_to_full dp_pre 0
              ((n_pre + 1) * (capacity_pre + 1)) dp_l_2);
            replace (dp_pre + 0 * sizeof (INT)) with dp_pre by lia;
            replace ((n_pre + 1) * (capacity_pre + 1) - 0) with
              ((n_pre + 1) * (capacity_pre + 1)) by lia;
            repeat cancel).
  all: split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_10_split_goal_1 : zeroOneKnapsack_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_10_split_goal_2 : zeroOneKnapsack_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold KnapsackResultState in PreH8.
  destruct PreH8 as [Hmax _].
  pose proof (KnapsackMaxValue_parameters_nonnegative__dp_refinement_and_exit
    weights_l values_l n_pre capacity_pre
    (Znth (n_pre * width + capacity_pre) dp_l 0) Hmax) as [Hn Hcap].
  nia.
Qed.

Lemma proof_of_zeroOneKnapsack_entail_wit_10 : zeroOneKnapsack_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_zeroOneKnapsack_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_zeroOneKnapsack_entail_wit_10_split_goal_2.
Qed.
