Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.maximum_subarray Require Import maximum_subarray_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib.
Local Open Scope sac.

Lemma proof_of_max_return_wit_2 : max_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    dump_pre_spatial.
    unfold max_Z.
    rewrite Z.max_r by lia.
    reflexivity.
Qed. 

Lemma proof_of_max_return_wit_1 : max_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    dump_pre_spatial.
    unfold max_Z.
    rewrite Z.max_l by lia.
    reflexivity.
Qed. 

Lemma proof_of_max_sub_array_entail_wit_1 : max_sub_array_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption;
      try (apply MaxSuffixSumPrefix_single; lia);
      try (apply MaxSubarraySumPrefix_single; lia);
      try match goal with
      | H : forall k : Z, _ |- _ =>
          specialize (H 0 ltac:(lia)); lia
      end.
Qed. 

Lemma proof_of_max_sub_array_entail_wit_2_split_goal_1 : max_sub_array_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply PreH12.
  exact H.
Qed.

Lemma proof_of_max_sub_array_entail_wit_2 : max_sub_array_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_max_sub_array_entail_wit_3 : max_sub_array_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption;
      try match goal with
      | H : forall k : Z, _ |- _ =>
          specialize (H i ltac:(lia)); lia
      end.
Qed. 

Lemma proof_of_max_sub_array_entail_wit_4 : max_sub_array_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption;
      try (subst retval;
           apply MaxSuffixSumPrefix_step; try lia; assumption);
      try (subst retval;
           unfold max_Z;
           pose proof (Z.le_max_l (Znth i l 0) (cur + Znth i l 0));
           match goal with
           | H : forall k : Z, _ |- _ =>
               specialize (H i ltac:(lia)); lia
           end);
      try (subst retval;
           eapply MaxSuffixSumPrefix_upper_bound with (n := n_pre);
           try lia;
           [ | intros k Hk;
               match goal with
               | H : forall k0 : Z, _ |- _ =>
                   specialize (H k ltac:(lia)); lia
               end
             | apply MaxSuffixSumPrefix_step; try lia; assumption ]).
    subst retval.
    eapply (MaxSuffixSumPrefix_upper_bound
              l (i + 1) (max_Z (Znth i l 0) (cur + Znth i l 0)) n_pre).
    + lia.
    + lia.
    + lia.
    + intros k Hk.
      match goal with
      | H : forall k0 : Z, _ |- _ =>
          specialize (H k ltac:(lia)); lia
      end.
    + apply MaxSuffixSumPrefix_step; try lia; assumption.
Qed. 

Lemma proof_of_max_sub_array_entail_wit_5 : max_sub_array_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures;
      dump_pre_spatial;
      try lia;
      try assumption;
      try (subst retval;
           apply MaxSubarraySumPrefix_step; assumption);
      try (subst retval;
           unfold max_Z;
           pose proof (Z.le_max_l res cur); lia);
      try (subst retval;
           unfold max_Z;
           apply Z.max_lub; lia).
Qed. 

Lemma proof_of_max_sub_array_entail_wit_6_split_goal_1 : max_sub_array_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply PreH12.
  exact H.
Qed.

Lemma proof_of_max_sub_array_entail_wit_6 : max_sub_array_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_max_sub_array_entail_wit_7 : max_sub_array_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial;
      try lia;
      try (assert (i = n_pre) by lia; subst i; assumption).
Qed. 
