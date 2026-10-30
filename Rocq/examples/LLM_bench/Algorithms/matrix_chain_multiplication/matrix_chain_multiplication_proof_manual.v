From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication Require Import matrix_chain_multiplication_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib.
Local Open Scope sac.
Require Import AUXLib.MonotonicList.

Ltac matrix_math :=
  try solve [assumption | reflexivity];
  repeat rewrite (Forall_Znth (fun value : Z => 0 <= value <= 7000000) 0) in *;
  unfold MatrixChainOptimalCost, MatrixChainTableComplete, MatrixChainSplitMinimum,
    MatrixChainLeftComplete, MatrixChainLengthsComplete in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end];
  try lia;
  repeat match goal with
  | H : Forall ?P ?xs |- _ => rewrite (Forall_Znth P 0 xs) in H
  | |- Forall ?P ?xs => apply (proj2 (Forall_Znth P 0 xs))
  end;
  try solve [assumption | intuition lia];
  try solve [intros; match goal with |- context[Znth ?i ?xs 0] =>
    repeat match goal with H : forall j : Z, _ -> _ |- _ =>
      let K := fresh "AtIndex" in pose proof (H i ltac:(lia)) as K; clear H
    end; lia
  end];
  try nia.

(* Current generated split goals; the witnesses below use the whole-goal route. *)
Lemma proof_of_matrixChainMinCost_entail_wit_1_split_goal_1 : matrixChainMinCost_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_1_split_goal_2 : matrixChainMinCost_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_1_split_goal_spatial : matrixChainMinCost_entail_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 : matrixChainMinCost_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_2_split_goal_2 : matrixChainMinCost_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_4_split_goal_1 : matrixChainMinCost_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 : matrixChainMinCost_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_2 : matrixChainMinCost_entail_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_3 : matrixChainMinCost_entail_wit_5_split_goal_3.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_4 : matrixChainMinCost_entail_wit_5_split_goal_4.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_5 : matrixChainMinCost_entail_wit_5_split_goal_5.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_6 : matrixChainMinCost_entail_wit_5_split_goal_6.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_7 : matrixChainMinCost_entail_wit_5_split_goal_7.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_8 : matrixChainMinCost_entail_wit_5_split_goal_8.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_9 : matrixChainMinCost_entail_wit_5_split_goal_9.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_10 : matrixChainMinCost_entail_wit_5_split_goal_10.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_11 : matrixChainMinCost_entail_wit_5_split_goal_11.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_12 : matrixChainMinCost_entail_wit_5_split_goal_12.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 : matrixChainMinCost_entail_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 : matrixChainMinCost_entail_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 : matrixChainMinCost_entail_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 : matrixChainMinCost_entail_wit_7_split_goal_2.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_3 : matrixChainMinCost_entail_wit_7_split_goal_3.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_4 : matrixChainMinCost_entail_wit_7_split_goal_4.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_5 : matrixChainMinCost_entail_wit_7_split_goal_5.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_6 : matrixChainMinCost_entail_wit_7_split_goal_6.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_7 : matrixChainMinCost_entail_wit_7_split_goal_7.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_8 : matrixChainMinCost_entail_wit_7_split_goal_8.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_9 : matrixChainMinCost_entail_wit_7_split_goal_9.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_10 : matrixChainMinCost_entail_wit_7_split_goal_10.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_11 : matrixChainMinCost_entail_wit_7_split_goal_11.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_12 : matrixChainMinCost_entail_wit_7_split_goal_12.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 : matrixChainMinCost_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 : matrixChainMinCost_entail_wit_8_split_goal_2.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_9_1_split_goal_1 : matrixChainMinCost_entail_wit_9_1_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_9_2_split_goal_1 : matrixChainMinCost_entail_wit_9_2_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_10_split_goal_1 : matrixChainMinCost_entail_wit_10_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_10_split_goal_2 : matrixChainMinCost_entail_wit_10_split_goal_2.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_10_split_goal_3 : matrixChainMinCost_entail_wit_10_split_goal_3.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 : matrixChainMinCost_entail_wit_11_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 : matrixChainMinCost_entail_wit_11_split_goal_2.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 : matrixChainMinCost_entail_wit_11_split_goal_3.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_11_split_goal_4 : matrixChainMinCost_entail_wit_11_split_goal_4.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 : matrixChainMinCost_entail_wit_12_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_13_split_goal_1 : matrixChainMinCost_entail_wit_13_split_goal_1.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_13_split_goal_spatial : matrixChainMinCost_entail_wit_13_split_goal_spatial.
Proof. Abort.

Lemma proof_of_matrixChainMinCost_entail_wit_1 : matrixChainMinCost_entail_wit_1.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext4 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hstep0 : ((Zlength (@nil Z) = 0 /\ Forall (eq 0) (@nil Z)) )).
  {
    split.
    - reflexivity.
    - constructor.
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists (@nil Z).
  sep_apply (IntArray.undef_full_split_to_undef_seg (&("cost"))
    (matrix_count_pre * matrix_count_pre) 64 ltac:(nia)).
  rewrite IntArray.seg_empty.
  split_pure_spatial.
  - try (sep_apply (IntArray.undef_full_split_to_undef_seg (&("cost")) (matrix_count_pre * matrix_count_pre) 64 ltac:(nia))); repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_2 : matrixChainMinCost_entail_wit_2.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext7 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext8 : ((Zlength cost_l_2 = i /\ Forall (eq 0) cost_l_2) )) by matrix_math.
  assert (Hstep0 : ((Zlength (app (cost_l_2) ((cons (0) ((@nil Z))))) = (i + 1 ) /\ Forall (eq 0) (app
    (cost_l_2) ((cons (0) ((@nil Z)))))) )).
  {
    destruct Hcontext8 as [Hlength Hzero].
    split.
    - rewrite Zlength_app, Hlength. reflexivity.
    - apply Forall_app. split; [exact Hzero | repeat constructor].
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists (cost_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_3 : matrixChainMinCost_entail_wit_3.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hi : i = matrix_count_pre * matrix_count_pre) by lia.
  subst i.
  assert (Hzero : (Zlength cost_l_2 = (matrix_count_pre * matrix_count_pre) /\ Forall (eq 0) cost_l_2)) by matrix_math.
  assert (Hdone : (1 <= 2 /\ MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre 2)).
  { apply matrix_chain_zero_table_lengths_done__initialization; assumption. }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists cost_l_2.
  split_pure_spatial.
  - rewrite Hi.
    rewrite IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full (&("cost")) 0
      (matrix_count_pre * matrix_count_pre) cost_l_2).
    replace ((&("cost")) + 0 * sizeof(INT)) with (&("cost")) by lia.
    replace (matrix_count_pre * matrix_count_pre - 0)
      with (matrix_count_pre * matrix_count_pre) by lia.
    cancel.
  - split_pures; dump_pre_spatial;
      try solve [eapply Forall_impl with (P := eq 0);
        [intros x Hx; subst x; lia | eassumption]];
      matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_4 : matrixChainMinCost_entail_wit_4.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext8 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext9 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l_2) )) by matrix_math.
  assert (Hcontext10 : ((1 <= chain_length /\ MatrixChainLengthsComplete dimensions_l cost_l_2
    matrix_count_pre chain_length) )) by matrix_math.
  assert (Hstep0 : ((1 <= chain_length /\ MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre
    chain_length 0) )).
  {
    unfold MatrixChainLeftComplete.
    rewrite <- and_assoc.
    split.
    - exact Hcontext10.
    - intros left right Hleft. lia.
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists cost_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_5 : matrixChainMinCost_entail_wit_5.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext10 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext11 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l_2) )) by matrix_math.
  assert (Hcontext12 : ((1 <= chain_length /\ MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre
    chain_length left) )) by matrix_math.
  assert (Hstep0 : ((Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) <= 100)).
  {
    destruct Hcontext10 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
    lia.
  }
  assert (Hstep1 : (1 <= (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0))).
  {
    destruct Hcontext10 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
    lia.
  }
  assert (Hstep2 : ((Znth (left + 1 ) dimensions_l 0) <= 100)).
  {
    destruct Hcontext10 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound (left + 1) ltac:(lia)).
    lia.
  }
  assert (Hstep3 : (1 <= (Znth (left + 1 ) dimensions_l 0))).
  {
    destruct Hcontext10 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound (left + 1) ltac:(lia)).
    lia.
  }
  assert (Hstep4 : ((Znth left dimensions_l 0) <= 100)).
  {
    destruct Hcontext10 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound left ltac:(lia)).
    lia.
  }
  assert (Hstep5 : (1 <= (Znth left dimensions_l 0))).
  {
    destruct Hcontext10 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound left ltac:(lia)).
    lia.
  }
  assert (Hstep6 : ((Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0) <= 7000000)).
  {
    rewrite (Forall_Znth _ 0 _) in Hcontext11.
    specialize (Hcontext11
      (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1))
      ltac:(rewrite PreH5; nia)).
    lia.
  }
  assert (Hstep7 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0))).
  {
    rewrite (Forall_Znth _ 0 _) in Hcontext11.
    specialize (Hcontext11
      (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1))
      ltac:(rewrite PreH5; nia)).
    lia.
  }
  assert (Hstep8 : ((Znth ((left * matrix_count_pre ) + left ) cost_l_2 0) <= 7000000)).
  {
    rewrite (Forall_Znth _ 0 _) in Hcontext11.
    specialize (Hcontext11 (left * matrix_count_pre + left)
      ltac:(rewrite PreH5; nia)).
    lia.
  }
  assert (Hstep9 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l_2 0))).
  {
    rewrite (Forall_Znth _ 0 _) in Hcontext11.
    specialize (Hcontext11 (left * matrix_count_pre + left)
      ltac:(rewrite PreH5; nia)).
    lia.
  }
  assert (Hstep10 : ((((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre
    * matrix_count_pre ))).
  {
    pose proof (Z.mul_le_mono_nonneg_r (left + 1) (matrix_count_pre - 1)
      matrix_count_pre ltac:(lia) ltac:(lia)) as Hrow.
    rewrite Z.mul_sub_distr_r in Hrow. lia.
  }
  assert (Hstep11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))).
  {
    pose proof (Z.mul_le_mono_nonneg_r left (matrix_count_pre - 1)
      matrix_count_pre ltac:(lia) ltac:(lia)) as Hrow.
    rewrite Z.mul_sub_distr_r in Hrow. lia.
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists cost_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6 : matrixChainMinCost_entail_wit_6.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext32 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext33 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l) )) by matrix_math.
  assert (Hcontext34 : ((1 <= chain_length /\ MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre
    chain_length left) )) by matrix_math.
  assert (Hstep0 : ((1 <= chain_length /\ MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre
    matrix_count_pre chain_length left (left + 1 ) (((Znth ((left * matrix_count_pre ) + left ) cost_l 0) +
    (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left
    dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 )
    dimensions_l 0) ) )) )).
  {
    eapply matrix_chain_split_progress_initial__candidate_progress.
    exact Hcontext34.
  }
  assert (Hstep1 : ((((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) *
    matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth
    (left + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) <=
    7000000)).
  {
    unfold MatrixChainLeftComplete in Hcontext34.
    rewrite <- and_assoc in Hcontext34.
    destruct Hcontext34 as [Hlengths _].
    unfold MatrixChainLengthsComplete in Hlengths.
    destruct Hlengths as [_ Hdone].
    assert (Hleft_minimum :
      MatrixChainIntervalMinimum dimensions_l left left
        (Znth (left * matrix_count_pre + left) cost_l 0)).
    {
      eapply Hdone with (len := 1); lia.
    }
    assert (Hright_minimum :
      MatrixChainIntervalMinimum dimensions_l (left + 1)
        (left + chain_length - 1)
        (Znth ((left + 1) * matrix_count_pre +
               (left + chain_length - 1)) cost_l 0)).
    {
      eapply Hdone with (len := chain_length - 1); lia.
    }
    pose proof
      (matrix_chain_interval_minimum_upper_bound__candidate_progress
         dimensions_l matrix_count_pre left left
         (Znth (left * matrix_count_pre + left) cost_l 0)
         Hcontext32 ltac:(lia) ltac:(lia) ltac:(lia) Hleft_minimum)
      as Hleft_bound.
    pose proof
      (matrix_chain_interval_minimum_upper_bound__candidate_progress
         dimensions_l matrix_count_pre (left + 1)
         (left + chain_length - 1)
         (Znth ((left + 1) * matrix_count_pre +
                (left + chain_length - 1)) cost_l 0)
         Hcontext32 ltac:(lia) ltac:(lia) ltac:(lia) Hright_minimum)
      as Hright_bound.
    assert (Htwo_dimensions :
      Znth left dimensions_l 0 * Znth (left + 1) dimensions_l 0 <= 10000)
      by nia.
    assert (Hlast_lower :
      1 <= Znth ((left + chain_length - 1) + 1) dimensions_l 0).
    {
      replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
      exact PreH30.
    }
    assert (Hlast_upper :
      Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 100).
    {
      replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
      exact PreH31.
    }
    assert (Hproduct_step :
      (Znth left dimensions_l 0 * Znth (left + 1) dimensions_l 0) *
      Znth ((left + chain_length - 1) + 1) dimensions_l 0 <=
      10000 * Znth ((left + chain_length - 1) + 1) dimensions_l 0).
    {
      apply Z.mul_le_mono_nonneg_r; lia.
    }
    assert (Hproduct :
      Znth left dimensions_l 0 * Znth (left + 1) dimensions_l 0 *
      Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 1000000)
      by lia.
    nia.
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists cost_l.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_7 : matrixChainMinCost_entail_wit_7.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext17 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext18 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l_2) )) by matrix_math.
  assert (Hcontext19 : ((1 <= chain_length /\ MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre
    matrix_count_pre chain_length left split best) )) by matrix_math.
  assert (Hstep0 : ((Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) <= 100)).
  {
    destruct Hcontext17 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
    lia.
  }
  assert (Hstep1 : (1 <= (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0))).
  {
    destruct Hcontext17 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
    lia.
  }
  assert (Hstep2 : ((Znth (split + 1 ) dimensions_l 0) <= 100)).
  {
    destruct Hcontext17 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound (split + 1) ltac:(lia)).
    lia.
  }
  assert (Hstep3 : (1 <= (Znth (split + 1 ) dimensions_l 0))).
  {
    destruct Hcontext17 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound (split + 1) ltac:(lia)).
    lia.
  }
  assert (Hstep4 : ((Znth left dimensions_l 0) <= 100)).
  {
    destruct Hcontext17 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound left ltac:(lia)).
    lia.
  }
  assert (Hstep5 : (1 <= (Znth left dimensions_l 0))).
  {
    destruct Hcontext17 as [_ Hbound].
    rewrite (Forall_Znth _ 0 _) in Hbound.
    specialize (Hbound left ltac:(lia)).
    lia.
  }
  assert (Hstep6 : ((Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0) <=
    7000000)).
  {
    rewrite (Forall_Znth _ 0 _) in Hcontext18.
    specialize (Hcontext18
      (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1))
      ltac:(rewrite PreH16; nia)).
    lia.
  }
  assert (Hstep7 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0))).
  {
    rewrite (Forall_Znth _ 0 _) in Hcontext18.
    specialize (Hcontext18
      (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1))
      ltac:(rewrite PreH16; nia)).
    lia.
  }
  assert (Hstep8 : ((Znth ((left * matrix_count_pre ) + split ) cost_l_2 0) <= 7000000)).
  {
    rewrite (Forall_Znth _ 0 _) in Hcontext18.
    specialize (Hcontext18 (left * matrix_count_pre + split)
      ltac:(rewrite PreH16; nia)).
    lia.
  }
  assert (Hstep9 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l_2 0))).
  {
    rewrite (Forall_Znth _ 0 _) in Hcontext18.
    specialize (Hcontext18 (left * matrix_count_pre + split)
      ltac:(rewrite PreH16; nia)).
    lia.
  }
  assert (Hstep10 : ((((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre
    * matrix_count_pre ))).
  {
    pose proof (Z.mul_le_mono_nonneg_r (split + 1) (matrix_count_pre - 1)
      matrix_count_pre ltac:(lia) ltac:(lia)) as Hrow.
    rewrite Z.mul_sub_distr_r in Hrow. lia.
  }
  assert (Hstep11 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))).
  {
    pose proof (Z.mul_le_mono_nonneg_r left (matrix_count_pre - 1)
      matrix_count_pre ltac:(lia) ltac:(lia)) as Hrow.
    rewrite Z.mul_sub_distr_r in Hrow. lia.
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists cost_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8 : matrixChainMinCost_entail_wit_8.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext36 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext37 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l) )) by matrix_math.
  assert (Hcontext38 : ((1 <= chain_length /\ MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre
    matrix_count_pre chain_length left split best) )) by matrix_math.
  assert (Hstep0 : (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left ((left + chain_length
    ) - 1 ) split (((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) *
    matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth
    (split + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) )).
  {
    unfold MatrixChainSplitCandidate. reflexivity.
  }
  assert (Hstep1 : ((((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) *
    matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth
    (split + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) <=
    7000000)).
  {
    unfold MatrixChainSplitMinimum in Hcontext38.
    rewrite <- and_assoc in Hcontext38.
    destruct Hcontext38 as [Hleft_progress _].
    unfold MatrixChainLeftComplete in Hleft_progress.
    rewrite <- and_assoc in Hleft_progress.
    destruct Hleft_progress as [Hlengths _].
    unfold MatrixChainLengthsComplete in Hlengths.
    destruct Hlengths as [_ Hdone].
    assert (Hleft_minimum :
      MatrixChainIntervalMinimum dimensions_l left split
        (Znth (left * matrix_count_pre + split) cost_l 0)).
    {
      eapply Hdone with (len := split - left + 1); lia.
    }
    assert (Hright_minimum :
      MatrixChainIntervalMinimum dimensions_l (split + 1)
        (left + chain_length - 1)
        (Znth ((split + 1) * matrix_count_pre +
               (left + chain_length - 1)) cost_l 0)).
    {
      eapply Hdone with (len := left + chain_length - split - 1); lia.
    }
    pose proof
      (matrix_chain_interval_minimum_upper_bound__candidate_progress
         dimensions_l matrix_count_pre left split
         (Znth (left * matrix_count_pre + split) cost_l 0)
         Hcontext36 ltac:(lia) ltac:(lia) ltac:(lia) Hleft_minimum)
      as Hleft_bound.
    pose proof
      (matrix_chain_interval_minimum_upper_bound__candidate_progress
         dimensions_l matrix_count_pre (split + 1)
         (left + chain_length - 1)
         (Znth ((split + 1) * matrix_count_pre +
                (left + chain_length - 1)) cost_l 0)
         Hcontext36 ltac:(lia) ltac:(lia) ltac:(lia) Hright_minimum)
      as Hright_bound.
    assert (Htwo_dimensions :
      Znth left dimensions_l 0 * Znth (split + 1) dimensions_l 0 <= 10000)
      by nia.
    assert (Hlast_lower :
      1 <= Znth ((left + chain_length - 1) + 1) dimensions_l 0).
    {
      replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
      exact PreH34.
    }
    assert (Hlast_upper :
      Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 100).
    {
      replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
      exact PreH35.
    }
    assert (Hproduct_step :
      (Znth left dimensions_l 0 * Znth (split + 1) dimensions_l 0) *
      Znth ((left + chain_length - 1) + 1) dimensions_l 0 <=
      10000 * Znth ((left + chain_length - 1) + 1) dimensions_l 0).
    {
      apply Z.mul_le_mono_nonneg_r; lia.
    }
    assert (Hproduct :
      Znth left dimensions_l 0 * Znth (split + 1) dimensions_l 0 *
      Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 1000000)
      by lia.
    nia.
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists cost_l.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_9_1 : matrixChainMinCost_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext19 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext20 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l_2) )) by matrix_math.
  assert (Hcontext22 : ((1 <= chain_length /\ MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre
    matrix_count_pre chain_length left split best) )) by matrix_math.
  assert (Hstep0 : ((1 <= chain_length /\ MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre
    matrix_count_pre chain_length left (split + 1 ) candidate) )).
  {
    rewrite PreH8 in PreH24.
    apply (matrix_chain_split_progress_better__min_update
      dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length
      left split best candidate);
      [lia | lia | exact PreH24 | exact Hcontext22].
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists cost_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_9_2 : matrixChainMinCost_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext19 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext20 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l_2) )) by matrix_math.
  assert (Hcontext22 : ((1 <= chain_length /\ MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre
    matrix_count_pre chain_length left split best) )) by matrix_math.
  assert (Hstep0 : ((1 <= chain_length /\ MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre
    matrix_count_pre chain_length left (split + 1 ) best) )).
  {
    rewrite PreH8 in PreH24.
    apply (matrix_chain_split_progress_not_better__min_update
      dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length
      left split best candidate);
      [lia | lia | exact PreH24 | exact Hcontext22].
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists cost_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_10 : matrixChainMinCost_entail_wit_10.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext17 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext18 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l_2) )) by matrix_math.
  assert (Hcontext19 : ((1 <= chain_length /\ MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre
    matrix_count_pre chain_length left split best) )) by matrix_math.
  assert (Hstep0 : (MatrixChainIntervalMinimum dimensions_l left ((left + chain_length ) - 1 ) best )).
  {
    apply (matrix_chain_split_progress_complete__min_update
      dimensions_l cost_l_2 matrix_count_pre chain_length left
      (left + chain_length - 1) best).
    - exact PreH4.
    - exact PreH6.
    - reflexivity.
    - lia.
    - lia.
    - replace (left + chain_length - 1) with split by lia.
      exact Hcontext19.
  }
  assert (Hstep1 : ((1 <= chain_length /\ MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre
    matrix_count_pre chain_length left ((left + chain_length ) - 1 ) best) )).
  {
    replace (left + chain_length - 1) with split by lia.
    exact Hcontext19.
  }
  assert (Hstep2 : (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre *
    matrix_count_pre ))).
  {
    nia.
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists cost_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_11 : matrixChainMinCost_entail_wit_11.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext16 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext17 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l_2) )) by matrix_math.
  assert (Hcontext18 : ((1 <= chain_length /\ MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre
    matrix_count_pre chain_length left right best) )) by matrix_math.
  assert (Hstep0 : ((1 <= chain_length /\ MatrixChainLeftComplete dimensions_l (replace_Znth (((left *
    matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)) matrix_count_pre chain_length
    (left + 1 )) )).
  {
    assert (Hcurrent :
        0 <= left * matrix_count_pre + (left + chain_length - 1) <
             Zlength cost_l_2).
    { rewrite PreH15. rewrite <- PreH7. lia. }
    unfold MatrixChainSplitMinimum in Hcontext18.
    rewrite <- and_assoc in Hcontext18.
    destruct Hcontext18 as [Hprogress _].
    unfold MatrixChainLeftComplete in *.
    rewrite <- and_assoc in Hprogress.
    rewrite <- and_assoc.
    destruct Hprogress as [Hlengths Hleft].
    split.
    - unfold MatrixChainLengthsComplete in *.
      destruct Hlengths as [Hnext Hdone].
      split; [exact Hnext |].
      intros length0 left0 right0 Hlength0 Hright0 Hleft0 Hfits0.
      specialize (Hdone length0 left0 right0 Hlength0 Hright0 Hleft0 Hfits0).
      rewrite Znth_replace_Znth_Diff.
      + exact Hdone.
      + exact Hcurrent.
      + rewrite PreH15. nia.
      + intro Heq.
        assert (Hright0_range : 0 <= right0 < matrix_count_pre) by lia.
        assert (Hright_range :
            0 <= left + chain_length - 1 < matrix_count_pre) by lia.
        destruct (Z.lt_trichotomy left0 left) as [Hlt | [Heql | Hgt]].
        * assert (left0 * matrix_count_pre + right0 <
                  left * matrix_count_pre) by nia.
          nia.
        * subst left0. nia.
        * assert (left * matrix_count_pre + (left + chain_length - 1) <
                  left0 * matrix_count_pre) by nia.
          nia.
    - intros left0 right0 Hleft0 Hright0 Hfits0.
      destruct (Z.eq_dec left0 left) as [Heq | Hneq].
      + subst left0.
        assert (right0 = left + chain_length - 1) by lia.
        subst right0.
        rewrite Znth_replace_Znth_Same by exact Hcurrent.
        replace (left + chain_length - 1) with right by lia.
        exact PreH23.
      + assert (Hleft0_old : 0 <= left0 < left) by lia.
        specialize (Hleft left0 right0 Hleft0_old Hright0 Hfits0).
        rewrite Znth_replace_Znth_Diff.
        * exact Hleft.
        * exact Hcurrent.
        * rewrite PreH15. nia.
        * intro Hindices.
          assert (Hright0_range : 0 <= right0 < matrix_count_pre) by lia.
          assert (Hright_range :
              0 <= left + chain_length - 1 < matrix_count_pre) by lia.
          assert (left0 * matrix_count_pre + right0 <
                  left * matrix_count_pre) by nia.
          nia.
  }
  assert (Hstep1 : ((Forall (fun value : Z => 0 <= value <= 7000000) (replace_Znth (((left * matrix_count_pre
    ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2))) )).
  {
    assert (Hcurrent :
        0 <= left * matrix_count_pre + (left + chain_length - 1) <
             Zlength cost_l_2).
    { rewrite PreH15. rewrite <- PreH7. lia. }
    repeat rewrite (Forall_Znth (fun value : Z => 0 <= value <= 7000000) 0) in *.
    intros index Hindex.
    rewrite Zlength_replace_Znth in Hindex.
    destruct (Z.eq_dec index
        (left * matrix_count_pre + (left + chain_length - 1))) as [Heq | Hneq].
    - subst index.
      rewrite Znth_replace_Znth_Same by exact Hcurrent.
      lia.
    - rewrite Znth_replace_Znth_Diff.
      + apply Hcontext17. exact Hindex.
      + exact Hcurrent.
      + exact Hindex.
      + intro Heq. apply Hneq. symmetry. exact Heq.
  }
  assert (Hstep2 : ((Zlength ((replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) ))
    (best) (cost_l_2)))) = (matrix_count_pre * matrix_count_pre ))).
  {
    rewrite Zlength_replace_Znth.
    exact PreH15.
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists (replace_Znth (left * matrix_count_pre + (left + chain_length - 1)) best cost_l_2).
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_12 : matrixChainMinCost_entail_wit_12.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext10 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext11 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l_2) )) by matrix_math.
  assert (Hcontext12 : ((1 <= chain_length /\ MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre
    chain_length left) )) by matrix_math.
  assert (Hstep0 : ((1 <= (chain_length + 1 ) /\ MatrixChainLengthsComplete dimensions_l cost_l_2
    matrix_count_pre (chain_length + 1 )) )).
  {
    unfold MatrixChainLeftComplete in Hcontext12.
    rewrite <- and_assoc in Hcontext12.
    destruct Hcontext12 as [Hlengths Hleft].
    unfold MatrixChainLengthsComplete in *.
    destruct Hlengths as [Hlengths_lb Hlengths_done].
    split.
    - lia.
    - intros length0 left0 right0 Hlength0 Hright0 Hleft0 Hfits0.
      destruct (Z_lt_ge_dec length0 chain_length) as [Hlt | Hge].
      + eapply Hlengths_done; eauto; lia.
      + assert (length0 = chain_length) by lia.
        subst length0.
        eapply Hleft; eauto; lia.
  }
  try match goal with H : ?r = (?l + ?len - 1) |- _ => rewrite H in * end.
  Exists cost_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_13 : matrixChainMinCost_entail_wit_13.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext8 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ Forall (fun value : Z => 1 <= value <=
    100) dimensions_l) )) by matrix_math.
  assert (Hcontext9 : ((Forall (fun value : Z => 0 <= value <= 7000000) cost_l) )) by matrix_math.
  assert (Hcontext10 : ((1 <= chain_length /\ MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre
    chain_length) )) by matrix_math.
  assert (Hstep0 : ((Zlength dimensions_l = matrix_count_pre + 1 /\ MatrixChainOptimalCost dimensions_l
    matrix_count_pre (Znth (matrix_count_pre - 1 ) cost_l 0)) )).
  {
    assert (Hchain : chain_length = matrix_count_pre + 1) by lia.
    unfold MatrixChainOptimalCost.
    split.
    - exact PreH4.
    - unfold MatrixChainLengthsComplete in Hcontext10.
      destruct Hcontext10 as [_ Hdone].
      eapply Hdone with (len := matrix_count_pre) (left := 0) (right := matrix_count_pre - 1).
      + rewrite Hchain. lia.
      + lia.
      + lia.
      + lia.
  }
  assert (Hstep1 : ((Zlength cost_l = matrix_count_pre * matrix_count_pre /\ MatrixChainTableComplete
    dimensions_l cost_l matrix_count_pre) )).
  {
    assert (Hchain : chain_length = matrix_count_pre + 1) by lia.
    unfold MatrixChainTableComplete.
    split.
    - exact PreH5.
    - intros left0 right0 [Hleft0 [Horder Hright0]].
      unfold MatrixChainLengthsComplete in Hcontext10.
      destruct Hcontext10 as [_ Hdone].
      eapply Hdone with
          (len := right0 - left0 + 1)
          (left := left0) (right := right0).
      + rewrite Hchain. lia.
      + lia.
      + lia.
      + lia.
  }
  assert (Hstep2 : ((1 <= (matrix_count_pre + 1 ) /\ MatrixChainLengthsComplete dimensions_l cost_l
    matrix_count_pre (matrix_count_pre + 1 )) )).
  {
    replace (matrix_count_pre + 1) with chain_length by lia.
    exact Hcontext10.
  }
  assert (Hstep3 : ((Znth (matrix_count_pre - 1 ) cost_l 0) <= 7000000)).
  {
    rewrite (Forall_Znth _ 0 _) in Hcontext9.
    specialize (Hcontext9 (matrix_count_pre - 1)).
    rewrite PreH5 in Hcontext9.
    destruct Hcontext9 as [_ Hupper]; nia.
  }
  assert (Hstep4 : (0 <= (Znth (matrix_count_pre - 1 ) cost_l 0))).
  {
    rewrite (Forall_Znth _ 0 _) in Hcontext9.
    specialize (Hcontext9 (matrix_count_pre - 1)).
    rewrite PreH5 in Hcontext9.
    destruct Hcontext9 as [Hlower _]; nia.
  }
  split_pure_spatial.
  - sep_apply (IntArray.full_to_undef_full (&("cost")) (matrix_count_pre * matrix_count_pre) cost_l).
    sep_apply (IntArray.undef_full_to_undef_seg (&("cost")) (matrix_count_pre * matrix_count_pre)).
    sep_apply (IntArray.undef_seg_merge_to_undef_full (&("cost")) 0
      (matrix_count_pre * matrix_count_pre) 64 ltac:(nia)).
    repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
    cancel.
    apply (store_int_undef_store_int (&("width")) matrix_count_pre).
  - split_pures; dump_pre_spatial; matrix_math.
Qed.
