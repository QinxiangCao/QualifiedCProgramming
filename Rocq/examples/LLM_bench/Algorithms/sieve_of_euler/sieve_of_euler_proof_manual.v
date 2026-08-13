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
From SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler Require Import sieve_of_euler_goal.
From SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler Require Import sieve_of_euler_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_lib.
Local Open Scope sac.

Lemma proof_of_get_prime_entail_wit_1_split_goal_1 : get_prime_entail_wit_1_split_goal_1.
Proof.
  unfold get_prime_entail_wit_1_split_goal_1.
  intros.
  apply EulerInitPrefix_start__core_invariants.
  exact PreH3.
Qed.

Lemma proof_of_get_prime_entail_wit_1 : get_prime_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_get_prime_entail_wit_2_split_goal_1 : get_prime_entail_wit_2_split_goal_1.
Proof.
  unfold get_prime_entail_wit_2_split_goal_1.
  intros.
  eapply EulerInitPrefix_step__core_invariants; eauto; lia.
Qed.

Lemma proof_of_get_prime_entail_wit_2 : get_prime_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_get_prime_entail_wit_3_split_goal_1 : get_prime_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_get_prime_entail_wit_3 : get_prime_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst tot.
  prop_apply (IntArray.seg_Zlength prime_pre 1 (n_pre + 1) prime0).
  Intros_p Hprime_len.
  Exists flag_l_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
  eapply (EulerInitPrefix_finish_outer__core_invariants n_pre i flag_l_2 prime0);
    eauto; try lia.
Qed.

Lemma proof_of_get_prime_entail_wit_5_1_split_goal_1 : get_prime_entail_wit_5_1_split_goal_1.
Proof.
  unfold get_prime_entail_wit_5_1_split_goal_1.
  intros.
  pose proof
    (EulerOuterState_self_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
    as [_ Hfirst_upper].
  assert
    (i * Znth 0 (replace_Znth (tot + 1 - 1) i prime_l_2) 0
      <= 46340 * 46340) by nia.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_get_prime_entail_wit_5_1_split_goal_2 : get_prime_entail_wit_5_1_split_goal_2.
Proof.
  unfold get_prime_entail_wit_5_1_split_goal_2.
  intros.
  pose proof
    (EulerOuterState_self_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
    as [_ Hfirst_upper].
  exact Hfirst_upper.
Qed.

Lemma proof_of_get_prime_entail_wit_5_1_split_goal_3 : get_prime_entail_wit_5_1_split_goal_3.
Proof.
  unfold get_prime_entail_wit_5_1_split_goal_3.
  intros.
  pose proof
    (EulerOuterState_self_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
    as [Hfirst_lower _].
  exact Hfirst_lower.
Qed.

Lemma proof_of_get_prime_entail_wit_5_1_split_goal_4 : get_prime_entail_wit_5_1_split_goal_4.
Proof.
  unfold get_prime_entail_wit_5_1_split_goal_4.
  intros.
  eapply EulerOuterState_self_inner_start__core_invariants; eauto; lia.
Qed.

Lemma proof_of_get_prime_entail_wit_5_1 : get_prime_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_5_1_split_goal_1.
  Goal_apply proof_of_get_prime_entail_wit_5_1_split_goal_2.
  Goal_apply proof_of_get_prime_entail_wit_5_1_split_goal_3.
  Goal_apply proof_of_get_prime_entail_wit_5_1_split_goal_4.
Qed.

Lemma proof_of_get_prime_entail_wit_5_2_split_goal_1 : get_prime_entail_wit_5_2_split_goal_1.
Proof.
  unfold get_prime_entail_wit_5_2_split_goal_1.
  intros.
  pose proof
    (EulerOuterState_nonself_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
    as [_ [_ Hfirst_upper]].
  assert (i * Znth 0 prime_l_2 0 <= 46340 * 46340) by nia.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_get_prime_entail_wit_5_2_split_goal_2 : get_prime_entail_wit_5_2_split_goal_2.
Proof.
  unfold get_prime_entail_wit_5_2_split_goal_2.
  intros.
  pose proof
    (EulerOuterState_nonself_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
    as [_ [_ Hfirst_upper]].
  exact Hfirst_upper.
Qed.

Lemma proof_of_get_prime_entail_wit_5_2_split_goal_3 : get_prime_entail_wit_5_2_split_goal_3.
Proof.
  unfold get_prime_entail_wit_5_2_split_goal_3.
  intros.
  pose proof
    (EulerOuterState_nonself_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
    as [_ [Hfirst_lower _]].
  exact Hfirst_lower.
Qed.

Lemma proof_of_get_prime_entail_wit_5_2_split_goal_4 : get_prime_entail_wit_5_2_split_goal_4.
Proof.
  unfold get_prime_entail_wit_5_2_split_goal_4.
  intros.
  eapply EulerOuterState_nonself_inner_start__core_invariants; eauto; lia.
Qed.

Lemma proof_of_get_prime_entail_wit_5_2_split_goal_5 : get_prime_entail_wit_5_2_split_goal_5.
Proof.
  unfold get_prime_entail_wit_5_2_split_goal_5.
  intros.
  pose proof
    (EulerOuterState_nonself_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 PreH9)
    as [Htot_pos _].
  exact Htot_pos.
Qed.

Lemma proof_of_get_prime_entail_wit_5_2 : get_prime_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_5_2_split_goal_1.
  Goal_apply proof_of_get_prime_entail_wit_5_2_split_goal_2.
  Goal_apply proof_of_get_prime_entail_wit_5_2_split_goal_3.
  Goal_apply proof_of_get_prime_entail_wit_5_2_split_goal_4.
  Goal_apply proof_of_get_prime_entail_wit_5_2_split_goal_5.
Qed.

Lemma proof_of_get_prime_entail_wit_7_split_goal_1 : get_prime_entail_wit_7_split_goal_1.
Proof.
  unfold get_prime_entail_wit_7_split_goal_1.
  intros.
  eapply (EulerInnerState_mark_product__core_invariants
            n_pre i j tot flag_l_2 prime_l_2);
    eauto; unfold ProductIndex; eauto; lia.
Qed.

Lemma proof_of_get_prime_entail_wit_7 : get_prime_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_get_prime_entail_wit_8_split_goal_1 : get_prime_entail_wit_8_split_goal_1.
Proof.
  unfold get_prime_entail_wit_8_split_goal_1.
  intros.
  unfold EulerInnerMarkedState in PreH11.
  destruct PreH11 as [_ [_ [_ [_ [_ [Hdivide_exit _]]]]]].
  apply Hdivide_exit.
  rewrite <- Z.rem_divide by lia.
  exact PreH1.
Qed.

Lemma proof_of_get_prime_entail_wit_8 : get_prime_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_8_split_goal_1.
Qed.

Lemma proof_of_get_prime_entail_wit_9_split_goal_1 : get_prime_entail_wit_9_split_goal_1.
Proof.
  unfold get_prime_entail_wit_9_split_goal_1.
  intros.
  assert (Hnondivide : ~ Z.divide (Znth (j - 1) prime_l_2 0) i).
  {
    intros Hdivide.
    apply PreH1.
    rewrite Z.rem_divide by lia.
    exact Hdivide.
  }
  unfold EulerInnerMarkedState in PreH11.
  destruct PreH11 as [_ [_ [_ [_ [_ [_ Hnondivide_exit]]]]]].
  pose proof (Hnondivide_exit Hnondivide) as Hnext.
  unfold EulerInnerState in Hnext.
  destruct Hnext as
    [_ [_ [_ [_ [_ [Hj_next_le [_ [_ [_ [_ [Hbounds_next _]]]]]]]]]]].
  specialize (Hbounds_next (j + 1) ltac:(lia)) as [_ Hupper].
  replace (j + 1 - 1) with j in Hupper by lia.
  assert (i * Znth j prime_l_2 0 <= 46340 * 46340) by nia.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_get_prime_entail_wit_9_split_goal_2 : get_prime_entail_wit_9_split_goal_2.
Proof.
  unfold get_prime_entail_wit_9_split_goal_2.
  intros.
  assert (Hnondivide : ~ Z.divide (Znth (j - 1) prime_l_2 0) i).
  {
    intros Hdivide.
    apply PreH1.
    rewrite Z.rem_divide by lia.
    exact Hdivide.
  }
  unfold EulerInnerMarkedState in PreH11.
  destruct PreH11 as [_ [_ [_ [_ [_ [_ Hnondivide_exit]]]]]].
  pose proof (Hnondivide_exit Hnondivide) as Hnext.
  unfold EulerInnerState in Hnext.
  destruct Hnext as
    [_ [_ [_ [_ [_ [Hj_next_le [_ [_ [_ [_ [Hbounds_next _]]]]]]]]]]].
  specialize (Hbounds_next (j + 1) ltac:(lia)) as [_ Hupper].
  replace (j + 1 - 1) with j in Hupper by lia.
  exact Hupper.
Qed.

Lemma proof_of_get_prime_entail_wit_9_split_goal_3 : get_prime_entail_wit_9_split_goal_3.
Proof.
  unfold get_prime_entail_wit_9_split_goal_3.
  intros.
  assert (Hnondivide : ~ Z.divide (Znth (j - 1) prime_l_2 0) i).
  {
    intros Hdivide.
    apply PreH1.
    rewrite Z.rem_divide by lia.
    exact Hdivide.
  }
  unfold EulerInnerMarkedState in PreH11.
  destruct PreH11 as [_ [_ [_ [_ [_ [_ Hnondivide_exit]]]]]].
  pose proof (Hnondivide_exit Hnondivide) as Hnext.
  unfold EulerInnerState in Hnext.
  destruct Hnext as
    [_ [_ [_ [_ [_ [Hj_next_le [_ [_ [_ [_ [Hbounds_next _]]]]]]]]]]].
  specialize (Hbounds_next (j + 1) ltac:(lia)) as [Hlower _].
  replace (j + 1 - 1) with j in Hlower by lia.
  exact Hlower.
Qed.

Lemma proof_of_get_prime_entail_wit_9_split_goal_4 : get_prime_entail_wit_9_split_goal_4.
Proof.
  unfold get_prime_entail_wit_9_split_goal_4.
  intros.
  assert (Hnondivide : ~ Z.divide (Znth (j - 1) prime_l_2 0) i).
  {
    intros Hdivide.
    apply PreH1.
    rewrite Z.rem_divide by lia.
    exact Hdivide.
  }
  unfold EulerInnerMarkedState in PreH11.
  destruct PreH11 as [_ [_ [_ [_ [_ [_ Hnondivide_exit]]]]]].
  apply Hnondivide_exit.
  exact Hnondivide.
Qed.

Lemma proof_of_get_prime_entail_wit_9_split_goal_5 : get_prime_entail_wit_9_split_goal_5.
Proof.
  unfold get_prime_entail_wit_9_split_goal_5.
  intros.
  assert (Hnondivide : ~ Z.divide (Znth (j - 1) prime_l_2 0) i).
  {
    intros Hdivide.
    apply PreH1.
    rewrite Z.rem_divide by lia.
    exact Hdivide.
  }
  unfold EulerInnerMarkedState in PreH11.
  destruct PreH11 as [_ [_ [_ [_ [_ [_ Hnondivide_exit]]]]]].
  pose proof (Hnondivide_exit Hnondivide) as Hnext.
  unfold EulerInnerState in Hnext.
  destruct Hnext as [_ [_ [_ [_ [_ [Hj_next_le _]]]]]].
  exact Hj_next_le.
Qed.

Lemma proof_of_get_prime_entail_wit_9 : get_prime_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_9_split_goal_1.
  Goal_apply proof_of_get_prime_entail_wit_9_split_goal_2.
  Goal_apply proof_of_get_prime_entail_wit_9_split_goal_3.
  Goal_apply proof_of_get_prime_entail_wit_9_split_goal_4.
  Goal_apply proof_of_get_prime_entail_wit_9_split_goal_5.
Qed.

Lemma proof_of_get_prime_entail_wit_10_split_goal_1 : get_prime_entail_wit_10_split_goal_1.
Proof.
  unfold get_prime_entail_wit_10_split_goal_1.
  intros.
  replace (j + 1 - 1) with j by lia.
  exact PreH12.
Qed.

Lemma proof_of_get_prime_entail_wit_10_split_goal_2 : get_prime_entail_wit_10_split_goal_2.
Proof.
  unfold get_prime_entail_wit_10_split_goal_2.
  intros.
  replace (j + 1 - 1) with j by lia.
  exact PreH11.
Qed.

Lemma proof_of_get_prime_entail_wit_10_split_goal_3 : get_prime_entail_wit_10_split_goal_3.
Proof.
  unfold get_prime_entail_wit_10_split_goal_3.
  intros.
  replace (j + 1 - 1) with j by lia.
  exact PreH10.
Qed.

Lemma proof_of_get_prime_entail_wit_10 : get_prime_entail_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_10_split_goal_1.
  Goal_apply proof_of_get_prime_entail_wit_10_split_goal_2.
  Goal_apply proof_of_get_prime_entail_wit_10_split_goal_3.
Qed.

Lemma proof_of_get_prime_entail_wit_11_1_split_goal_1 : get_prime_entail_wit_11_1_split_goal_1.
Proof.
  unfold get_prime_entail_wit_11_1_split_goal_1.
  intros.
  unfold EulerInnerState in PreH10.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  match goal with
  | H : ProductIndex i j prime_l_2 > n_pre ->
        EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2 |- _ =>
      unfold ProductIndex in H; exact (H PreH1)
  end.
Qed.

Lemma proof_of_get_prime_entail_wit_11_1_split_goal_2 : get_prime_entail_wit_11_1_split_goal_2.
Proof.
  unfold get_prime_entail_wit_11_1_split_goal_2.
  intros.
  unfold EulerInnerState in PreH10.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  assumption.
Qed.

Lemma proof_of_get_prime_entail_wit_11_1 : get_prime_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_11_1_split_goal_1.
  Goal_apply proof_of_get_prime_entail_wit_11_1_split_goal_2.
Qed.

Lemma proof_of_get_prime_entail_wit_11_2_split_goal_1 : get_prime_entail_wit_11_2_split_goal_1.
Proof.
  unfold get_prime_entail_wit_11_2_split_goal_1.
  intros.
  unfold EulerOuterState in PreH11.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  assumption.
Qed.

Lemma proof_of_get_prime_entail_wit_11_2 : get_prime_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_11_2_split_goal_1.
Qed.

Lemma proof_of_get_prime_entail_wit_13_split_goal_1 : get_prime_entail_wit_13_split_goal_1.
Proof.
  unfold get_prime_entail_wit_13_split_goal_1.
  intros.
  replace (n_pre + 1) with i by lia.
  exact PreH8.
Qed.

Lemma proof_of_get_prime_entail_wit_13 : get_prime_entail_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_13_split_goal_1.
Qed.

Lemma proof_of_get_prime_which_implies_wit_1_split_goal_1 : get_prime_which_implies_wit_1_split_goal_1.
Proof.
  unfold get_prime_which_implies_wit_1_split_goal_1.
  intros.
  unfold EulerOuterState in PreH5.
  destruct PreH5 as [Hflag Hrest].
  destruct Hrest as [Hprime_len Hrest].
  destruct Hrest as [Hnext_low Hrest].
  destruct Hrest as [Hnext_high Hrest].
  destruct Hrest as [Htot_nonneg Hrest].
  destruct Hrest as [Htot_lt Hrest].
  destruct Hrest as [Hprime_prefix Hbounds].
  unfold EulerFlagState in Hflag.
  destruct Hflag as [Hflag_len Hflag_entries].
  unfold EulerSieveResult.
  split; [exact Hflag_len |].
  split; [exact Hprime_len |].
  split; [exact Htot_nonneg |].
  split; [lia |].
  split.
  - unfold LeastPrimeFlagList.
    split; [exact Hflag_len |].
    intros k Hk.
    unfold FlagValue.
    destruct (Hflag_entries k Hk) as [Hknown _].
    apply Hknown; lia.
  - replace (n_pre + 1 - 1) with n_pre in Hprime_prefix by lia.
    exact Hprime_prefix.
Qed.

Lemma proof_of_get_prime_which_implies_wit_1 : get_prime_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_which_implies_wit_1_split_goal_1.
Qed.
