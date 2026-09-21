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
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.

Require Import AUXLib.MonotonicList.
Ltac sieve_arith :=
  unfold Legacy.ProductIndex, ProductIndex, Legacy.FlagValue, FlagValue in *;
  try rewrite ?Zlength_replace_Znth, ?Zlength_app, ?Zlength_cons, ?Zlength_nil;
  (lia || nia || int_auto).
Ltac sieve_restore :=
  first [assumption | solve [sieve_arith] |
  match goal with
  | |- Legacy.EulerInitPrefix ?n ?next ?flags =>
      apply (proj2 (Modern.init_prefix_facts n next flags)); sieve_restore
  | |- Legacy.EulerOuterState ?n ?next ?tot ?flags ?primes =>
      apply (proj2 (Modern.outer_state_facts n next tot flags primes)); sieve_restore
  | |- Legacy.EulerInnerState ?n ?current ?j ?tot ?flags ?primes =>
      apply (proj2 (Modern.inner_state_facts n current j tot flags primes)); sieve_restore
  | |- Legacy.EulerInnerMarkedState ?n ?current ?j ?tot ?flags ?primes =>
      apply (proj2 (Modern.marked_state_facts n current j tot flags primes)); sieve_restore
  | |- Legacy.EulerSieveResult ?n ?tot ?flags ?primes =>
      apply (proj2 (Modern.sieve_result_facts n tot flags primes)); sieve_restore
  end | (split; sieve_restore)].
Ltac sieve_weaken :=
  match goal with
  | |- Modern.EulerInitPrefix ?n ?next ?flags => apply (Modern.init_prefix_math n next flags)
  | |- Modern.EulerOuterState ?n ?next ?tot ?flags ?primes =>
      apply (Modern.outer_state_math n next tot flags primes)
  | |- Modern.EulerInnerState ?n ?current ?j ?tot ?flags ?primes =>
      apply (Modern.inner_state_math n current j tot flags primes)
  | |- Modern.EulerInnerMarkedState ?n ?current ?j ?tot ?flags ?primes =>
      apply (Modern.marked_state_math n current j tot flags primes)
  | |- Modern.EulerSieveResult ?n ?tot ?flags ?primes =>
      apply (Modern.sieve_result_math n tot flags primes)
  end.
Ltac sieve_finish :=
  first [assumption | solve [tauto] | solve [sieve_arith] | solve [sieve_weaken; assumption] |
  match goal with
  | H : Legacy.EulerInitPrefix ?n ?next ?flags |- _ =>
      let HF := fresh "HF" in pose proof (proj1 (Modern.init_prefix_facts n next flags) H) as HF;
      clear H; decompose [and] HF; sieve_finish
  | H : Legacy.EulerOuterState ?n ?next ?tot ?flags ?primes |- _ =>
      let HF := fresh "HF" in pose proof (proj1 (Modern.outer_state_facts n next tot flags primes) H) as HF;
      clear H; decompose [and] HF; sieve_finish
  | H : Legacy.EulerInnerState ?n ?current ?j ?tot ?flags ?primes |- _ =>
      let HF := fresh "HF" in pose proof (proj1 (Modern.inner_state_facts n current j tot flags primes) H) as HF;
      clear H; decompose [and] HF; sieve_finish
  | H : Legacy.EulerInnerMarkedState ?n ?current ?j ?tot ?flags ?primes |- _ =>
      let HF := fresh "HF" in pose proof (proj1 (Modern.marked_state_facts n current j tot flags primes) H) as HF;
      clear H; decompose [and] HF; sieve_finish
  | H : Legacy.EulerSieveResult ?n ?tot ?flags ?primes |- _ =>
      let HF := fresh "HF" in pose proof (proj1 (Modern.sieve_result_facts n tot flags primes) H) as HF;
      clear H; decompose [and] HF; sieve_finish
  end].


Lemma proof_of_get_prime_entail_wit_1 : get_prime_entail_wit_1.
Proof.
  unfold get_prime_entail_wit_1. right. intros.
  sep_apply (IntArray.undef_full_split_to_undef_seg (&("flag")) (n_pre + 1) 46341); try lia.
  sep_apply (IntArray.undef_seg_split_to_undef_seg (&("flag")) 0 2 (n_pre + 1)); try lia.
  entailer!.
Qed. 

Lemma proof_of_get_prime_entail_wit_2 : get_prime_entail_wit_2.
Proof.
  unfold get_prime_entail_wit_2. right. intros.
  rewrite Zlength_app_cons. entailer!.
Qed. 

Lemma proof_of_get_prime_entail_wit_3 : get_prime_entail_wit_3.
Proof.
  unfold get_prime_entail_wit_3. right. intros.
  assert (z = n_pre + 1) by lia. subst z.
  Exists flag_init.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia.
    sieve_weaken. apply Legacy.EulerInitPrefix_start__core_invariants. lia.
Qed. 

Lemma proof_of_get_prime_entail_wit_4_split_goal_1 : get_prime_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_get_prime_entail_wit_4_split_goal_2 : get_prime_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH7 : (Legacy.EulerInitPrefix n_pre i flag_l_2 )) by sieve_restore.
  sieve_weaken.
  eapply Legacy.EulerInitPrefix_step__core_invariants; eauto; lia.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_4 : get_prime_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_get_prime_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_get_prime_entail_wit_4_split_goal_2.

  all: try sieve_finish.
Qed. 

Lemma proof_of_get_prime_entail_wit_5_split_goal_1 : get_prime_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hinit : Legacy.EulerInitPrefix n_pre i flag_l_2) by sieve_restore.
  sieve_weaken.
  eapply Legacy.EulerInitPrefix_finish_outer__core_invariants; eauto; lia.
Qed.

Lemma proof_of_get_prime_entail_wit_5 : get_prime_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_5_split_goal_1.

  all: try sieve_finish.
Qed. 

Lemma proof_of_get_prime_entail_wit_6_1_split_goal_1 : get_prime_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_get_prime_entail_wit_6_1_split_goal_2 : get_prime_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH9 : (Legacy.EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) by sieve_restore.
  pose proof
    (Legacy.EulerOuterState_self_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 ReusePreH9)
    as [_ Hfirst_upper].
  exact Hfirst_upper.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_6_1_split_goal_3 : get_prime_entail_wit_6_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH9 : (Legacy.EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) by sieve_restore.
  pose proof
    (Legacy.EulerOuterState_self_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 ReusePreH9)
    as [Hfirst_lower _].
  exact Hfirst_lower.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_6_1_split_goal_4 : get_prime_entail_wit_6_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH9 : (Legacy.EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) by sieve_restore.
  sieve_weaken.
  eapply Legacy.EulerOuterState_self_inner_start__core_invariants; eauto; lia.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_6_1 : get_prime_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_get_prime_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_get_prime_entail_wit_6_1_split_goal_2.
  - Goal_apply proof_of_get_prime_entail_wit_6_1_split_goal_3.
  - Goal_apply proof_of_get_prime_entail_wit_6_1_split_goal_4.

  all: try sieve_finish.
Qed. 

Lemma proof_of_get_prime_entail_wit_6_2_split_goal_1 : get_prime_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH9 : (Legacy.EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) by sieve_restore.
  pose proof
    (Legacy.EulerOuterState_nonself_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 ReusePreH9)
    as [_ [_ Hfirst_upper]].
  exact Hfirst_upper.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_6_2_split_goal_2 : get_prime_entail_wit_6_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH9 : (Legacy.EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) by sieve_restore.
  pose proof
    (Legacy.EulerOuterState_nonself_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 ReusePreH9)
    as [_ [Hfirst_lower _]].
  exact Hfirst_lower.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_6_2_split_goal_3 : get_prime_entail_wit_6_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH9 : (Legacy.EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) by sieve_restore.
  sieve_weaken.
  eapply Legacy.EulerOuterState_nonself_inner_start__core_invariants; eauto; lia.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_6_2_split_goal_4 : get_prime_entail_wit_6_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH9 : (Legacy.EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) by sieve_restore.
  pose proof
    (Legacy.EulerOuterState_nonself_first_prime_facts__core_invariants
       n_pre i tot flag_l_2 prime_l_2 PreH1 PreH2 PreH5 ReusePreH9)
    as [Htot_pos _].
  exact Htot_pos.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_6_2_split_goal_5 : get_prime_entail_wit_6_2_split_goal_5.
Proof. exact proof_of_get_prime_entail_wit_6_2_split_goal_4. Qed.

Lemma proof_of_get_prime_entail_wit_6_2 : get_prime_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_get_prime_entail_wit_6_2_split_goal_1.
  - Goal_apply proof_of_get_prime_entail_wit_6_2_split_goal_2.
  - Goal_apply proof_of_get_prime_entail_wit_6_2_split_goal_3.
  - Goal_apply proof_of_get_prime_entail_wit_6_2_split_goal_4.
  - Goal_apply proof_of_get_prime_entail_wit_6_2_split_goal_5.

  all: try sieve_finish.
Qed. 

Lemma proof_of_get_prime_entail_wit_7_split_goal_1 : get_prime_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH11 : (Legacy.EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) by sieve_restore.
  assert (OldPost : (Legacy.EulerInnerMarkedState n_pre i j tot (replace_Znth (((i * (Znth (j - 1 ) prime_l_2 0) ) - 2 )) ((Znth (j - 1 ) prime_l_2 0)) (flag_l_2)) prime_l_2 )).
  {
  eapply (Legacy.EulerInnerState_mark_product__core_invariants
            n_pre i j tot flag_l_2 prime_l_2);
    eauto; unfold Legacy.ProductIndex; eauto; lia.
  }
  sieve_finish.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_7_split_goal_2 : get_prime_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_get_prime_entail_wit_7_split_goal_3 : get_prime_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH11 : (Legacy.EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) by sieve_restore.
  sieve_weaken.
  eapply (Legacy.EulerInnerState_mark_product__core_invariants
            n_pre i j tot flag_l_2 prime_l_2);
    eauto; unfold Legacy.ProductIndex; eauto; lia.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_7 : get_prime_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_get_prime_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_get_prime_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_get_prime_entail_wit_7_split_goal_3.

  all: try sieve_finish.
Qed. 

Lemma proof_of_get_prime_entail_wit_8_split_goal_1 : get_prime_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH11 : (Legacy.EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) by sieve_restore.
  sieve_weaken.
  unfold Legacy.EulerInnerMarkedState in ReusePreH11.
  destruct ReusePreH11 as [_ [_ [_ [_ [_ [Hdivide_exit _]]]]]].
  apply Hdivide_exit.
  rewrite <- Z.rem_divide by lia.
  exact PreH1.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_8 : get_prime_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_get_prime_entail_wit_8_split_goal_1.

  all: try sieve_finish.
Qed. 

Lemma proof_of_get_prime_entail_wit_9_split_goal_1 : get_prime_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH11 : (Legacy.EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) by sieve_restore.
  assert (Hnondivide : ~ Z.divide (Znth (j - 1) prime_l_2 0) i).
  {
    intros Hdivide.
    apply PreH1.
    rewrite Z.rem_divide by lia.
    exact Hdivide.
  }
  unfold Legacy.EulerInnerMarkedState in ReusePreH11.
  destruct ReusePreH11 as [_ [_ [_ [_ [_ [_ Hnondivide_exit]]]]]].
  pose proof (Hnondivide_exit Hnondivide) as Hnext.
  unfold Legacy.EulerInnerState in Hnext.
  destruct Hnext as
    [_ [_ [_ [_ [_ [Hj_next_le [_ [_ [_ [_ [Hbounds_next _]]]]]]]]]]].
  specialize (Hbounds_next (j + 1) ltac:(lia)) as [_ Hupper].
  replace (j + 1 - 1) with j in Hupper by lia.
  exact Hupper.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_9_split_goal_2 : get_prime_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH11 : (Legacy.EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) by sieve_restore.
  assert (Hnondivide : ~ Z.divide (Znth (j - 1) prime_l_2 0) i).
  {
    intros Hdivide.
    apply PreH1.
    rewrite Z.rem_divide by lia.
    exact Hdivide.
  }
  unfold Legacy.EulerInnerMarkedState in ReusePreH11.
  destruct ReusePreH11 as [_ [_ [_ [_ [_ [_ Hnondivide_exit]]]]]].
  pose proof (Hnondivide_exit Hnondivide) as Hnext.
  unfold Legacy.EulerInnerState in Hnext.
  destruct Hnext as
    [_ [_ [_ [_ [_ [Hj_next_le [_ [_ [_ [_ [Hbounds_next _]]]]]]]]]]].
  specialize (Hbounds_next (j + 1) ltac:(lia)) as [Hlower _].
  replace (j + 1 - 1) with j in Hlower by lia.
  exact Hlower.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_9_split_goal_3 : get_prime_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH11 : (Legacy.EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) by sieve_restore.
  sieve_weaken.
  assert (Hnondivide : ~ Z.divide (Znth (j - 1) prime_l_2 0) i).
  {
    intros Hdivide.
    apply PreH1.
    rewrite Z.rem_divide by lia.
    exact Hdivide.
  }
  unfold Legacy.EulerInnerMarkedState in ReusePreH11.
  destruct ReusePreH11 as [_ [_ [_ [_ [_ [_ Hnondivide_exit]]]]]].
  apply Hnondivide_exit.
  exact Hnondivide.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_9_split_goal_4 : get_prime_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH11 : (Legacy.EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) by sieve_restore.
  assert (Hnondivide : ~ Z.divide (Znth (j - 1) prime_l_2 0) i).
  {
    intros Hdivide.
    apply PreH1.
    rewrite Z.rem_divide by lia.
    exact Hdivide.
  }
  unfold Legacy.EulerInnerMarkedState in ReusePreH11.
  destruct ReusePreH11 as [_ [_ [_ [_ [_ [_ Hnondivide_exit]]]]]].
  pose proof (Hnondivide_exit Hnondivide) as Hnext.
  unfold Legacy.EulerInnerState in Hnext.
  destruct Hnext as [_ [_ [_ [_ [_ [Hj_next_le _]]]]]].
  exact Hj_next_le.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_9 : get_prime_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_get_prime_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_get_prime_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_get_prime_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_get_prime_entail_wit_9_split_goal_4.

  all: try sieve_finish.
Qed. 

Lemma proof_of_get_prime_entail_wit_10_split_goal_1 : get_prime_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH9 : (Legacy.EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) by sieve_restore.
  replace (j + 1 - 1) with j by lia.
  exact PreH11.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_10_split_goal_2 : get_prime_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH9 : (Legacy.EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) by sieve_restore.
  replace (j + 1 - 1) with j by lia.
  exact PreH10.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_10 : get_prime_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_get_prime_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_get_prime_entail_wit_10_split_goal_2.

  all: try sieve_finish.
Qed. 

Lemma proof_of_get_prime_entail_wit_11_1_split_goal_1 : get_prime_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (ReusePreH10 : (Legacy.EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) by sieve_restore.
  sieve_weaken.
  unfold Legacy.EulerInnerState in ReusePreH10.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  match goal with
  | H : Legacy.ProductIndex i j prime_l_2 > n_pre ->
        Legacy.EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2 |- _ =>
      unfold Legacy.ProductIndex in H; exact (H PreH1)
  end.

  all: try sieve_finish.
Qed.

Lemma proof_of_get_prime_entail_wit_11_1 : get_prime_entail_wit_11_1.
Proof. aggressive_pre_process. Goal_apply proof_of_get_prime_entail_wit_11_1_split_goal_1. Qed. 

Lemma proof_of_get_prime_entail_wit_12 : get_prime_entail_wit_12.
Proof.
  unfold get_prime_entail_wit_12. right. intros.
  replace i with (n_pre + 1) in * by lia.
  assert (Hres : EulerSieveResult n_pre tot flag_l prime_l).
  {
    assert (Houter : Legacy.EulerOuterState n_pre (n_pre + 1) tot flag_l prime_l) by sieve_restore.
    sieve_weaken.
  unfold Legacy.EulerOuterState in Houter.
  destruct Houter as [Hflag Hrest].
  destruct Hrest as [Hprime_len Hrest].
  destruct Hrest as [Hnext_low Hrest].
  destruct Hrest as [Hnext_high Hrest].
  destruct Hrest as [Htot_nonneg Hrest].
  destruct Hrest as [Htot_lt Hrest].
  destruct Hrest as [Hprime_prefix Hbounds].
  unfold Legacy.EulerFlagState in Hflag.
  destruct Hflag as [Hflag_len Hflag_entries].
  unfold Legacy.EulerSieveResult.
  split; [exact Hflag_len |].
  split; [exact Hprime_len |].
  split; [exact Htot_nonneg |].
  split; [lia |].
  split.
  - unfold Legacy.LeastPrimeFlagList.
    split; [exact Hflag_len |].
    intros k Hk.
    unfold Legacy.FlagValue.
    destruct (Hflag_entries k Hk) as [Hknown _].
    apply Hknown; lia.
  - replace (n_pre + 1 - 1) with n_pre in Hprime_prefix by lia.
    exact Hprime_prefix.


  }
  Exists flag_l.
  sep_apply (IntArray.seg_to_undef_seg (&("flag")) 2 (n_pre + 1) flag_l).
  sep_apply (IntArray.undef_seg_merge_to_undef_seg (&("flag")) 0 2 (n_pre + 1)); try lia.
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&("flag")) 0 (n_pre + 1) 46341); try lia.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
  entailer!.
Qed. 

Lemma proof_of_get_prime_return_wit_1 : get_prime_return_wit_1.
Proof.
  unfold get_prime_return_wit_1. right. intros. Exists tot.
  pose proof (proj2 PreH3) as Hprime. entailer!.
Qed. 

