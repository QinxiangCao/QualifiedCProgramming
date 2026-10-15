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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P068_21C_stripe_2_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P068_21C_stripe_2_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P068_21C_stripe_2_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia);
  unfold PrefixSum;
  rewrite Zsublist_nil by lia;
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | Hbound : (forall z : Z, 0 <= z /\ z < ?n -> _),
    Hk : (0 <= ?k0 /\ ?k0 < ?n) |- _ =>
      first [exact (Hbound k0 Hk) | fail 100 "MISMATCH" Hbound k0 Hk]
  end.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (PreH5 i (conj PreH6 PreH1)) as [Ha _].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (PrefixSum_succ__prefix_sum_core values i) by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Htot : total = PrefixSum values n_pre) by exact PreH9.
  unfold Spec.
  rewrite PreH5.
  symmetry.
  apply set_card_empty__zero_spec_final.
  intros q Hmember.
  cbn zeta in Hmember.
  destruct Hmember as [Hq [[Hi0 Hij] [Hjn [Heq1 Heq2]]]].
  pose proof (sublist_sum_as_prefix_diff__zero_spec_final values 0 (q / n_pre)
    ltac:(lia) ltac:(lia) ltac:(rewrite PreH5; lia)) as Hd1.
  pose proof (sublist_sum_as_prefix_diff__zero_spec_final values (q / n_pre) (q mod n_pre)
    ltac:(lia) ltac:(lia) ltac:(rewrite PreH5; lia)) as Hd2.
  pose proof (sublist_sum_as_prefix_diff__zero_spec_final values (q mod n_pre) n_pre
    ltac:(lia) ltac:(lia) ltac:(rewrite PreH5; lia)) as Hd3.
  assert (H0 : PrefixSum values 0 = 0).
  { unfold PrefixSum. rewrite Zsublist_nil by lia. reflexivity. }
  rewrite Hd1 in Heq1.
  rewrite Hd2 in Heq1, Heq2.
  rewrite Hd3 in Heq2.
  rewrite H0 in Heq1.
  assert (Htotal3 : total = 3 * PrefixSum values (q / n_pre)) by lia.
  apply PreH1.
  rewrite Htotal3.
  rewrite Z.mul_comm.
  apply Z.rem_mul.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia.
  rewrite <- Hi.
  exact PreH9.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6; assumption.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia);
  unfold ValidPairCount, sum_range;
  symmetry;
  apply sum_Z_range_empty; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia);
  symmetry;
  apply FirstCutCount_zero__prefix_sum_core.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia);
  unfold PrefixSum;
  rewrite Zsublist_nil by lia;
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_5 : solver_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (Z.quot_rem' total 3) as Hqr.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_6 : solver_entail_wit_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hi : i = n_pre) by lia.
  rewrite <- Hi.
  exact PreH9.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_7 : solver_entail_wit_4_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  match goal with
  | Hbound : (forall z : Z, 0 <= z /\ z < ?n -> _),
    Hk : (0 <= ?k0 /\ ?k0 < ?n) |- _ =>
      exact (Hbound k0 Hk)
  end.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hps : PrefixSum values (i + 1) = 2 * third).
  { rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
    rewrite <- PreH15. exact PreH2. }
  rewrite PreH17, PreH16.
  rewrite (ValidPairCount_succ_true__loop_step_transitions values third i) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hps : PrefixSum values (i + 1) = third).
  { rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
    rewrite <- PreH15. exact PreH1. }
  rewrite PreH16.
  rewrite (FirstCutCount_succ_true__loop_step_transitions values third i) by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_3 : solver_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
  rewrite <- PreH15. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH7 i ltac:(lia)) as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_2 : solver_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH7 i ltac:(lia)) as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_3 : solver_entail_wit_5_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi0 : i = 0) by lia.
  subst i.
  rewrite PreH16.
  destruct (Z.eq_dec (PrefixSum values (0 + 1)) (2 * third)) as [Heq | Hneq].
  - rewrite (ValidPairCount_succ_true__loop_step_transitions values third 0) by lia.
    rewrite (FirstCutCount_zero__loop_step_transitions values third).
    lia.
  - rewrite (ValidPairCount_succ_false__loop_step_transitions values third 0) by lia.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_4 : solver_entail_wit_5_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hps : PrefixSum values (i + 1) = third).
  { rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
    rewrite <- PreH14. exact PreH1. }
  rewrite PreH15.
  rewrite (FirstCutCount_succ_true__loop_step_transitions values third i) by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_5 : solver_entail_wit_5_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
  rewrite <- PreH14. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_1 : solver_entail_wit_5_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH8 i ltac:(lia)) as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_2 : solver_entail_wit_5_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH8 i ltac:(lia)) as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_3 : solver_entail_wit_5_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hne : PrefixSum values (i + 1) <> 2 * third).
  { rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
    rewrite <- PreH15. exact PreH2. }
  rewrite PreH17.
  rewrite (ValidPairCount_succ_false__loop_step_transitions values third i) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_4 : solver_entail_wit_5_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hps : PrefixSum values (i + 1) = third).
  { rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
    rewrite <- PreH15. exact PreH1. }
  rewrite PreH16.
  rewrite (FirstCutCount_succ_true__loop_step_transitions values third i) by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_5 : solver_entail_wit_5_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
  rewrite <- PreH15. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_3_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_3_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_1 : solver_entail_wit_5_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH8 i ltac:(lia)) as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_2 : solver_entail_wit_5_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH8 i ltac:(lia)) as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_3 : solver_entail_wit_5_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Heq2 : PrefixSum values (i + 1) = 2 * third).
  { rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
    rewrite <- PreH15. exact PreH2. }
  rewrite PreH16, PreH17.
  rewrite (ValidPairCount_succ_true__loop_step_transitions values third i) by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_4 : solver_entail_wit_5_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hne : PrefixSum values (i + 1) <> third).
  { rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
    rewrite <- PreH15. exact PreH1. }
  rewrite PreH16.
  rewrite (FirstCutCount_succ_false__loop_step_transitions values third i) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_5 : solver_entail_wit_5_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
  rewrite <- PreH15. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_4_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_5_5_split_goal_1 : solver_entail_wit_5_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi0 : i = 0) by lia.
  subst i.
  rewrite PreH16.
  destruct (Z.eq_dec (PrefixSum values (0 + 1)) (2 * third)) as [Heq | Hneq].
  - rewrite (ValidPairCount_succ_true__loop_step_transitions values third 0) by lia.
    rewrite (FirstCutCount_zero__loop_step_transitions values third).
    lia.
  - rewrite (ValidPairCount_succ_false__loop_step_transitions values third 0) by lia.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_5_split_goal_2 : solver_entail_wit_5_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hne : PrefixSum values (i + 1) <> third).
  { rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
    rewrite <- PreH14. exact PreH1. }
  rewrite PreH15.
  rewrite (FirstCutCount_succ_false__loop_step_transitions values third i) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_5_split_goal_3 : solver_entail_wit_5_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
  rewrite <- PreH14. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_5_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_6_split_goal_1 : solver_entail_wit_5_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH8 i ltac:(lia)) as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_6_split_goal_2 : solver_entail_wit_5_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hne : PrefixSum values (i + 1) <> 2 * third).
  { rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
    rewrite <- PreH15. exact PreH2. }
  rewrite PreH17.
  rewrite (ValidPairCount_succ_false__loop_step_transitions values third i) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_6_split_goal_3 : solver_entail_wit_5_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hne : PrefixSum values (i + 1) <> third).
  { rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
    rewrite <- PreH15. exact PreH1. }
  rewrite PreH16.
  rewrite (FirstCutCount_succ_false__loop_step_transitions values third i) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_6_split_goal_4 : solver_entail_wit_5_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (PrefixSum_succ__loop_step_transitions values i) by lia.
  rewrite <- PreH15. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_5_6 : solver_entail_wit_5_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_6_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_6_split_goal_4.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre - 1) by lia.
  subst i.
  unfold Spec.
  cbv zeta.
  rewrite PreH4.
  rewrite PreH14.
  rewrite (valid_pair_count_iff_spec__zero_spec_final values third n_pre
    (eq_sym PreH4) ltac:(lia)).
  apply set_card_ext__zero_spec_final.
  intros q.
  assert (H0 : PrefixSum values 0 = 0).
  { unfold PrefixSum. rewrite Zsublist_nil by lia. reflexivity. }
  split.
  - intros [Hq [Hi0 [Hij [Hjn [Hk Hj]]]]].
    pose proof (sublist_sum_as_prefix_diff__zero_spec_final values 0 (q / n_pre)
      ltac:(lia) ltac:(lia) ltac:(rewrite PreH4; lia)) as Hd1.
    pose proof (sublist_sum_as_prefix_diff__zero_spec_final values (q / n_pre) (q mod n_pre)
      ltac:(lia) ltac:(lia) ltac:(rewrite PreH4; lia)) as Hd2.
    pose proof (sublist_sum_as_prefix_diff__zero_spec_final values (q mod n_pre) n_pre
      ltac:(lia) ltac:(lia) ltac:(rewrite PreH4; lia)) as Hd3.
    repeat split; try lia.
  - intros [Hq [[Hi0 Hij] [Hjn [Heq1 Heq2]]]].
    pose proof (sublist_sum_as_prefix_diff__zero_spec_final values 0 (q / n_pre)
      ltac:(lia) ltac:(lia) ltac:(rewrite PreH4; lia)) as Hd1.
    pose proof (sublist_sum_as_prefix_diff__zero_spec_final values (q / n_pre) (q mod n_pre)
      ltac:(lia) ltac:(lia) ltac:(rewrite PreH4; lia)) as Hd2.
    pose proof (sublist_sum_as_prefix_diff__zero_spec_final values (q mod n_pre) n_pre
      ltac:(lia) ltac:(lia) ltac:(rewrite PreH4; lia)) as Hd3.
    rewrite Hd1, H0 in Heq1.
    rewrite Hd2 in Heq1, Heq2.
    rewrite Hd3 in Heq2.
    rewrite <- PreH6, PreH7 in Heq2.
    repeat split; try lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

