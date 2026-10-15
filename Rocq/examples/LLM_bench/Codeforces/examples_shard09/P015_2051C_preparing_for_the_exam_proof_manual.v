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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P015_2051C_preparing_for_the_exam_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P015_2051C_preparing_for_the_exam_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P015_2051C_preparing_for_the_exam_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold UnknownPrefixSummary.
  split; [lia |].
  left.
  split; [reflexivity |].
  intros x Hx.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (unknown_prefix_summary_unknown_step__prefix_scan
           n_pre known_questions q unknown only); try lia.
  - exact PreH17.
  - unfold KnownFlagsBridge in PreH18.
    destruct PreH18 as [_ Hbridge].
    specialize (Hbridge q ltac:(lia)).
    destruct Hbridge as [[Hknown Hnonzero] | [Hunknown Hzero]].
    + exfalso. apply Hnonzero. exact PreH1.
    + exact Hunknown.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (unknown_prefix_summary_known_step__prefix_scan
           n_pre known_questions q unknown only); try lia.
  - exact PreH17.
  - unfold KnownFlagsBridge in PreH18.
    destruct PreH18 as [_ Hbridge].
    specialize (Hbridge q ltac:(lia)).
    destruct Hbridge as [[Hknown Hnonzero] | [Hunknown Hzero]].
    + exact Hknown.
    + exfalso. apply PreH1. exact Hzero.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (q = n_pre + 1) by lia.
  subst q.
  Exists (@nil Z) (@nil Z).
  unfold ResultPrefix.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray.undef_full_to_undef_seg res_pre (m_pre + 1)).
    rewrite (CharArray.full_empty res_pre 0).
    cancel.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; lia.
  - split_pures;
      try (dump_pre_spatial; lia);
      try (dump_pre_spatial; assumption).
    dump_pre_spatial.
    rewrite (Zsublist_nil missing 0 0) by lia.
    rewrite Zlength_nil.
    unfold Spec.
    repeat split; try reflexivity; constructor.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (app out_2 (cons 1 nil)) (app result_bytes_2 (cons 49 nil)).
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    eapply result_prefix_accept_only__result_steps; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (app out_2 (cons 1 nil)) (app result_bytes_2 (cons 49 nil)).
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    eapply result_prefix_accept_all_known__result_steps; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (app out_2 (cons 0 nil)) (app result_bytes_2 (cons 48 nil)).
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    apply (result_prefix_reject_many_unknown__result_steps
      n_pre missing known_questions i out_2 result_bytes_2 unknown only).
    + lia.
    + lia.
    + exact PreH18.
    + exact PreH19.
Qed.

Lemma proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (app out_2 (cons 0 nil)) (app result_bytes_2 (cons 48 nil)).
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try lia.
    apply (result_prefix_reject_other__result_steps
      n_pre missing known_questions i out_2 result_bytes_2 unknown only).
    + lia.
    + exact PreH2.
    + exact PreH1.
    + exact PreH19.
    + exact PreH20.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = m_pre) by lia.
  subst i.
  pose proof
    (result_prefix_finish__final_result
       n_pre missing known_questions m_pre out_2 result_bytes_2
       PreH9 PreH17) as [Hspec Hbridge].
  Exists (result_bytes_2 ++ 0 :: nil) out_2.
  split_pure_spatial.
  - rewrite CharArray.undef_seg_empty.
    cancel.
    cancel (IntArray.full a_pre m_pre missing).
    cancel emp.
  - split_pures.
    + dump_pre_spatial. exact Hspec.
    + dump_pre_spatial. exact Hbridge.
Qed.
