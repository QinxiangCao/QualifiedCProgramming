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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P027_1800D_remove_two_letters_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P027_1800D_remove_two_letters_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P027_1800D_remove_two_letters_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (EqualGapTwoCount_bounds__gap_count_transitions text 0 ltac:(lia))
    as [Hnonneg Hupper].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (EqualGapTwoCount_bounds__gap_count_transitions text 0 ltac:(lia))
    as [_ Hupper].
  exact Hupper.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (EqualGapTwoCount_bounds__gap_count_transitions text 0 ltac:(lia))
    as [Hnonneg _].
  exact Hnonneg.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH3.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite !Znth_app_left__gap_count_transitions in PreH1 by lia.
  pose proof
    (EqualGapTwoCount_step_eq__gap_count_transitions text i PreH7 PreH1)
    as Hstep.
  rewrite Hstep.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_3 : solver_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (EqualGapTwoCount_bounds__gap_count_transitions text (i + 1) ltac:(lia))
    as [_ Hupper].
  exact Hupper.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_4 : solver_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (EqualGapTwoCount_bounds__gap_count_transitions text (i + 1) ltac:(lia))
    as [Hnonneg _].
  exact Hnonneg.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite !Znth_app_left__gap_count_transitions in PreH1 by lia.
  pose proof
    (EqualGapTwoCount_step_neq__gap_count_transitions text i PreH7 PreH1)
    as Hstep.
  rewrite Hstep.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (EqualGapTwoCount_bounds__gap_count_transitions text (i + 1) ltac:(lia))
    as [_ Hupper].
  exact Hupper.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_3 : solver_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (EqualGapTwoCount_bounds__gap_count_transitions text (i + 1) ltac:(lia))
    as [Hnonneg _].
  exact Hnonneg.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst n_pre.
  assert (Hi : i = Zlength text - 2) by lia.
  subst i.
  subst answer.
  apply remove_two_spec_count__final_cardinality.
  - lia.
  - apply (Forall_Znth_intro__final_cardinality
      (fun c => 97 <= c <= 122) text 0).
    intros k Hk.
    apply PreH4. lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
