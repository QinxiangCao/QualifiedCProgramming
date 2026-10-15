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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P016_450A_jzzhu_and_children_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P016_450A_jzzhu_and_children_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P016_450A_jzzhu_and_children_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold LastMaxPrefix.
  split; [lia |].
  left.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  fold LastMaxPrefix.
  assert (Hwant_i : 1 <= Znth i wants_data 0 <= 100).
  { apply PreH7. lia. }
  assert (Hturn :
    (Znth i wants_data 0 + m_pre - 1) ÷ m_pre =
    CandyTurns m_pre (Znth i wants_data 0)).
  { unfold CandyTurns.
    apply Z.quot_div_nonneg; lia. }
  apply (last_max_prefix_update_ge__prefix_updates
    m_pre wants_data i best answer
    ((Znth i wants_data 0 + m_pre - 1) ÷ m_pre)); try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  fold LastMaxPrefix.
  assert (Hwant_i : 1 <= Znth i wants_data 0 <= 100).
  { apply PreH7. lia. }
  assert (Hturn :
    (Znth i wants_data 0 + m_pre - 1) ÷ m_pre =
    CandyTurns m_pre (Znth i wants_data 0)).
  { unfold CandyTurns.
    apply Z.quot_div_nonneg; lia. }
  assert (Hturn_nonneg :
    0 <= (Znth i wants_data 0 + m_pre - 1) ÷ m_pre).
  { rewrite Hturn.
    unfold CandyTurns.
    apply Z.div_pos; lia. }
  apply (last_max_prefix_update_lt__prefix_updates
    m_pre wants_data i best answer
    ((Znth i wants_data 0 + m_pre - 1) ÷ m_pre)); try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength wants_data) by lia.
  subst i.
  assert (Hpositive : forall j,
    0 <= j < Zlength wants_data -> 0 < Znth j wants_data 0).
  { intros j Hj. specialize (PreH6 j Hj). lia. }
  unfold Spec.
  eapply candy_queue_trace_last_argmax__final_trace.
  - lia.
  - lia.
  - exact Hpositive.
  - exact PreH10.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
