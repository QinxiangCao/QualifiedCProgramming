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
From SimpleC.EE.QCP_demos_human Require Import functional_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import sll_lib.
From SimpleC.EE.QCP_demos_human Require Import functional_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_queue.
  subst.
  Exists q_l1 p_callee_v l1 (x_pre :: l2).
  split_pure_spatial.
  - cancel (&((q_pre)  # "queue" ->ₛ "l1") # Ptr  |-> q_l1).
    cancel (&((q_pre)  # "queue" ->ₛ "l2") # Ptr  |-> p_callee_v).
    cancel (sll q_l1 l1).
    cancel (sll p_callee_v (x_pre :: l2)).
  - dump_pre_spatial.
    simpl.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_queue.
  Intros p1 p2 l1 l2.
  Exists p2 p1 l1 l2.
  split_pure_spatial.
  - cancel (&((q)  # "queue" ->ₛ "l1") # Ptr  |-> p1).
    cancel (&((q)  # "queue" ->ₛ "l2") # Ptr  |-> p2).
    cancel (sll p1 l1).
    cancel (sll p2 l2).
  - dump_pre_spatial.
    exact H.
Qed.

Lemma proof_of_dequeue_return_wit_1 : dequeue_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_zero q_l1 l1 PreH2).
  Intros_p Hl1.
  subst q_l1 retval l1.
  unfold store_queue.
  Exists p_callee_v 0 l nil.
  split_pure_spatial.
  - simpl sll.
    split_pure_spatial.
    + cancel (&((q_pre)  # "queue" ->ₛ "l1") # Ptr  |-> p_callee_v).
      cancel (&((q_pre)  # "queue" ->ₛ "l2") # Ptr  |-> 0).
      cancel (sll p_callee_v l).
    + dump_pre_spatial.
      reflexivity.
  - split_pures.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      rewrite app_nil_r.
      reflexivity.
Qed.

Lemma proof_of_dequeue_return_wit_2_split_goal_1 :
  dequeue_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl in PreH4.
  injection PreH4 as ? ?.
  subst.
  dump_pre_spatial.
  reflexivity.
Qed.

Lemma proof_of_dequeue_return_wit_2_split_goal_spatial :
  dequeue_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl in PreH4.
  injection PreH4 as ? ?.
  subst.
  unfold store_queue.
  Exists p_callee_v q_l2 l1_tail l2.
  split_pure_spatial.
  - cancel (&((q_pre)  # "queue" ->ₛ "l1") # Ptr  |-> p_callee_v).
    cancel (&((q_pre)  # "queue" ->ₛ "l2") # Ptr  |-> q_l2).
    cancel (sll p_callee_v l1_tail).
    cancel (sll q_l2 l2).
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma proof_of_dequeue_return_wit_2 : dequeue_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  simpl in PreH4.
  injection PreH4 as ? ?.
  subst.
  unfold store_queue.
  Exists p_callee_v q_l2 l1_tail l2.
  split_pure_spatial.
  - cancel (&((q_pre)  # "queue" ->ₛ "l1") # Ptr  |-> p_callee_v).
    cancel (&((q_pre)  # "queue" ->ₛ "l2") # Ptr  |-> q_l2).
    cancel (sll p_callee_v l1_tail).
    cancel (sll q_l2 l2).
  - split_pures.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_dequeue_partial_solve_wit_3_pure_split_goal_1 :
  dequeue_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_zero q_l1 l1 PreH1).
  Intros_p Hl1.
  subst q_l1 l1.
  dump_pre_spatial.
  simpl in PreH2.
  symmetry.
  exact PreH2.
Qed.

Lemma proof_of_dequeue_partial_solve_wit_3_pure : dequeue_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_dequeue_partial_solve_wit_3_pure_split_goal_1.
Qed.

Lemma proof_of_dequeue_which_implies_wit_1 : dequeue_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_queue.
  Intros p1 p2 l1 l2.
  Exists p2 p1 l1 l2.
  split_pure_spatial.
  - cancel (&((q)  # "queue" ->ₛ "l1") # Ptr  |-> p1).
    cancel (&((q)  # "queue" ->ₛ "l2") # Ptr  |-> p2).
    cancel (sll p1 l1).
    cancel (sll p2 l2).
  - dump_pre_spatial.
    exact H.
Qed.

Lemma proof_of_dequeue_which_implies_wit_3 : dequeue_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_not_zero q_l1 l1 PreH1).
  Intros y a l0.
  Exists a l0.
  split_pure_spatial.
  - simpl sll.
    Exists y.
    split_pure_spatial.
    + cancel (&((q)  # "queue" ->ₛ "l1") # Ptr  |-> q_l1).
      cancel (&((q_l1)  # "list" ->ₛ "data") # Int  |-> a).
      cancel (&((q_l1)  # "list" ->ₛ "next") # Ptr  |-> y).
      cancel (sll y l0).
    + dump_pre_spatial.
      exact PreH1.
  - dump_pre_spatial.
    exact H.
Qed.
