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
From SimpleC.EE.QCP_demos_human Require Import sll_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import sll_lib.
From SimpleC.EE.QCP_demos_human Require Import sll_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_queue.
  sep_apply (sllseg_len1 q_tail x_pre retval); [ | tauto ].
  sep_apply (sllseg_sllseg q_head q_tail retval l (x_pre :: nil)%list).
  Exists q_head retval.
  Exists retval_data retval_next.
  split_pure_spatial.
  - cancel.
    cancel.
  - dump_pre_spatial.
    exact PreH1.
Qed.

Lemma proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_queue.
  Intros h t u v.
  Exists h v u t.
  split_pure_spatial.
  - cancel (&((q)  # "queue" ->ₛ "tail") # Ptr  |-> t).
    cancel (&((t)  # "list" ->ₛ "data") # Int  |-> u).
    cancel (&((t)  # "list" ->ₛ "next") # Ptr  |-> v).
    cancel (&((q)  # "queue" ->ₛ "head") # Ptr  |-> h).
    cancel (sllseg h t l).
  - dump_pre_spatial.
    exact H.
Qed.

Lemma proof_of_dequeue_return_wit_1 : dequeue_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_queue.
  Exists q_head_next q_tail u v.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      tauto.
Qed.

Lemma proof_of_dequeue_which_implies_wit_1 : dequeue_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_queue.
  Intros h t u v.
  simpl.
  Intros h_next.
  Exists h_next h v u t.
  split_pure_spatial.
  - cancel (&((q)  # "queue" ->ₛ "tail") # Ptr  |-> t).
    cancel (&((t)  # "list" ->ₛ "data") # Int  |-> u).
    cancel (&((t)  # "list" ->ₛ "next") # Ptr  |-> v).
    cancel (&((q)  # "queue" ->ₛ "head") # Ptr  |-> h).
    cancel (&((h)  # "list" ->ₛ "data") # Int  |-> x).
    cancel (&((h)  # "list" ->ₛ "next") # Ptr  |-> h_next).
    cancel (sllseg h_next t l).
  - dump_pre_spatial.
    exact H.
Qed.

Lemma proof_of_init_empty_queue_return_wit_1 : init_empty_queue_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_queue.
  Exists retval_2 retval_2 retval_data retval_next.
  simpl sllseg.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      exact PreH1.
    + dump_pre_spatial.
      reflexivity.
Qed.
