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
From SimpleC.EE.QCP_demos_human Require Import dll_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import dll_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_queue.
  sep_apply dllseg_head_zero; [ | tauto ].
  Intros.
  subst.
  Exists retval retval.
  sep_apply dllseg_len1; [ | tauto ].
  cancel.
  change NULL with 0.
  change (nil +:: x_pre) with (x_pre :: nil).
  cancel.
Qed.

Lemma proof_of_enqueue_return_wit_2 : enqueue_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_queue.
  Exists q_head retval.
  sep_apply (dllseg_len1 q_tail); [ | tauto ].
  sep_apply (dllseg_len1 retval); [ | tauto ].
  sep_apply (dllseg_dllseg q_tail).
  sep_apply (dllseg_dllseg q_head).
  cancel.
  change NULL with 0.
  cancel.
  rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  unfold store_queue.
  Intros h t; Exists h t.
  change NULL with 0.
  cancel (dllseg h 0 0 t l).
  cancel (&((q)  # "queue" ->ₛ "head") # Ptr  |-> h).
  cancel (&((q)  # "queue" ->ₛ "tail") # Ptr  |-> t).
Qed.

Lemma proof_of_enqueue_which_implies_wit_2 : enqueue_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply dllseg_head_neq_destruct_tail; [ | tauto ].
  Intros z l0 a.
  Exists z 0 l0 a.
  split_pure_spatial.
  - cancel (&((q)  # "queue" ->ₛ "tail") # Ptr  |-> q_tail).
    cancel (&((q_tail)  # "list" ->ₛ "data") # Int  |-> a).
    cancel (&((q_tail)  # "list" ->ₛ "next") # Ptr  |-> 0).
    cancel (&((q_tail)  # "list" ->ₛ "prev") # Ptr  |-> z).
    cancel (&((q)  # "queue" ->ₛ "head") # Ptr  |-> q_head).
    cancel (dllseg q_head q_tail 0 z l0).
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity.
Qed.

Lemma proof_of_dequeue_return_wit_1 : dequeue_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_queue.
  sep_apply dllseg_head_zero; [ | tauto ].
  Intros.
  subst.
  Exists 0 0.
  simpl.
  repeat (split_pure_spatial || split_pures).
  - cancel.
  - dump_pre_spatial. unfold NULL. reflexivity.
  - dump_pre_spatial. unfold NULL. reflexivity.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_dequeue_return_wit_2 : dequeue_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  unfold store_queue.
  Exists q_head_next q_tail.
  simpl.
  Exists q_head_next_2.
  change NULL with 0.
  repeat (split_pure_spatial || split_pures).
  - cancel (&(q_head_next # "list" ->ₛ "data") # Int |-> q_head_data).
    cancel (&(q_head_next # "list" ->ₛ "next") # Ptr |-> q_head_next_2).
    cancel (&(q_head_next # "list" ->ₛ "prev") # Ptr |-> 0).
    cancel (dllseg q_head_next_2 0 q_head_next q_tail l0).
    cancel (&(q_pre # "queue" ->ₛ "head") # Ptr |-> q_head_next).
    cancel (&(q_pre # "queue" ->ₛ "tail") # Ptr |-> q_tail).
  - dump_pre_spatial. reflexivity.
  - dump_pre_spatial. tauto.
Qed.

Lemma proof_of_dequeue_which_implies_wit_1 : dequeue_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_queue.
  Intros h t.
  simpl.
  Intros h_next.
  Exists h_next t 0 h.
  change NULL with 0.
  split_pure_spatial.
  - cancel (&((q)  # "queue" ->ₛ "head") # Ptr  |-> h).
    cancel (&((h)  # "list" ->ₛ "prev") # Ptr  |-> 0).
    cancel (&((h)  # "list" ->ₛ "data") # Int  |-> x).
    cancel (&((q)  # "queue" ->ₛ "tail") # Ptr  |-> t).
    cancel (&((h)  # "list" ->ₛ "next") # Ptr  |-> h_next).
    cancel (dllseg h_next 0 h t l).
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma proof_of_dequeue_which_implies_wit_2 : dequeue_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply dllseg_head_neq; [ | tauto ].
  Intros z a l0.
  Exists z a l0.
  split_pure_spatial.
  - cancel (&((q)  # "queue" ->ₛ "head") # Ptr  |-> q_head).
    cancel (&((q_head)  # "list" ->ₛ "data") # Int  |-> a).
    cancel (&((q_head)  # "list" ->ₛ "prev") # Ptr  |-> p).
    cancel (&((q)  # "queue" ->ₛ "tail") # Ptr  |-> q_tail).
    cancel (&((q_head)  # "list" ->ₛ "next") # Ptr  |-> z).
    cancel (dllseg z 0 q_head q_tail l0).
  - dump_pre_spatial.
    assumption.
Qed.
