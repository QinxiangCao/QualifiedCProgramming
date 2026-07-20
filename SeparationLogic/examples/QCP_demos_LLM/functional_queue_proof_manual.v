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
From SimpleC.EE.QCP_demos_LLM Require Import functional_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
From SimpleC.EE.QCP_demos_LLM Require Import functional_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  subst.
  Exists ql1 p_callee_v l1 (x_pre :: l2).
  split_pure_spatial.
  - cancel (&((q_pre)  # "queue" ->ₛ "l1") # Ptr  |-> ql1).
    cancel (&((q_pre)  # "queue" ->ₛ "l2") # Ptr  |-> p_callee_v).
    cancel (sll ql1 l1).
    cancel (sll p_callee_v (x_pre :: l2)).
  - dump_pre_spatial. 
    simpl.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Intros p1 p2 l1 l2.
  Exists p2 p1 l1 l2.
  split_pure_spatial.
  - cancel (&((q_pre)  # "queue" ->ₛ "l1") # Ptr  |-> p1).
    cancel (&((q_pre)  # "queue" ->ₛ "l2") # Ptr  |-> p2).
    cancel (sll p1 l1).
    cancel (sll p2 l2).
  - dump_pre_spatial.
    auto.
Qed.

Lemma proof_of_dequeue_return_wit_1 : dequeue_return_wit_1.
Proof.
  pre_process.
  subst.
  unfold store_queue.
  simpl in PreH2.
  inversion PreH2; subst.
  Exists p_callee_v ql2 l1_tail l2.
  split_pure_spatial.
  - cancel (&((q_pre)  # "queue" ->ₛ "l1") # Ptr  |-> p_callee_v).
    cancel (&((q_pre)  # "queue" ->ₛ "l2") # Ptr  |-> ql2).
    cancel (sll p_callee_v l1_tail).
    cancel (sll ql2 l2).
  - split_pures ; dump_pre_spatial ; reflexivity.
Qed.

Lemma proof_of_dequeue_entail_wit_1 : dequeue_entail_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Intros p1 p2 l1 l2.
  Exists p2 p1 l1 l2.
  split_pure_spatial.
  - cancel (&((q_pre)  # "queue" ->ₛ "l1") # Ptr  |-> p1).
    cancel (&((q_pre)  # "queue" ->ₛ "l2") # Ptr  |-> p2).
    cancel (sll p1 l1).
    cancel (sll p2 l2).
  - dump_pre_spatial.
    auto.
Qed.

Lemma proof_of_dequeue_entail_wit_2 : dequeue_entail_wit_2.
Proof.
  pre_process.
  sep_apply (sll_zero ql1_2 l1); [ | tauto ].
  Intros.
  subst.
  Exists retval.
  Exists (rev l2).
  split_pure_spatial.
  - cancel (&((q_pre)  # "queue" ->ₛ "l1") # Ptr  |-> retval).
    cancel (&((q_pre)  # "queue" ->ₛ "l2") # Ptr  |-> 0).
    cancel (sll retval (rev l2)).
  - dump_pre_spatial.
    simpl in PreH2.
    auto.
Qed.

Lemma proof_of_dequeue_entail_wit_3 : dequeue_entail_wit_3.
Proof.
  pre_process.
  sep_apply sll_not_zero; [ | tauto].
  Intros y a l0.
  Exists ql2_2.
  Exists l0.
  Exists l2_2.
  Exists ql1_2.
  split_pure_spatial.
  - match goal with
    | Hcons : l1 = _ :: _ |- _ => rewrite Hcons in PreH2
    end.
    inversion PreH2; subst.
    cancel (&((q_pre)  # "queue" ->ₛ "l1") # Ptr  |-> ql1_2).
    cancel (&((q_pre)  # "queue" ->ₛ "l2") # Ptr  |-> ql2_2).
    simpl.
    Exists y.
    split_pure_spatial.
    * cancel ((&((ql1_2)  # "list" ->ₛ "data")) # Int  |-> a).
      cancel ((&((ql1_2)  # "list" ->ₛ "next")) # Ptr  |-> y).
      cancel (sll y l0).
      cancel (sll ql2_2 l2_2).
    * dump_pre_spatial.
      auto.
  - split_pures ; dump_pre_spatial ; auto.
    match goal with
    | Hcons : l1 = _ :: _ |- _ => rewrite Hcons in PreH2
    end.
    inversion PreH2; subst.
    reflexivity.
Qed.

Lemma proof_of_dequeue_entail_wit_4_1 : dequeue_entail_wit_4_1.
Proof.
  pre_process.
  Exists 0 ql1_2.
  destruct rev_l2 ; try discriminate.
  inversion PreH1. subst.
  Exists rev_l2.
  Exists nil.
  split_pure_spatial.
  + cancel (&( q_pre # "queue" ->ₛ "l1") # Ptr |-> ql1_2).
    cancel (&( q_pre # "queue" ->ₛ "l2") # Ptr |-> 0).
    cancel (sll ql1_2 (z :: rev_l2)).
    simpl.
    split_pure_spatial.
    * reflexivity.
    * easy.
  + dump_pre_spatial.
    simpl.
    rewrite app_nil_r.
    reflexivity.
Qed.
