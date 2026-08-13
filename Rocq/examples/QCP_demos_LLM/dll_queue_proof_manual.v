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
From SimpleC.EE.QCP_demos_LLM Require Import dll_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.dll_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	unfold store_queue.
	Intros qhead qtail.
	Exists qhead qtail.
	change (dllseg qhead NULL NULL qtail l) with (dllseg qhead 0 0 qtail l).
	cancel (&((q_pre)  # "queue" ->ₛ "head") # Ptr  |-> qhead).
	cancel (&((q_pre)  # "queue" ->ₛ "tail") # Ptr  |-> qtail).
	cancel (dllseg qhead 0 0 qtail l).
Qed.

Lemma proof_of_enqueue_entail_wit_2 : enqueue_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	assert (Hqhead_neq : qhead_2 <> 0) by lia.
	sep_apply_l_atomic (dllseg_head_neq_destruct_tail qhead_2 0 0 qtail_2 l Hqhead_neq).
	Intros qtailprev l0 qtailv.
	Exists qtailprev.
	Exists 0.
	Exists l0.
	Exists qtailv.
	Exists qhead_2.
	Exists qtail_2.
	split_pure_spatial.
	- cancel ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0).
		cancel ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0).
		cancel ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre).
		cancel ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_2).
		cancel ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail_2).
		cancel (dllseg qhead_2 qtail_2 0 qtailprev l0).
		cancel ((&((qtail_2)  # "list" ->ₛ "data")) # Int  |-> qtailv).
		cancel ((&((qtail_2)  # "list" ->ₛ "next")) # Ptr  |-> 0).
		cancel ((&((qtail_2)  # "list" ->ₛ "prev")) # Ptr  |-> qtailprev).
	- split_pures.
		+ dump_pre_spatial.
			exact PreH2.
		+ dump_pre_spatial.
			exact H.
		+ dump_pre_spatial.
			exact PreH1.
		+ dump_pre_spatial.
			exact H0.
		+ dump_pre_spatial.
			reflexivity.
Qed.

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
  Exists qhead p.
  sep_apply (dllseg_len1 qtail); [ | tauto ].
  sep_apply (dllseg_len1 p); [ | tauto ].
  sep_apply (dllseg_dllseg qtail).
  sep_apply (dllseg_dllseg qhead).
  cancel.
  change NULL with 0.
  cancel.
  rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_dequeue_entail_wit_1 : dequeue_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	unfold store_queue.
	Intros qhead qtail.
	simpl.
	Intros qhead_next.
	Exists qtail qhead_next qhead.
	split_pure_spatial.
	- unfold NULL.
		cancel ((&((qhead)  # "list" ->ₛ "prev")) # Ptr  |-> 0).
		cancel ((&((qhead)  # "list" ->ₛ "data")) # Int  |-> x).
		cancel ((&((qhead)  # "list" ->ₛ "next")) # Ptr  |-> qhead_next).
		cancel (dllseg qhead_next 0 qhead qtail l).
		cancel ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead).
		cancel ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail).
	- dump_pre_spatial.
		exact H.
Qed.

Lemma proof_of_dequeue_entail_wit_2 : dequeue_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (dllseg_head_neq qheadnext_2 0 qhead qtail_2 l PreH1).
	Intros qhead_next headv l0.
	Exists qtail_2.
	Exists qhead_next.
	Exists headv.
	Exists l0.
	Exists qheadnext_2.
	split_pure_spatial.
	- cancel ((&((qheadnext_2)  # "list" ->ₛ "prev")) # Ptr  |-> qhead).
		cancel ((&((qheadnext_2)  # "list" ->ₛ "data")) # Int  |-> headv).
		cancel ((&((qheadnext_2)  # "list" ->ₛ "next")) # Ptr  |-> qhead_next).
		cancel (dllseg qhead_next 0 qheadnext_2 qtail_2 l0).
		cancel ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qheadnext_2).
		cancel ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail_2).
	- split_pures.
		+ dump_pre_spatial.
			exact PreH1.
		+ dump_pre_spatial.
			exact H.
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
  Exists qhead qtail.
  simpl.
  Exists qheadnext.
  change NULL with 0.
  repeat (split_pure_spatial || split_pures).
  - cancel (&(qhead # "list" ->ₛ "data") # Int |-> headv).
    cancel (&(qhead # "list" ->ₛ "next") # Ptr |-> qheadnext).
    cancel (&(qhead # "list" ->ₛ "prev") # Ptr |-> 0).
    cancel (dllseg qheadnext 0 qhead qtail l0).
    cancel (&(q_pre # "queue" ->ₛ "head") # Ptr |-> qhead).
    cancel (&(q_pre # "queue" ->ₛ "tail") # Ptr |-> qtail).
  - dump_pre_spatial. reflexivity.
  - dump_pre_spatial. exact PreH1.
Qed.
