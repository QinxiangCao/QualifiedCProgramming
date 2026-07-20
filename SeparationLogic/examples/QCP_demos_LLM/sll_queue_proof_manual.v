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
From SimpleC.EE.QCP_demos_LLM Require Import sll_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
From SimpleC.EE.QCP_demos_LLM Require Import sll_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Intros qhead qtail u v.
  Exists v.
  Exists u.
  Exists qhead.
  Exists qtail.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  sep_apply (sllseg_len1 qtail x_pre retval); [ | tauto ].
  sep_apply (sllseg_sllseg qhead qtail retval l (x_pre :: nil)%list).
  Exists qhead retval.
  Exists retval_data retval_next.
  split_pure_spatial.
  - cancel.
    cancel.
  - dump_pre_spatial.
    exact PreH1.
Qed.

Lemma proof_of_dequeue_entail_wit_1 : dequeue_entail_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Intros qhead qtail u v.
  simpl sllseg.
  Intros qheadnext.
  Exists v.
  Exists u.
  Exists qheadnext.
  Exists qtail.
  Exists qhead.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      exact H0.
    + dump_pre_spatial.
      exact H.
Qed.

Lemma proof_of_dequeue_return_wit_1 : dequeue_return_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Exists qheadnext qtail u v.
  split_pure_spatial.
  - cancel.
    cancel.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      exact PreH2.
Qed.

Lemma proof_of_init_empty_queue_return_wit_1 : init_empty_queue_return_wit_1.
Proof.
  pre_process.
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
