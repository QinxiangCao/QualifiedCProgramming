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
From SimpleC.EE.Applications_human.LiteOS Require Import OsAdd2SortLink_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_OsAdd2SortLink_partial_solve_wit_2_pure_split_goal_1 :
    OsAdd2SortLink_partial_solve_wit_2_pure_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    assert (unsigned_last_nbits (waitTicks_pre * g) 64 = waitTicks_pre * g) as Hbits1 by
      (pose proof (unsigned_last_nbits_eq (waitTicks_pre * g) 64) as Hbits1_eq;
       rewrite Hbits1_eq; lia).
    rewrite Hbits1.
    assert (unsigned_last_nbits (startTime_pre + waitTicks_pre * g ÷ 100) 64 =
      startTime_pre + waitTicks_pre * g ÷ 100) as Hbits2 by
      (pose proof (unsigned_last_nbits_eq (startTime_pre + waitTicks_pre * g ÷ 100) 64) as Hbits2_eq;
       rewrite Hbits2_eq; lia).
    rewrite Hbits2.
    dump_pre_spatial.
    reflexivity.
Qed.

Lemma proof_of_OsAdd2SortLink_partial_solve_wit_2_pure : OsAdd2SortLink_partial_solve_wit_2_pure.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsAdd2SortLink_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_OsAdd2SortLink_which_implies_wit_1_split_goal_spatial :
    OsAdd2SortLink_which_implies_wit_1_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    unfold storesortedLinkTaskNode.
    Intros y.
    apply addr_of_arrow_field_inv in H.
    rewrite H.
    simpl.
    cancel.
Qed.

Lemma proof_of_OsAdd2SortLink_which_implies_wit_1 : OsAdd2SortLink_which_implies_wit_1.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsAdd2SortLink_which_implies_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_OsAdd2SortLink_which_implies_wit_2_split_goal_spatial :
    OsAdd2SortLink_which_implies_wit_2_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    subst node_responseTime.
    unfold storesortedLinkTaskNode.
    Exists node.
    simpl.
    split_pure_spatial.
    - cancel.
    - dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_OsAdd2SortLink_which_implies_wit_2 : OsAdd2SortLink_which_implies_wit_2.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsAdd2SortLink_which_implies_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_OsAdd2SortLink_return_wit_1 : OsAdd2SortLink_return_wit_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    Exists l1_2 l2_2.
    split_pure_spatial.
    - cancel.
    - split_pures; dump_pre_spatial; auto.
Qed.


Lemma proof_of_OsAddNode2SortLink_derive_taskSpec_by_highSpec : OsAddNode2SortLink_derive_taskSpec_by_highSpec.
Proof. 
    unfold OsAddNode2SortLink_derive_taskSpec_by_highSpec.
    LLM_pre_process ltac:(int_auto).
    intros.
    Intros un pu.
    csimpl.
    simpl.
    unfold store_task_sorted_dll.
    Exists Z a_taskSpec t_taskSpec (fun (p : addr) (taskID : glob_vars_and_defs.TaskID) =>
    “ p = &( ((glob_vars_and_defs.g_taskCBArray sg_taskSpec) # "LosTaskCB" + taskID) ->ₛ "sortList") ” &&
    emp) l_taskSpec.
    Intros x.
    csimpl.
    simpl.
    Exists un pu.
    rewrite H.
    unfold store_task_sorted_dll.
    rewrite H0.
    unfold glob_vars_and_defs.TaskID.
    csimpl.
    cancel.
    unfold storesortedLinkTaskNode.
    Intros y.
    unfold task_store.
    apply addr_of_arrow_field_inv in H1.
    rewrite H1.
    unfold storesortedLinkNode.
    Exists y.
    csimpl.
    simpl.
    cancel.
    Intros_p H2.
    split_pure_spatial.
    - cancel.
      cancel (&( y # "SortLinkList" ->ₛ "responseTime") # UInt64 |-> t_taskSpec).
      rewrite <- derivable1_wand_sepcon_adjoint.
      Intros l1_2 l2_2.
      Exists l1_2 l2_2.
      Exists x.
      rewrite H0.
      csimpl.
      andp_lift (“ l_taskSpec = l1_2 ++ l2_2 ”).
      split_pure_spatial.
      + cancel.
      + split_pures.
        * dump_pre_spatial.
          assumption.
        * dump_pre_spatial.
          reflexivity.
    - split_pures.
      + dump_pre_spatial.
        reflexivity.
      + dump_pre_spatial.
        assumption.
Qed. 
