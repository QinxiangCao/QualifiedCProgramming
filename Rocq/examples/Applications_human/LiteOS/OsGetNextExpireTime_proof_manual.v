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
From SimpleC.EE.Applications_human.LiteOS Require Import OsGetNextExpireTime_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.


Lemma proof_of_OsGetNextExpireTime_return_wit_2_split_goal_1 :
    OsGetNextExpireTime_return_wit_2_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    rewrite PreH3 in PreH1.
    rewrite PreH2 in PreH1.
    subst retval retval_2.
    unfold getminExpireTime.
    intros.
    remember (getFirstNodeExpireTime l1 startTime_pre tickPrecision_pre) as x.
    remember (getFirstNodeExpireTime l2 startTime_pre tickPrecision_pre) as y.
    assert (H_ltb : (x <? y)%Z = true) by (apply Z.ltb_lt; exact PreH1).
    rewrite H_ltb.
    lia.
Qed.

Lemma proof_of_OsGetNextExpireTime_return_wit_2 : OsGetNextExpireTime_return_wit_2.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsGetNextExpireTime_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_OsGetNextExpireTime_return_wit_1_split_goal_1 :
    OsGetNextExpireTime_return_wit_1_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    rewrite PreH3 in PreH1.
    rewrite PreH2 in PreH1.
    subst retval retval_2.
    unfold getminExpireTime.
    intros.
    remember (getFirstNodeExpireTime l1 startTime_pre tickPrecision_pre) as x.
    remember (getFirstNodeExpireTime l2 startTime_pre tickPrecision_pre) as y.
    assert (H_le : y <= x) by (apply Z.ge_le; exact PreH1).
    assert (H_ltb : (x <? y)%Z = false) by (apply Z.ltb_ge; exact H_le).
    rewrite H_ltb.
    lia.
Qed.

Lemma proof_of_OsGetNextExpireTime_return_wit_1 : OsGetNextExpireTime_return_wit_1.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsGetNextExpireTime_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_derive_swmtrSpec_by_highSpec : GetSortLinkNextExpireTime_derive_swmtrSpec_by_highSpec.
Proof. 
    unfold GetSortLinkNextExpireTime_derive_swmtrSpec_by_highSpec.
    LLM_pre_process ltac:(int_auto).
    intros.
    Exists Z.
    Exists (fun (p : addr) (swmtrID : glob_vars_and_defs.SwtmrID) =>
   “ p = &( ((glob_vars_and_defs.g_swtmrCBArray sg_swmtrSpec) # "SWTMR_CTRL_S" + swmtrID % 5) ->ₛ "stSortList") ” &&
   emp) l_swmtrSpec.
   unfold store_swtmr_sorted_dll.
   Intros y.
   rewrite H.
   unfold glob_vars_and_defs.SwtmrID. unfold SwtmrID.
   cancel.
   rewrite H0.
   match goal with
   | |- ?P |-- ?P ** _ => cancel P
   end.
   rewrite <- derivable1_wand_sepcon_adjoint.
   Intros retval_2.
   Exists retval_2.
   rewrite H1.
   csimpl.
   cancel.
   Exists (&( "g_swtmrSortLink")).
   csimpl.
   split_pure_spatial.
   - cancel.
   - split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_derive_taskSpec_by_highSpec : GetSortLinkNextExpireTime_derive_taskSpec_by_highSpec.
Proof. 
    unfold GetSortLinkNextExpireTime_derive_taskSpec_by_highSpec.
    LLM_pre_process ltac:(int_auto).
    intros.
    Exists Z (fun (p : addr) (taskID : glob_vars_and_defs.TaskID) =>
   “ p = &( ((glob_vars_and_defs.g_taskCBArray sg_taskSpec) # "LosTaskCB" + taskID) ->ₛ "sortList") ” &&
   emp) l_taskSpec.
   unfold store_task_sorted_dll.
   rewrite H.
   csimpl.
   unfold glob_vars_and_defs.TaskID.
   cancel.
   Intros y.
   rewrite H0.
   csimpl.
   cancel.
   rewrite <- derivable1_wand_sepcon_adjoint. 
   Intros retval_2.
   Exists retval_2.
   rewrite H1.
   csimpl.
   cancel.
   Exists y.
   cancel.
   rewrite H0.
   csimpl.
   split_pure_spatial.
   - cancel.
   - split_pures; dump_pre_spatial; reflexivity.
Qed. 
