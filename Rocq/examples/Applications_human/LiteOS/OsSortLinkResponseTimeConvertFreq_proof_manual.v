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
From SimpleC.EE.Applications_human.LiteOS Require Import OsSortLinkResponseTimeConvertFreq_goal.
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

Lemma proof_of_SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec : SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec.
Proof. 
   LLM_pre_process ltac:(int_auto).
   unfold store_swtmr_sorted_dll. 
   Intros y. subst y.
   Exists Z.
   Exists n_swmtrSpec (fun (p : addr) (swmtrID : SwtmrID) => “ p = &(((sg_swmtrSpec).(g_swtmrCBArray) # ("SWTMR_CTRL_S") + swmtrID % 5) ->ₛ "stSortList") ” && emp) l_swmtrSpec.
   cancel.
   rewrite H0.
   unfold glob_vars_and_defs.SwtmrID.
   csimpl.
   cancel.
   unfold SwtmrID.
   split_pure_spatial.
   - cancel (store_sorted_dll
       (fun (p : addr) (swmtrID : Z) =>
        “ p =
          &(
          ((sg_swmtrSpec).(g_swtmrCBArray) # ("SWTMR_CTRL_S") + swmtrID % 5)
          ->ₛ "stSortList") ” && emp)
       &( &( "g_swtmrSortLink") ->ₛ "sortLink") l_swmtrSpec).
     cancel (&( "g_sysClock") # UInt64 |-> n_swmtrSpec).
     rewrite <- derivable1_wand_sepcon_adjoint.
     Exists (&( "g_swtmrSortLink")).
     csimpl.
     split_pure_spatial.
     + cancel.
     + dump_pre_spatial.
       reflexivity.
   - dump_pre_spatial.
     exact H.
Qed. 

Lemma proof_of_SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec : SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec.
Proof. 
   LLM_pre_process ltac:(int_auto).
   unfold store_task_sorted_dll.
   Intros y. subst y.
   Exists Z.
   Exists n_taskSpec (fun (p : addr) (taskID : glob_vars_and_defs.TaskID) =>
    “ p = &( ((glob_vars_and_defs.g_taskCBArray sg_taskSpec) # "LosTaskCB" + taskID) ->ₛ "sortList") ” &&
    emp) l_taskSpec.
   cancel.
   rewrite H0.
   unfold glob_vars_and_defs.TaskID.
   csimpl.
   split_pure_spatial.
   - cancel (store_sorted_dll
       (fun (p : addr) (taskID : glob_vars_and_defs.TaskID) =>
        “ p = &(
          ((glob_vars_and_defs.g_taskCBArray sg_taskSpec) # "LosTaskCB" + taskID)
          ->ₛ "sortList") ” && emp)
       &( &( "g_taskSortLink") ->ₛ "sortLink") l_taskSpec).
     cancel (&( "g_sysClock") # UInt64 |-> n_taskSpec).
     rewrite <- derivable1_wand_sepcon_adjoint.
     Exists (&( "g_taskSortLink")).
     csimpl.
     split_pure_spatial.
     + cancel.
     + dump_pre_spatial.
       reflexivity.
   - dump_pre_spatial.
     exact H.
Qed.
