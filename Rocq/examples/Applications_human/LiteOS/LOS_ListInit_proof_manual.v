From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.LiteOS Require Import LOS_ListInit_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_LOS_ListInit_return_wit_1 : LOS_ListInit_return_wit_1.
Proof. 
    unfold LOS_ListInit_return_wit_1.
    LLM_pre_process ltac:(int_auto).
    simpl.
    unfold store_dll.
    intros.
    unfold dllseg.
    Exists list_pre.
    Exists list_pre.
    split_pure_spatial.
    - cancel.
    - split_pures; dump_pre_spatial; auto.
Qed. 


