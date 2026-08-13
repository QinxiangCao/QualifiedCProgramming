Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick.
Import DLL.
Import SDLL.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma los_sortlink_strategy7_correctness : los_sortlink_strategy7.
  pre_process_default.
  intros.
  Intros_p H.
  rewrite H.
  cancel.
Qed.

Lemma los_sortlink_strategy14_correctness : los_sortlink_strategy14.
  pre_process_default.
  intros.
  Intros_p H.
  rewrite H.
  cancel.
Qed.

Lemma los_sortlink_strategy15_correctness : los_sortlink_strategy15.
  pre_process_default.
  intros.
  Intros_p H.
  rewrite H.
  cancel.
Qed.

Lemma los_sortlink_strategy18_correctness : los_sortlink_strategy18.
  pre_process_default.
Qed.

Lemma los_sortlink_strategy19_correctness : los_sortlink_strategy19.
  pre_process_default.
  Intros_p H.
  Intros_p H0.
  rewrite H.
  rewrite H0.
  unfold NULL in *.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.


Lemma los_sortlink_strategy6_correctness : los_sortlink_strategy6.
  pre_process_default.
  intros.
  Intros_p H.
  rewrite H.
  cancel.
Qed.


Lemma los_sortlink_strategy20_correctness : los_sortlink_strategy20.
  pre_process_default.
  intros.
  Intros_p H.
  Intros_p H0.
  Intros_p H1.
  rewrite H.
  rewrite H0.
  rewrite H1.
  simpl.
  csimpl.
  destruct a1.
  simpl.
  destruct data0.
  simpl.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; congruence.
Qed.

Lemma los_sortlink_strategy21_correctness : los_sortlink_strategy21.
  pre_process_default.
  intros.
  simpl.
  rewrite H.
  Intros_r v. 
  rewrite <- derivable1_wand_sepcon_adjoint.
  pre_process_default. Intros.
  subst v.
  cancel.
Qed.

Lemma los_sortlink_strategy22_correctness : los_sortlink_strategy22.
  pre_process_default.
  intros.
  cancel (sa # Ptr |-> sp).
  cancel (la # Ptr |-> re).
  rewrite <- derivable1_wand_sepcon_adjoint.
  Intros_p H.
  rewrite H.
  cancel.
Qed.

Lemma los_sortlink_strategy17_correctness : los_sortlink_strategy17.
  pre_process_default.
  intros.
  Exists x.
  split_pure_spatial.
  - cancel (storeA x a).
    cancel (&( x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px).
    cancel (&( px # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> x).
    cancel (dllseg_shift storeA x py l0).
    rewrite <- derivable1_wand_sepcon_adjoint.
    normalize.
    cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma los_sortlink_strategy3_correctness : los_sortlink_strategy3.
  pre_process_default.
  intros.
  Intros_p H.
  rewrite H.
  cancel.
Qed.

Lemma los_sortlink_strategy8_correctness : los_sortlink_strategy8.
  pre_process_default.
  intros.
  Intros_p H.
  rewrite H.
  cancel.
Qed.

Lemma los_sortlink_strategy11_correctness : los_sortlink_strategy11.
  pre_process_default.
  intros.
  Intros_p H.
  rewrite H.
  cancel.
Qed.


Lemma los_sortlink_strategy16_correctness : los_sortlink_strategy16.
  pre_process_default.
  intros.
  Intros x0.
  rewrite H.
  cancel.
Qed.
