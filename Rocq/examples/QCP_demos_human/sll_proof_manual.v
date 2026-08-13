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
From SimpleC.EE.QCP_demos_human Require Import sll_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import sll_lib.
Local Open Scope sac.

Lemma proof_of_length_entail_wit_1 : length_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists nil l.
  split_pure_spatial.
  - simpl sllseg.
    split_pure_spatial.
    + cancel (sll p_pre l).
    + dump_pre_spatial.
      reflexivity.
  - split_pures.
    + dump_pre_spatial.
      simpl.
      reflexivity.
    + dump_pre_spatial.
      simpl.
      reflexivity.
    + dump_pre_spatial.
      exact PreH1.
Qed.

Lemma proof_of_length_entail_wit_2 : length_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (l1_2 ++ (p_data::nil)) l3.
  split_pure_spatial.
  - simpl.
    sep_apply sllseg_len1; try easy.
    sep_apply (sllseg_sllseg p_pre).
    easy.
  - split_pures.
    + dump_pre_spatial.
      rewrite PreH2, PreH1 ; clear PreH2 PreH1.
      rename l1_2 into l1.
      revert l1 PreH3.
      induction l3; intros; simpl.
      * rewrite app_nil_r. auto.
      * rewrite <- app_assoc. simpl. f_equal.
    + dump_pre_spatial.
      simpl.
      rewrite Zlength_app.
      rewrite <- PreH3.
      rewrite Zlength_cons. rewrite Zlength_nil. lia.
    + dump_pre_spatial.
      exact PreH4.
Qed. 

Lemma proof_of_length_return_wit_1 : length_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst p.
  sep_apply (sll_zero 0 l2); [ | reflexivity ].
  Intros_p Hl2.
  rewrite Hl2 in PreH1.
  rewrite app_nil_r in PreH1.
  subst l.
  split_pure_spatial.
  - apply sllseg_0_sll.
  - dump_pre_spatial.
    rewrite PreH2.
    reflexivity.
Qed.

Lemma proof_of_length_safety_wit_2 : length_safety_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  - dump_pre_spatial.
    rewrite PreH3.
    rewrite PreH2 in PreH4.
    rewrite PreH1 in PreH4.
    rewrite Zlength_app in PreH4.
    rewrite Zlength_cons in PreH4.
    pose proof Zlength_nonneg l3.
    lia.
  - dump_pre_spatial.
    rewrite PreH3.
    pose proof Zlength_nonneg l1.
    lia.
Qed.

Lemma proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists nil l.
  split_pure_spatial.
  - simpl sll.
    split_pure_spatial.
    + cancel (sll p_pre l).
    + dump_pre_spatial.
      reflexivity.
  - dump_pre_spatial.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_reverse_entail_wit_2_split_goal_1 :
  reverse_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst l2_2.
  simpl.
  rewrite <- app_assoc.
  simpl. auto.
Qed.

Lemma proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_reverse_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_zero v l2); [ | tauto ].
  Intros_p Hl2.
  rewrite Hl2 in PreH1.
  rewrite app_nil_r in PreH1.
  subst l.
  rewrite rev_involutive.
  cancel (sll w l1).
Qed.

Lemma proof_of_reverse_alter_style1_entail_wit_1 : reverse_alter_style1_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists nil l.
  split_pure_spatial.
  - simpl sll.
    split_pure_spatial.
    + cancel (sll p_pre l).
    + dump_pre_spatial.
      reflexivity.
  - dump_pre_spatial.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_reverse_alter_style1_entail_wit_2_split_goal_1 :
  reverse_alter_style1_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst l2_2.
  simpl.
  rewrite <- app_assoc.
  simpl. auto.
Qed.

Lemma proof_of_reverse_alter_style1_entail_wit_2 :
  reverse_alter_style1_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_reverse_alter_style1_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_reverse_alter_style1_return_wit_1 : reverse_alter_style1_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_zero v l2); [ | tauto ].
  Intros_p Hl2.
  rewrite Hl2 in PreH1.
  rewrite app_nil_r in PreH1.
  subst l.
  rewrite rev_involutive.
  cancel (sll w l1).
Qed.

Lemma proof_of_reverse_alter_style2_entail_wit_1 : reverse_alter_style2_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists nil l.
  split_pure_spatial.
  - simpl sll.
    split_pure_spatial.
    + cancel (sll p_pre l).
    + dump_pre_spatial.
      reflexivity.
  - dump_pre_spatial.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_reverse_alter_style2_entail_wit_2_split_goal_1 :
  reverse_alter_style2_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst l2_2.
  simpl.
  rewrite <- app_assoc.
  simpl. auto.
Qed.

Lemma proof_of_reverse_alter_style2_entail_wit_2 :
  reverse_alter_style2_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_reverse_alter_style2_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_reverse_alter_style3_entail_wit_3 : reverse_alter_style3_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists nil l.
  subst w v.
  simpl.
  split_pure_spatial.
  - Intros_p Hnull.
    cancel (sll p_pre l).
  - split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_reverse_alter_style3_entail_wit_4 : reverse_alter_style3_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (v_data :: l1_2) l2_new.
  split_pure_spatial.
  - cancel (sll v_next l2_new).
    simpl sll.
    Exists w.
    split_pure_spatial.
    + cancel (sll w l1_2).
      cancel.
    + dump_pre_spatial.
      exact PreH3.
  - dump_pre_spatial.
    subst l2_2.
    simpl.
    rewrite <- app_assoc.
    simpl.
    exact PreH2.
Qed.

Lemma proof_of_reverse_alter_style3_return_wit_1 : reverse_alter_style3_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_zero v l2); [ | tauto ].
  Intros_p Hl2.
  rewrite Hl2 in PreH1.
  rewrite app_nil_r in PreH1.
  subst l.
  rewrite rev_involutive.
  cancel (sll w l1).
Qed.

Lemma proof_of_reverse_alter_style2_return_wit_1 : reverse_alter_style2_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_zero v_inv l2); [ | tauto ].
  Intros_p Hl2.
  rewrite Hl2 in PreH1.
  rewrite app_nil_r in PreH1.
  subst l.
  rewrite rev_involutive.
  cancel (sll w_inv l1).
Qed.

Lemma proof_of_append_entail_wit_1_split_goal_1 :
  append_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_append_entail_wit_1 : append_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_append_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_append_entail_wit_2 : append_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst t_next_2 l1b_2.
  Exists u_next (l1a_2 ++ (t_data_2 :: nil)%list) u_data l1b_new.
  split_pure_spatial.
  - sep_apply (sllseg_len1 t t_data_2 u); [ | tauto ].
    sep_apply (sllseg_sllseg x t u l1a_2 (t_data_2 :: nil)%list).
    cancel.
  - split_pures.
    + dump_pre_spatial.
      rewrite <- app_assoc.
      simpl.
      exact PreH3.
    + dump_pre_spatial.
      exact PreH2.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      exact PreH6.
    + dump_pre_spatial.
      exact PreH7.
Qed.

Lemma proof_of_append_return_wit_2 : append_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1.
  sep_apply (sll_zero 0 l1); [ | reflexivity ].
  Intros_p Hl1.
  rewrite Hl1 in *.
  subst l1.
  simpl.
  cancel (sll y_pre l2).
Qed.

Lemma proof_of_append_return_wit_1 : append_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst t_next.
  sep_apply (sll_zero u l1b); [ | tauto ].
  Intros_p Hl1b.
  rewrite Hl1b in *.
  sep_apply (sllseg_len1 t t_data y); [ | tauto ].
  sep_apply (sllseg_sll t y (t_data :: nil)%list l2).
  sep_apply (sllseg_sll x t l1a (t_data :: l2)).
  subst l1.
  rewrite <- app_assoc.
  simpl.
  cancel.
Qed.

Lemma proof_of_append_long_entail_wit_1_split_goal_1 :
  append_long_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_append_long_entail_wit_1 : append_long_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_append_long_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_append_long_entail_wit_2 : append_long_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst t_next_2 l1c_2.
  Exists un (l1a_2 ++ (b_2 :: nil)%list) c l1d.
  split_pure_spatial.
  - sep_apply (sllseg_len1 t b_2 u); [ | tauto ].
    sep_apply (sllseg_sllseg x t u l1a_2 (b_2 :: nil)%list).
    cancel.
  - split_pures.
    + dump_pre_spatial.
      rewrite <- app_assoc.
      simpl.
      exact PreH3.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      exact PreH2.
    + dump_pre_spatial.
      exact PreH6.
    + dump_pre_spatial.
      exact PreH7.
    + dump_pre_spatial.
      exact PreH8.
Qed.

Lemma proof_of_append_long_return_wit_3 : append_long_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1.
  sep_apply (sll_zero 0 l1); [ | reflexivity ].
  Intros_p Hl1.
  rewrite Hl1 in *.
  subst l1.
  simpl.
  cancel (sll y_pre l2).
Qed.

Lemma proof_of_append_long_return_wit_2 : append_long_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH1.
  sep_apply (sll_zero 0 l1b); [ | reflexivity ].
  Intros_p Hl1b.
  rewrite Hl1b in *.
  sep_apply (sllseg_len1 x_pre a y_pre); [ | tauto ].
  sep_apply (sllseg_sll x_pre y_pre (a :: nil)%list l2).
  subst l1.
  simpl.
  cancel.
Qed.

Lemma proof_of_append_long_return_wit_1 : append_long_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst t_next.
  sep_apply (sll_zero u l1c); [ | tauto ].
  Intros_p Hl1c.
  rewrite Hl1c in *.
  sep_apply (sllseg_len1 t b y); [ | tauto ].
  sep_apply (sllseg_sll t y (b :: nil)%list l2).
  sep_apply (sllseg_sll x t l1a (b :: l2)).
  subst l1.
  rewrite <- app_assoc.
  simpl.
  cancel.
Qed.

Lemma proof_of_append_2p_entail_wit_1 : append_2p_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists nil l1.
  split_pure_spatial.
  - simpl sllbseg.
    split_pure_spatial.
    + cancel (sll x_pre l1).
      cancel (sll y_pre l2).
    + dump_pre_spatial.
      reflexivity.
  - dump_pre_spatial.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_append_2p_entail_wit_2 : append_2p_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_not_zero pt_v_2 l1b_2); [ | tauto ].
  Intros pt_v x l0.
  rename H0 into Hl1b.
  Exists pt_v (l1a_2 ++ x :: nil)%list l0.
  split_pure_spatial.
  - sep_apply (sllbseg_len1 pt pt_v_2 x); [ | tauto ].
    sep_apply (sllbseg_sllbseg (&( "x" )) pt (&((pt_v_2)  # "list" ->ₛ "next")) l1a_2 (x :: nil)%list).
    cancel.
  - dump_pre_spatial.
    rewrite Hl1b in PreH1.
    rewrite <- app_assoc.
    simpl.
    exact PreH1.
Qed.

Lemma proof_of_append_2p_return_wit_1 : append_2p_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sll_zero pt_v l1b); [ | tauto ].
  Intros_p Hl1b.
  rewrite Hl1b in PreH1.
  rewrite app_nil_r in PreH1.
  subst l1.
  sep_apply (sllseg_sll pres_v y l1a l2).
  cancel.
Qed.

Lemma proof_of_append_2p_which_implies_wit_1 : append_2p_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply sllbseg_2_sllseg.
  Intros y'.
  Exists y'.
  subst pt_v.
  cancel.
Qed.
