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
From SimpleC.EE.QCP_demos_LLM Require Import sll_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Local Open Scope sac.

Lemma proof_of_length_safety_wit_2 : length_safety_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  - dump_pre_spatial.
    pose proof PreH5 as Hlen.
    rewrite PreH1 in Hlen.
    rewrite PreH4 in Hlen.
    rewrite Zlength_app in Hlen.
    rewrite Zlength_cons in Hlen.
    rewrite PreH2.
    pose proof Zlength_nonneg l1.
    pose proof Zlength_nonneg l3.
    lia.
  - dump_pre_spatial.
    rewrite PreH2.
    pose proof Zlength_nonneg l1.
    lia.
Qed.

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
      exact PreH1.
    + dump_pre_spatial.
      simpl.
      reflexivity.
Qed.

Lemma proof_of_length_entail_wit_3 : length_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst l2_2.
  Exists (l1_2 ++ (pdata :: nil))%list l3.
  split_pure_spatial.
  - sep_apply (sllseg_len1 p pdata pnext); [ | easy ].
    sep_apply (sllseg_sllseg p_pre p pnext l1_2 (pdata :: nil)%list).
    cancel.
  - split_pures.
    + dump_pre_spatial.
      rewrite <- app_assoc.
      simpl.
      exact PreH1.
    + dump_pre_spatial.
      exact PreH5.
    + dump_pre_spatial.
      rewrite PreH2.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      rewrite Zlength_nil.
      lia.
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
    rewrite PreH3.
    reflexivity.
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

Lemma proof_of_reverse_entail_wit_3 : reverse_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (vdata :: l1_2) l2_new.
  split_pure_spatial.
  - cancel (sll vnext l2_new).
    simpl sll.
    Exists w.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      exact PreH2.
  - dump_pre_spatial.
    subst l2_2.
    simpl.
    rewrite <- app_assoc.
    simpl.
    exact PreH1.
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

Lemma proof_of_reverse_alter_style1_entail_wit_3 : reverse_alter_style1_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (x :: l1_2) xs.
  split_pure_spatial.
  - cancel (sll vn xs).
    simpl sll.
    Exists w.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      exact PreH2.
  - dump_pre_spatial.
    subst l2_2.
    simpl.
    rewrite <- app_assoc.
    simpl.
    exact PreH1.
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

Lemma proof_of_reverse_alter_style2_entail_wit_3 : reverse_alter_style2_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (x :: l1_2) xs.
  split_pure_spatial.
  - cancel (sll v_inv_next xs).
    simpl sll.
    Exists w_inv.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      exact PreH2.
  - dump_pre_spatial.
    subst l2_2.
    simpl.
    rewrite <- app_assoc.
    simpl.
    exact PreH1.
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

Lemma proof_of_reverse_alter_style3_entail_wit_2 : reverse_alter_style3_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst w v.
  Exists nil l.
  split_pure_spatial.
  - cancel (sll 0 nil).
    cancel (sll p_pre l).
  - dump_pre_spatial.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_reverse_alter_style3_entail_wit_4 : reverse_alter_style3_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (vdata :: l1_2) l2_new.
  split_pure_spatial.
  - cancel (sll vnext l2_new).
    simpl sll.
    Exists w.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      exact PreH2.
  - dump_pre_spatial.
    subst l2_2.
    simpl.
    rewrite <- app_assoc.
    simpl.
    exact PreH1.
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

Lemma proof_of_append_entail_wit_2 : append_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists xn.
  Exists nil.
  Exists a.
  Exists l1n.
  split_pure_spatial.
  - cancel ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a).
    cancel ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn).
    cancel (sll xn l1n).
    cancel (sll y_pre l2).
    simpl sllseg.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      reflexivity.
  - split_pures.
    + dump_pre_spatial.
      simpl.
      symmetry.
      exact PreH2.
    + dump_pre_spatial.
      exact PreH1.
    + dump_pre_spatial.
      exact PreH1.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_append_entail_wit_4 : append_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst t_next_2 l1b_2.
  Exists unext.
  Exists (l1a_2 ++ (t_data_2 :: nil))%list.
  Exists udata.
  Exists l1b_new.
  split_pure_spatial.
  - sep_apply (sllseg_len1 t t_data_2 u); [ | tauto ].
    sep_apply (sllseg_sllseg x_pre).
    cancel.
  - split_pures.
    + dump_pre_spatial.
      rewrite <- app_assoc.
      simpl.
      exact PreH1.
    + dump_pre_spatial.
      exact PreH5.
    + dump_pre_spatial.
      exact PreH4.
    + dump_pre_spatial.
      reflexivity.
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
  sep_apply (sllseg_len1 t t_data y_pre); [ | tauto ].
  sep_apply (sllseg_sll t y_pre (t_data :: nil)%list l2).
  sep_apply (sllseg_sll x_pre t l1a (t_data :: l2)).
  subst l1.
  rewrite <- app_assoc.
  simpl.
  cancel.
Qed.

Lemma proof_of_append_long_entail_wit_2 : append_long_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists xn.
  Exists nil.
  Exists a.
  Exists l1b.
  split_pure_spatial.
  - cancel ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a).
    cancel ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn).
    cancel (sll xn l1b).
    cancel (sll y_pre l2).
    simpl sllseg.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      reflexivity.
  - split_pures.
    + dump_pre_spatial.
      simpl.
      symmetry.
      exact PreH3.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      exact PreH2.
    + dump_pre_spatial.
      exact PreH2.
Qed.

Lemma proof_of_append_long_entail_wit_4 : append_long_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst t_next_2 l1c_2.
  Exists un.
  Exists (l1a_2 ++ (b_2 :: nil))%list.
  Exists c.
  Exists l1d.
  split_pure_spatial.
  - sep_apply (sllseg_len1 t b_2 u); [ | tauto ].
    sep_apply (sllseg_sllseg x_pre).
    cancel.
  - split_pures.
    + dump_pre_spatial.
      rewrite <- app_assoc.
      simpl.
      exact PreH1.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      exact PreH5.
    + dump_pre_spatial.
      exact PreH4.
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
  sep_apply (sllseg_len1 t b y_pre); [ | tauto ].
  sep_apply (sllseg_sll t y_pre (b :: nil)%list l2).
  sep_apply (sllseg_sll x_pre t l1a (b :: l2)).
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
  sep_apply (sll_not_zero ptvv_2 l1b_2); [ | tauto ].
  Intros ptn a l0.
  Exists ptn (l1a_2 ++ a :: nil)%list l0.
  split_pure_spatial.
  - sep_apply (sllbseg_len1 ptv ptvv_2 a); [ | tauto ].
    sep_apply (sllbseg_sllbseg (&( "x" )) ptv (&((ptvv_2)  # "list" ->ₛ "next")) l1a_2 (a :: nil)%list).
    cancel.
  - dump_pre_spatial.
    subst l1b_2.
    rewrite <- app_assoc.
    simpl.
    exact PreH1.
Qed.

Lemma proof_of_append_2p_entail_wit_3 : append_2p_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH2.
  sep_apply (sll_zero 0 l1b); [ | reflexivity ].
  Intros_p Hl1b.
  rewrite Hl1b in PreH1.
  rewrite app_nil_r in PreH1.
  sep_apply sllbseg_2_sllseg.
  Intros pres_v.
  Exists pres_v.
  subst l1.
  cancel.
  cancel.
Qed.

Lemma proof_of_append_2p_return_wit_1 : append_2p_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sllseg_sll presv y_pre l1 l2).
  cancel.
Qed.
