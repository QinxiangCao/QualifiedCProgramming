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
From SimpleC.EE.Applications_human.mergeablelist Require Import sll_project_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From SimpleC.EE.Applications_human.mergeablelist Require Import sll_project_lib.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_cons_list_return_wit_1 : cons_list_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold sll_pt.
  destruct l.
  - Intros. subst next_pre.
    Right.
    Exists (&(retval # "sll" ->ₛ"next")).
    simpl sllbseg.
    split_pure_spatial.
    + cancel.
    + repeat split_pures; dump_pre_spatial;
        try assumption; try reflexivity; try discriminate.
  - Intros.
    Left.
    Exists pt.
    simpl sllbseg.
    Exists next_pre.
    split_pure_spatial.
    + normalize.
      cancel (&(retval # "sll" ->ₛ "data") # UInt |-> data_pre); cancel.
    + repeat split_pures; dump_pre_spatial;
        try assumption; try reflexivity; discriminate.
Qed.

Lemma proof_of_free_list_return_wit_1_split_goal_spatial :
  free_list_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst head.
  sep_apply sll_zero.
  - Intros_p Hl. cancel.
  - reflexivity.
Qed.

Lemma proof_of_free_list_return_wit_1 : free_list_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_free_list_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_free_list_which_implies_wit_1 : free_list_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct l_rest as [ | a l0].
  - simpl sll. Intros. tauto.
  - simpl sll. Intros. Intros y.
    Exists y a l0.
    split_pure_spatial.
    + cancel. reflexivity.
    + dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_map_list_entail_wit_1 : map_list_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (@nil Z) l.
  simpl sllseg.
  simpl app.
  simpl map_mult.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_map_list_entail_wit_2 : map_list_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (l1_2 ++ (p_data :: nil)) l2_new.
  split_pure_spatial.
  - sep_apply sllseg_len1; try easy.
    sep_apply (sllseg_sllseg head_pre).
    assert (H_eq: map_mult x_pre (l1_2 ++ p_data :: nil) = map_mult x_pre l1_2 ++ unsigned_last_nbits (x_pre * p_data) 32 :: nil).
    { unfold map_mult. rewrite map_app. simpl. reflexivity. }
    rewrite H_eq. cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity.
    rewrite PreH3, PreH1. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma proof_of_map_list_return_wit_1_split_goal_spatial :
  map_list_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst p.
  sep_apply sll_zero; try tauto.
  Intros. subst l2.
  sep_apply sllseg_0_sll.
  rewrite app_nil_r in PreH2. subst l. cancel.
Qed.

Lemma proof_of_map_list_return_wit_1 : map_list_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_map_list_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_map_list_which_implies_wit_1 : map_list_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct l2 as [ | a l0].
  - simpl sll. Intros. tauto.
  - simpl sll. Intros. Intros y.
    Exists y a l0.
    split_pure_spatial.
  + cancel (&(p # "sll" ->ₛ "data") # UInt |-> a).
    cancel (&(p # "sll" ->ₛ "next") # Ptr |-> y).
    cancel.
    + dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_cons_list_box_return_wit_1_split_goal_spatial :
  cons_list_box_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  simpl sll_pt.
  Intros.
  simpl sllbseg.
  Exists retval.
  subst pt_new_2.
  subst l.
  simpl sllbseg.
  normalize.
  split_pure_spatial.
  - cancel (&(retval # "sll" ->ₛ "data") # UInt |-> data_pre).
    cancel (&(box_pre # "sllb" ->ₛ "head") # Ptr |-> retval).
    reflexivity.
  - repeat split_pures; dump_pre_spatial; try assumption; reflexivity.
Qed.

Lemma proof_of_cons_list_box_return_wit_1 : cons_list_box_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cons_list_box_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cons_list_box_return_wit_2_split_goal_spatial :
  cons_list_box_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  simpl sll_pt.
  Intros.
  simpl sllbseg.
  Exists retval.
  subst pt_new_2.
  split_pure_spatial.
  - cancel (&(retval # "sll" ->ₛ "data") # UInt |-> data_pre).
    cancel (&(box_pre # "sllb" ->ₛ "head") # Ptr |-> retval).
    reflexivity.
  - dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cons_list_box_return_wit_2 : cons_list_box_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cons_list_box_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cons_list_box_which_implies_wit_1 : cons_list_box_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sllbseg_0_sll_pt (&(box # "sllb" ->ₛ"head")) pt l).
  Intros h.
  Exists h.
  cancel.
Qed. 

Lemma proof_of_app_list_box_return_wit_2_split_goal_spatial :
  app_list_box_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold sll_pt.
  destruct l2.
  + Intros. subst h2.
    rewrite app_nil_r.
    sep_apply (sllbseg_2_sllb b1_pre pt1 l1).
    cancel.
    assumption.
  + Intros. tauto.
Qed.

Lemma proof_of_app_list_box_return_wit_2 : app_list_box_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_app_list_box_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_app_list_box_return_wit_1_split_goal_spatial :
  app_list_box_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold sll_pt.
  destruct l2.
  + Intros. tauto.
  + Intros.
    clear H.
    assert (h2 <> 0) as H by exact PreH1.
    sep_apply (sllbseg_append_sllbseg (&(b1_pre # "sllb" ->ₛ"head")) pt1 l1 h2 pt2 z l2 H).
    sep_apply (sllbseg_2_sllb b1_pre pt2 (l1 ++ z :: l2) PreH2).
    cancel.
Qed.

Lemma proof_of_app_list_box_return_wit_1 : app_list_box_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_app_list_box_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_app_list_box_which_implies_wit_1 : app_list_box_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (sllb_2_sllbseg b1 l1).
  Intros pt1.
  sep_apply (sllb_2_sll_pt b2 l2).
  Intros h2 pt2.
  Exists pt2 h2 pt1.
  split_pure_spatial.
  - cancel (&(b2 # "sllb" ->ₛ "head") # Ptr |-> h2).
    cancel (&(b2 # "sllb" ->ₛ "ptail") # Ptr |-> pt2).
    cancel (&(b1 # "sllb" ->ₛ "ptail") # Ptr |-> pt1).
    cancel (sllbseg (&(b1 # "sllb" ->ₛ "head")) pt1 l1).
    cancel (sll_pt h2 pt2 l2).
    reflexivity.
  - repeat split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sll_length_entail_wit_1 : sll_length_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (@nil Z) l.
  simpl sllseg.
  simpl app.
  simpl Zlength.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try reflexivity; assumption.
Qed.

Lemma proof_of_sll_length_entail_wit_2 : sll_length_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (l1_2 ++ (head_data :: nil)) l3.
  simpl.
  split_pure_spatial.
  - sep_apply sllseg_len1.
    + sep_apply (sllseg_sllseg head_pre). cancel.
    + exact PreH5.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity.
    + rewrite PreH2, PreH1. rewrite <- app_assoc. simpl. reflexivity.
    + rewrite Zlength_app. rewrite Zlength_cons, Zlength_nil.
      rewrite PreH3.
      apply unsigned_last_nbits_eq.
      rewrite PreH2, PreH1 in PreH4.
      rewrite Zlength_app, Zlength_cons in PreH4.
      pose proof (Zlength_nonneg l1_2).
      pose proof (Zlength_nonneg l3). lia.
Qed.

Lemma proof_of_sll_length_return_wit_1_split_goal_1 :
  sll_length_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH4.
  assert (Hnull : (0 : addr) = NULL) by reflexivity.
  sep_apply (sll_zero 0 l2 Hnull).
  Intros_p Hl.
  subst l2.
  normalize.
  rewrite PreH1, app_nil_r.
  dump_pre_spatial.
  exact PreH2.
Qed.

Lemma proof_of_sll_length_return_wit_1_split_goal_spatial :
  sll_length_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH4.
  assert (Hnull : (0 : addr) = NULL) by reflexivity.
  sep_apply (sll_zero 0 l2 Hnull).
  Intros_p Hl.
  subst l2.
  normalize.
  rewrite PreH1, app_nil_r.
  sep_apply sllseg_0_sll.
  cancel.
Qed.

Lemma proof_of_sll_length_return_wit_1 : sll_length_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sll_length_return_wit_1_split_goal_spatial.
  Goal_apply proof_of_sll_length_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sll_length_which_implies_wit_1 : sll_length_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct l2 as [ | a l0].
  - simpl sll. Intros. tauto.
  - simpl sll. Intros. Intros x.
    Exists x a l0.
    split_pure_spatial.
    + cancel.
      reflexivity.
    + dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_sll2array_entail_wit_1_split_goal_1 :
  sll2array_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst retval.
  pose proof (Zlength_nonneg l).
  lia.
Qed.

Lemma proof_of_sll2array_entail_wit_1_split_goal_2 :
  sll2array_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_sll2array_entail_wit_1 : sll2array_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sll2array_entail_wit_1_split_goal_1.
  Goal_apply proof_of_sll2array_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_sll2array_entail_wit_2 : sll2array_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (l1_2 ++ p_data :: nil) l3.
  split_pure_spatial.
  - sep_apply sllseg_len1; try easy.
    sep_apply (sllseg_sllseg head_pre).
    cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity.
    + rewrite PreH3, PreH1. rewrite <- app_assoc. simpl. reflexivity.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_sll2array_return_wit_1_split_goal_spatial :
  sll2array_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst p.
  sep_apply sll_zero; try tauto.
  Intros. subst l2.
  rewrite app_nil_r in PreH1.
  subst l.
  sep_apply sllseg_0_sll.
  rewrite PreH2.
  rewrite PreH3.
  rewrite (UIntArray.undef_seg_empty arr (Zlength l1)).
  sep_apply (UIntArray.seg_shape_to_full_shape arr 0 (Zlength l1)).
  replace (arr + 0 * sizeof(UINT)) with arr by lia.
  replace (Zlength l1 - 0) with (Zlength l1) by lia.
  cancel.
Qed.

Lemma proof_of_sll2array_return_wit_1 : sll2array_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sll2array_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_sll2array_partial_solve_wit_3_pure : sll2array_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (sll_not_null_length p l2 PreH8).
  Intros.
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; try lia.
  rewrite PreH2.
  rewrite PreH3.
  rewrite PreH1.
  rewrite Zlength_app.
  lia.
Qed.

Lemma proof_of_sll2array_which_implies_wit_1 : sll2array_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct l2 as [ | a l0].
  - simpl sll. Intros. tauto.
  - simpl sll. Intros. Intros y.
    Exists y a l0.
    split_pure_spatial.
    + cancel (&(p # "sll" ->ₛ "data") # UInt |-> a).
      cancel (&(p # "sll" ->ₛ "next") # Ptr |-> y).
      cancel (sll y l0).
      cancel (sllseg head_pre p l1).
      reflexivity.
    + split_pures; dump_pre_spatial; try assumption; reflexivity.
Qed.
