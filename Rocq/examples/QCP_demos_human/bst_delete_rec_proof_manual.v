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
From SimpleC.EE.QCP_demos_human Require Import bst_delete_rec_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From SimpleC.EE.QCP_demos_human Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst t_right.
  destruct r0 as [| rl rk rv rr].
  - simpl store_tree.
    Exists t_left. Exists 0. Exists (@nil half_tree).
    Exists l0. Exists t_key. Exists t_value.
    repeat (split_pure_spatial || split_pures).
    + simpl store_pt.
      split_pure_spatial.
      * Intros_p Hzero.
        cancel (&(t_pre # "tree" ->ₛ "value") # Int |-> t_value).
        cancel (&(t_pre # "tree" ->ₛ "key") # Int |-> t_key).
        cancel (&(t_pre # "tree" ->ₛ "right") # Ptr |-> 0).
        cancel (&(t_pre # "tree" ->ₛ "left") # Ptr |-> t_left).
        cancel.
      * dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. subst tr. simpl. intros tr_ret_right. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
  - simpl store_tree.
    Intros pl pr.
    unfold NULL in H.
    lia.
Qed.

Lemma proof_of_get_pre_return_wit_1 : get_pre_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst tr.
  Exists retval_left_2. Exists retval_right_2.
  Exists (pt_2 ++ (RH t_key t_value l0 :: nil)).
  Exists tr_ret_left_2. Exists retval_key_2. Exists retval_value_2.
  repeat (split_pure_spatial || split_pures).
  + cancel (&(retval # "tree" ->ₛ "value") # Int |-> retval_value_2).
    cancel (&(retval # "tree" ->ₛ "key") # Int |-> retval_key_2).
    cancel (&(retval # "tree" ->ₛ "right") # Ptr |-> retval_right_2).
    cancel (&(retval # "tree" ->ₛ "left") # Ptr |-> retval_left_2).
    cancel (store_tree retval_left_2 tr_ret_left_2).
    sep_apply_l_atomic (store_pt_RH t_right t_pre t_left t_key t_value l0).
    * dump_pre_spatial. exact PreH10.
    * dump_pre_spatial. split; [exact PreH7 | exact PreH8].
    * sep_apply_l_atomic (store_pt_app retval t_right t_pre pt_2 (RH t_key t_value l0 :: nil)).
      cancel.
  + dump_pre_spatial. exact PreH1.
  + dump_pre_spatial.
    intros tr0.
    pose proof PreH2 tr0 as Hmerge.
    pose proof combine_tree_pt_assoc
      (RH t_key t_value l0 :: nil) pt_2
      (make_tree tr_ret_left_2 retval_key_2 retval_value_2 tr0) as Hassoc.
    rewrite <- Hassoc.
    transitivity (make_tree l0 t_key t_value (tree_pre_merge r0 tr0)); simpl.
    - destruct r0; simpl; reflexivity.
    - f_equal. exact Hmerge.
  + dump_pre_spatial. exact PreH3.
  + dump_pre_spatial. exact PreH4.
  + dump_pre_spatial. exact PreH5.
Qed.


Lemma proof_of_get_pre_which_implies_wit_1 : get_pre_which_implies_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_not_zero; [ | tauto].
  Intros x k v r0.
  Intros pl pr.
  Exists pr pl x v.
  Exists r0 k.
  split_pure_spatial.
  - cancel (&(t # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(t # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(t # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl x).
    cancel (&(t # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel.
  - split_pures.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      exact H0.
Qed.


Lemma proof_of_delete_return_wit_1 : delete_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst b_pre_v_2.
  destruct tr_low_level_spec as [| rl rk rv rr].
  - simpl store_tree.
    Exists 0.
    simpl.
    split_pure_spatial.
    + Intros_p Hzero. cancel.
    + dump_pre_spatial. reflexivity.
  - simpl store_tree.
    Intros pl pr.
    unfold NULL in H.
    lia.
Qed.

Lemma proof_of_delete_return_wit_2 : delete_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst tr_low_level_spec.
  Exists b_pre_v_2.
  assert (Hdel: tree_delete x_pre (make_tree l0 p_key p_value r0)
        = make_tree (tree_delete x_pre l0) p_key p_value r0).
  { simpl. destruct (Key.dec x_pre p_key) as [[Hlt | Hgt] | Heq]; try lia; reflexivity. }
  rewrite Hdel.
  cancel (b_pre # Ptr |-> b_pre_v_2).
  sep_apply_l_atomic (store_tree_make_tree b_pre_v_2 p_key p_value b_callee_v p_right
    (tree_delete x_pre l0) r0).
  - dump_pre_spatial. exact PreH5.
  - dump_pre_spatial. split; [exact PreH2 | exact PreH3].
  - cancel.
Qed.

Lemma proof_of_delete_return_wit_3 : delete_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst tr_low_level_spec.
  Exists b_pre_v_2.
  assert (Hdel: tree_delete x_pre (make_tree l0 p_key p_value r0)
        = make_tree l0 p_key p_value (tree_delete x_pre r0)).
  { simpl. destruct (Key.dec x_pre p_key) as [[Hlt | Hgt] | Heq]; try lia; reflexivity. }
  rewrite Hdel.
  cancel (b_pre # Ptr |-> b_pre_v_2).
  sep_apply_l_atomic (store_tree_make_tree b_pre_v_2 p_key p_value p_left b_callee_v
    l0 (tree_delete x_pre r0)).
  - dump_pre_spatial. exact PreH6.
  - dump_pre_spatial. split; [exact PreH3 | exact PreH4].
  - cancel.
Qed.

Lemma proof_of_delete_return_wit_4 : delete_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst tr_low_level_spec.
  Exists p_right.
  cancel (b_pre # Ptr |-> p_right).
  sep_apply (store_tree_zero p_left l0); [ | tauto].
  Intros_p Hl0.
    assert (x_pre = p_key) by lia.
    subst x_pre.
    simpl.
    destruct (Key.dec p_key p_key) as [[Hlt | Hgt] | Heq]; try lia.
    rewrite Hl0.
    simpl.
    cancel.
Qed.

Lemma proof_of_delete_return_wit_5 : delete_return_wit_5.
Proof. 
  LLM_pre_process ltac:(int_auto).
  assert (x_pre = p_key) by lia.
  subst x_pre.
  Exists p_left.
  assert (Hdel: tree_delete p_key (make_tree l0 p_key p_value r0) = tree_pre_merge l0 r0).
  { simpl. destruct (Key.dec p_key p_key) as [[Hlt | Hgt] | Heq].
    - lia.
    - lia.
    - reflexivity.
  }
  rewrite PreH11, Hdel.
  assert (Hmerge: tree_pre_merge l0 r0 =
    combine_tree pt0 (make_tree tr_ret_left retval_key retval_value r0)).
  { apply PreH2. }
  rewrite Hmerge.
  cancel (b_pre # Ptr |-> p_left).
  sep_apply_l_atomic (store_tree_make_tree retval retval_key retval_value
    retval_left p_right tr_ret_left r0).
  - dump_pre_spatial. exact PreH1.
  - dump_pre_spatial. split; [exact PreH4 | exact PreH5].
  - sep_apply_l_atomic (store_combine p_left retval pt0
      (make_tree tr_ret_left retval_key retval_value r0)).
    cancel.
Qed.

Lemma proof_of_delete_which_implies_wit_1 : delete_which_implies_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_not_zero; [ | tauto].
  Intros x k v r0. 
  Intros pl pr.
  Exists pr pl x v.
  Exists r0 k.
  split_pure_spatial.
  - cancel (&(p # "tree" ->ₛ "key") # Int |-> k).
    cancel (&(p # "tree" ->ₛ "value") # Int |-> v).
    cancel (&(p # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl x).
    cancel (&(p # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pr r0).
  - split_pures.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      exact H0.
Qed.

Lemma proof_of_delete_derive_high_level_spec_by_low_level_spec : delete_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Intros b_pre_v.
  unfold Bst.store_map.
  Intros tr.
  Exists tr.
  Exists b_pre_v.
  split_pure_spatial.
  - cancel (store_tree b_pre_v tr).
    cancel (b_pre # Ptr |-> b_pre_v).
    apply derivable1_wand_sepcon_adjoint.
    Intros b_callee_v_2.
    Exists b_callee_v_2.
    unfold Bst.store_map.
    Exists (tree_delete x_pre tr).
    repeat (split_pure_spatial || split_pures).
    + cancel (b_pre # Ptr |-> b_callee_v_2).
      cancel (store_tree b_callee_v_2 (tree_delete x_pre tr)).
    + dump_pre_spatial.
      apply delete_SearchTree.
      exact H1.
    + dump_pre_spatial.
      apply delete_Abs; assumption.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact H0.
Qed.
