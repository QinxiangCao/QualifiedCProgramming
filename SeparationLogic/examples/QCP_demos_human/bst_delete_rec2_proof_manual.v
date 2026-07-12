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
From SimpleC.EE.QCP_demos_human Require Import bst_delete_rec2_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From SimpleC.EE.QCP_demos_human Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_get_pre_return_wit_2_split_goal_1 : get_pre_return_wit_2_split_goal_1.
Proof.
  pre_process.
  sep_apply store_tree_zero ; try auto.
  Intros.
  dump_pre_spatial.
  rewrite H0.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_2_split_goal_2 : get_pre_return_wit_2_split_goal_2.
Proof.
  pre_process.
  sep_apply store_tree_zero ; try auto.
  Intros.
  dump_pre_spatial. 
  rewrite H0.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_2_split_goal_3 : get_pre_return_wit_2_split_goal_3.
Proof.
  pre_process.
  sep_apply store_tree_zero ; try auto.
  Intros.
  dump_pre_spatial. 
  rewrite H0.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_2_split_goal_4 : get_pre_return_wit_2_split_goal_4.
Proof.
  pre_process.
  sep_apply store_tree_zero ; try auto.
  Intros.
  dump_pre_spatial. 
  rewrite H0.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_2_split_goal_spatial : get_pre_return_wit_2_split_goal_spatial.
Proof.
  pre_process.
  sep_apply store_tree_zero ; try auto.
  entailer!.
Qed.

Lemma proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_get_pre_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_get_pre_return_wit_2_split_goal_1.
  - Goal_apply proof_of_get_pre_return_wit_2_split_goal_2.
  - Goal_apply proof_of_get_pre_return_wit_2_split_goal_3.
  - Goal_apply proof_of_get_pre_return_wit_2_split_goal_4.
Qed.

Lemma proof_of_get_pre_return_wit_1_split_goal_1 : get_pre_return_wit_1_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial. 
  rewrite PreH14.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_1_split_goal_2 : get_pre_return_wit_1_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial. 
  rewrite PreH14.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_1_split_goal_3 : get_pre_return_wit_1_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial. 
  rewrite PreH14.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_1_split_goal_spatial : get_pre_return_wit_1_split_goal_spatial.
Proof.
  pre_process.
  sep_apply (store_ptb_RH).
  sep_apply (store_ptb_app retval &( t_pre_v # "tree" ->ₛ "right") t_pre t_pt_2 (RH t_key t_value t_left :: nil)).
  rewrite PreH14. simpl. rewrite PreH9.
  entailer!.
  all :  tauto.
Qed.

Lemma proof_of_get_pre_return_wit_1 : get_pre_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_get_pre_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_get_pre_return_wit_1_split_goal_1.
  - Goal_apply proof_of_get_pre_return_wit_1_split_goal_2.
  - Goal_apply proof_of_get_pre_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_get_pre_which_implies_wit_1 : get_pre_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply store_tree_not_zero; try tauto.
  Intros l0 k0 v0 r0.
  Intros pl pr.
  Exists pr pl l0 r0.
  Exists v0 k0.
  entailer!.
Qed.

Lemma proof_of_delete_return_wit_1 : delete_return_wit_1.
Proof. 
  pre_process.
  Exists b_pre_v_2.
  entailer!.
  sep_apply (store_tree_zero); [ | tauto].
  entailer!.
  rewrite H0.
  simpl. 
  entailer!.
Qed.

Lemma proof_of_delete_return_wit_2 : delete_return_wit_2.
Proof.
  pre_process.
  Exists b_pre_v_2.
  entailer!.
  subst tr_low_level_spec.
  simpl.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?]; try Key.order.
  sep_apply store_tree_make_tree; try tauto.
  reflexivity.
Qed.

Lemma proof_of_delete_return_wit_3 : delete_return_wit_3.
Proof. 
  pre_process.
  Exists b_pre_v_2.
  entailer!.
  subst tr_low_level_spec.
  simpl.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?]; try Key.order.
  sep_apply store_tree_make_tree; try tauto.
  reflexivity.
Qed.

Lemma proof_of_delete_return_wit_4 : delete_return_wit_4.
Proof. 
  pre_process.
  Exists p_right.
  entailer!.
  sep_apply (store_tree_zero); [ | tauto].
  entailer!.
  assert (x_pre = p_key) by lia.
  subst x_pre tr_low_level_spec l0.
  simpl.
  destruct (Key.dec p_key p_key) as [[? | ?] | ?]; try lia.
  entailer!.
Qed.

Lemma proof_of_delete_return_wit_5 : delete_return_wit_5.
Proof. 
  pre_process.
  subst tr_low_level_spec l0.
  assert (x_pre = p_key) by lia.
  subst x_pre.
  Exists b_pre_v_2.
  assert (Hdel:
    tree_delete' p_key
      (make_tree (make_tree l0' p_l_k p_l_v r0') p_key p_value r0) =
    make_tree (combine_tree t_pt ret_left) retval_v_key retval_v_value r0).
  { simpl. destruct (Key.dec p_key p_key) as [[Hlt | Hgt] | Heq]; try lia.
    rewrite PreH4, PreH5, PreH6, PreH7. reflexivity. }
  rewrite Hdel.
  cancel (b_pre # Ptr |-> b_pre_v_2).
  sep_apply_l_atomic (store_ptb_store_tree (&(b_pre_v_2 # "tree" ->ₛ "left"))
    retval retval_v_left t_pt ret_left).
  Intros p_root.
  sep_apply_l_atomic (store_tree_make_tree b_pre_v_2 retval_v_key retval_v_value
    p_root p_right (combine_tree t_pt ret_left) r0).
  - dump_pre_spatial. exact PreH18.
  - dump_pre_spatial. split; [exact PreH2 | exact PreH3].
  - cancel.
Qed.

Lemma proof_of_delete_which_implies_wit_1 : delete_which_implies_wit_1.
Proof. 
  pre_process.
  sep_apply store_tree_not_zero; [ | tauto].
  Intros x k v r0. 
  Intros pl pr.
  Exists pr pl x v.
  Exists r0 k.
  entailer!.
Qed.

Lemma proof_of_delete_which_implies_wit_2 : delete_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply store_tree_not_zero; try tauto.
  Intros l1 k0 v0 r1.
  Intros pl pr.
  Exists pr pl l1 r1.
  Exists v0 k0.
  entailer!.
Qed.

Lemma proof_of_delete_derive_high_level_spec_by_low_level_spec : delete_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Intros b_pre_v.
  unfold Bst.store_map. Intros tr.
  Exists tr. 
  entailer!.
  Exists b_pre_v.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  Intros b_pre_v_4.
  Exists b_pre_v_4.
  entailer!.
  Exists (tree_delete' x_pre tr).
  entailer!.
  - apply delete'_Abs. tauto. tauto.
  - apply delete'_SearchTree. tauto.
Qed.
