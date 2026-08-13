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
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_zero ; try auto.
  Intros.
  dump_pre_spatial.
  rewrite H0.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_2_split_goal_2 : get_pre_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_zero ; try auto.
  Intros.
  dump_pre_spatial. 
  rewrite H0.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_2_split_goal_3 : get_pre_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_zero ; try auto.
  Intros.
  dump_pre_spatial. 
  rewrite H0.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_2_split_goal_4 : get_pre_return_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_zero ; try auto.
  Intros.
  dump_pre_spatial. 
  rewrite H0.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_2_split_goal_spatial : get_pre_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst t_pre_v_right.
  destruct t_right as [| rl rk rv rr].
  - simpl store_tree.
    Intros_p Hzero.
    cancel.
  - simpl store_tree.
    Intros pl pr.
    unfold NULL in H.
    lia.
Qed.

Lemma proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Proof.
  aggressive_pre_process.
  - sep_apply (proof_of_get_pre_return_wit_2_split_goal_spatial
      t_right t_key t_pre_v t_pre_v_right PreH1 PreH2 PreH3 PreH4).
    Intros.
    cancel.
  - Goal_apply proof_of_get_pre_return_wit_2_split_goal_1.
  - Goal_apply proof_of_get_pre_return_wit_2_split_goal_2.
  - Goal_apply proof_of_get_pre_return_wit_2_split_goal_3.
  - Goal_apply proof_of_get_pre_return_wit_2_split_goal_4.
Qed.

Lemma proof_of_get_pre_return_wit_1_split_goal_1 : get_pre_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial. 
  rewrite PreH14.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_1_split_goal_2 : get_pre_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial. 
  rewrite PreH14.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_1_split_goal_3 : get_pre_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial. 
  rewrite PreH14.
  simpl. tauto.
Qed.

Lemma proof_of_get_pre_return_wit_1_split_goal_spatial : get_pre_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (store_ptb_RH).
  sep_apply (store_ptb_app retval &( t_pre_v # "tree" ->ₛ "right") t_pre t_pt_2 (RH t_key t_value t_left :: nil)).
  rewrite PreH14. simpl. rewrite PreH9.
  cancel.
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
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_not_zero; try tauto.
  Intros l0 k0 v0 r0.
  Intros pl pr.
  Exists pr pl l0 r0.
  Exists v0 k0.
  split_pure_spatial.
  - cancel (t # Ptr |-> t_v_2).
    cancel (&(t_v_2 # "tree" ->ₛ "right") # Ptr |-> t_v_right).
    cancel (&(t_v_right # "tree" ->ₛ "key") # Int |-> k0).
    cancel (&(t_v_right # "tree" ->ₛ "value") # Int |-> v0).
    cancel (&(t_v_right # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl l0).
    cancel (&(t_v_right # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pr r0).
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
    Intros_p Hzero.
    simpl.
    split_pure_spatial.
    + cancel.
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
  assert (Hdel: tree_delete' x_pre (make_tree l0 p_key p_value r0)
        = make_tree (tree_delete' x_pre l0) p_key p_value r0).
  { simpl. destruct (Key.dec x_pre p_key) as [[Hlt | Hgt] | Heq]; try lia; reflexivity. }
  rewrite Hdel.
  cancel (b_pre # Ptr |-> b_pre_v_2).
  sep_apply_l_atomic (store_tree_make_tree b_pre_v_2 p_key p_value b_callee_v p_right
    (tree_delete' x_pre l0) r0).
  - dump_pre_spatial. exact PreH5.
  - dump_pre_spatial. split; [exact PreH2 | exact PreH3].
  - cancel.
Qed.

Lemma proof_of_delete_return_wit_3 : delete_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst tr_low_level_spec.
  Exists b_pre_v_2.
  assert (Hdel: tree_delete' x_pre (make_tree l0 p_key p_value r0)
        = make_tree l0 p_key p_value (tree_delete' x_pre r0)).
  { simpl. destruct (Key.dec x_pre p_key) as [[Hlt | Hgt] | Heq]; try lia; reflexivity. }
  rewrite Hdel.
  cancel (b_pre # Ptr |-> b_pre_v_2).
  sep_apply_l_atomic (store_tree_make_tree b_pre_v_2 p_key p_value p_left b_callee_v
    l0 (tree_delete' x_pre r0)).
  - dump_pre_spatial. exact PreH6.
  - dump_pre_spatial. split; [exact PreH3 | exact PreH4].
  - cancel.
Qed.

Lemma proof_of_delete_return_wit_4 : delete_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst tr_low_level_spec.
  sep_apply (store_tree_zero p_left l0); [ | tauto].
  Intros_p Hl0.
  assert (x_pre = p_key) by lia.
  subst x_pre.
  Exists p_right.
  assert (Hdel: tree_delete' p_key (make_tree l0 p_key p_value r0) = r0).
  { simpl. destruct (Key.dec p_key p_key) as [[Hlt | Hgt] | Heq]; try lia.
    subst l0. simpl. reflexivity.
  }
  rewrite Hdel.
  cancel (b_pre # Ptr |-> p_right).
  cancel (store_tree p_right r0).
Qed.

Lemma proof_of_delete_return_wit_5 : delete_return_wit_5.
Proof. 
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_delete_which_implies_wit_2 : delete_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_not_zero; try tauto.
  Intros l1 k0 v0 r1.
  Intros pl pr.
  Exists pr pl l1 r1.
  Exists v0 k0.
  split_pure_spatial.
  - cancel (&(p # "tree" ->ₛ "left") # Ptr |-> p_left).
    cancel (&(p_left # "tree" ->ₛ "key") # Int |-> k0).
    cancel (&(p_left # "tree" ->ₛ "value") # Int |-> v0).
    cancel (&(p_left # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl l1).
    cancel (&(p_left # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pr r1).
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
    Exists (tree_delete' x_pre tr).
    repeat (split_pure_spatial || split_pures).
    + cancel (b_pre # Ptr |-> b_callee_v_2).
      cancel (store_tree b_callee_v_2 (tree_delete' x_pre tr)).
    + dump_pre_spatial.
      apply delete'_SearchTree.
      exact H1.
    + dump_pre_spatial.
      apply delete'_Abs; assumption.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact H0.
Qed.
