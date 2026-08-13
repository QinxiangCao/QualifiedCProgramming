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
From SimpleC.EE.QCP_demos_LLM Require Import bst_delete_rec2_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From SimpleC.EE.QCP_demos_LLM Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_get_pre_return_wit_1 : get_pre_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst t_right.
  Exists retval_v_left_2. Exists retval_v_right_2.
  Exists ret_left_2. Exists (t_pt_2 ++ (RH t_key t_value t_left :: nil)).
  Exists retval_v_value_2. Exists retval_v_key_2. Exists retval_v_2.
  repeat (split_pure_spatial || split_pures).
  + cancel (retval # Ptr |-> retval_v_2).
    cancel (&(retval_v_2 # "tree" ->ₛ "key") # Int |-> retval_v_key_2).
    cancel (&(retval_v_2 # "tree" ->ₛ "value") # Int |-> retval_v_value_2).
    cancel (&(retval_v_2 # "tree" ->ₛ "right") # Ptr |-> retval_v_right_2).
    cancel (&(retval_v_2 # "tree" ->ₛ "left") # Ptr |-> retval_v_left_2).
    cancel (store_tree retval_v_left_2 ret_left_2).
    sep_apply_l_atomic (store_ptb_RH t_pre t_v_2 t_v_left t_key t_value t_left).
    * dump_pre_spatial. exact PreH9.
    * dump_pre_spatial. split; [exact PreH11 | exact PreH12].
    * sep_apply_l_atomic (store_ptb_app retval (&(t_v_2 # "tree" ->ₛ "right")) t_pre t_pt_2 (RH t_key t_value t_left :: nil)).
      cancel.
  + dump_pre_spatial. exact PreH1.
  + dump_pre_spatial. exact PreH2.
  + dump_pre_spatial. exact PreH3.
  + dump_pre_spatial. simpl. rewrite PreH4. reflexivity.
  + dump_pre_spatial. simpl. rewrite PreH5. reflexivity.
  + dump_pre_spatial. simpl. rewrite PreH6. reflexivity.
  + dump_pre_spatial. simpl. rewrite PreH7. reflexivity.
  + dump_pre_spatial. exact PreH8.
Qed.

Lemma proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (store_tree_zero t_pre_v_right t_right).
  * dump_pre_spatial. exact PreH1.
  * Intros_p Hright.
    Exists t_pre_v_left. Exists t_pre_v_right.
    Exists t_left. Exists (@nil half_tree).
    Exists t_value. Exists t_key. Exists t_pre_v.
    repeat (split_pure_spatial || split_pures).
    + cancel (t_pre # Ptr |-> t_pre_v).
      cancel (&(t_pre_v # "tree" ->ₛ "key") # Int |-> t_key).
      cancel (&(t_pre_v # "tree" ->ₛ "value") # Int |-> t_value).
      cancel (&(t_pre_v # "tree" ->ₛ "right") # Ptr |-> t_pre_v_right).
      simpl. split_pure_spatial.
      - cancel.
      - dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. subst t_right. simpl. reflexivity.
    + dump_pre_spatial. subst t_right. simpl. reflexivity.
    + dump_pre_spatial. subst t_right. simpl. reflexivity.
    + dump_pre_spatial. subst t_right. simpl. reflexivity.
    + dump_pre_spatial. exact PreH1.
Qed.

Lemma proof_of_get_pre_entail_wit_1 : get_pre_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct t_right as [| tree_l k_val v_val tree_r].
  - simpl. Intros_p Hzero. contradiction.
  - simpl. Intros pl. Intros pr.
    Exists pr. Exists pl. Exists t_pre_v_left. Exists tree_l. Exists tree_r.
    Exists v_val. Exists k_val. Exists t_pre_v_right. Exists t_pre_v.
    repeat (split_pure_spatial || split_pures).
    + cancel (t_pre # Ptr |-> t_pre_v).
      cancel (&(t_pre_v # "tree" ->ₛ "right") # Ptr |-> t_pre_v_right).
      cancel (&(t_pre_v # "tree" ->ₛ "key") # Int |-> t_key).
      cancel (&(t_pre_v # "tree" ->ₛ "value") # Int |-> t_value).
      cancel (&(t_pre_v # "tree" ->ₛ "left") # Ptr |-> t_pre_v_left).
      cancel (store_tree t_pre_v_left t_left).
      cancel (&(t_pre_v_right # "tree" ->ₛ "key") # Int |-> k_val).
      cancel (&(t_pre_v_right # "tree" ->ₛ "value") # Int |-> v_val).
      cancel (&(t_pre_v_right # "tree" ->ₛ "left") # Ptr |-> pl).
      cancel (store_tree pl tree_l).
      cancel (&(t_pre_v_right # "tree" ->ₛ "right") # Ptr |-> pr).
      cancel (store_tree pr tree_r).
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact (proj1 H0).
    + dump_pre_spatial. exact (proj2 H0).
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_delete_return_wit_2 : delete_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst p tr_low_level_spec.
  Exists b_v.
  assert (Hdel: tree_delete' x_pre (make_tree l0 p_key p_value r0)
        = make_tree (tree_delete' x_pre l0) p_key p_value r0).
  { simpl. destruct (Key.dec x_pre p_key) as [[Hlt | Hgt] | Heq]; try lia; reflexivity. }
  rewrite Hdel.
  cancel (b_pre # Ptr |-> b_v).
  sep_apply_l_atomic (store_tree_make_tree b_v p_key p_value b_callee_v p_right
    (tree_delete' x_pre l0) r0).
  - dump_pre_spatial. exact PreH3.
  - dump_pre_spatial. split; [exact PreH4 | exact PreH5].
  - cancel.
Qed.

Lemma proof_of_delete_return_wit_1 : delete_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (store_tree_zero b_pre_v_2 tr_low_level_spec).
  * dump_pre_spatial. exact PreH1.
  * Intros_p Htr.
    Exists 0.
    subst b_pre_v_2 tr_low_level_spec.
    cancel (b_pre # Ptr |-> 0).
    simpl.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_delete_return_wit_5 : delete_return_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst p tr_low_level_spec.
  subst y.
  subst l0.
  assert (x_pre = p_key) by lia.
  subst x_pre.
  Exists b_v.
  assert (Hdel:
    tree_delete' p_key
      (make_tree (make_tree l0_left p_l_k p_l_v r0_left) p_key p_value r0) =
    make_tree (combine_tree t_pt ret_left) retval_v_key retval_v_value r0).
  { simpl. destruct (Key.dec p_key p_key) as [[Hlt | Hgt] | Heq]; try lia.
    rewrite PreH4, PreH5, PreH6, PreH7. reflexivity. }
  rewrite Hdel.
  cancel (b_pre # Ptr |-> b_v).
  sep_apply_l_atomic (store_ptb_store_tree (&(b_v # "tree" ->ₛ "left"))
    retval retval_v_left t_pt ret_left).
  Intros p_root.
  sep_apply_l_atomic (store_tree_make_tree b_v retval_v_key retval_v_value
    p_root p_right (combine_tree t_pt ret_left) r0).
  - dump_pre_spatial. exact PreH10.
  - dump_pre_spatial. split; [exact PreH2 | exact PreH3].
  - cancel.
Qed.

Lemma proof_of_delete_return_wit_4 : delete_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst p tr_low_level_spec.
  sep_apply_l_atomic (store_tree_zero p_left l0).
  * dump_pre_spatial. exact PreH1.
  * Intros_p Hl0.
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

Lemma proof_of_delete_return_wit_3 : delete_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst p tr_low_level_spec.
  Exists b_v.
  assert (Hdel: tree_delete' x_pre (make_tree l0 p_key p_value r0)
        = make_tree l0 p_key p_value (tree_delete' x_pre r0)).
  { simpl. destruct (Key.dec x_pre p_key) as [[Hlt | Hgt] | Heq]; try lia; reflexivity. }
  rewrite Hdel.
  cancel (b_pre # Ptr |-> b_v).
  sep_apply_l_atomic (store_tree_make_tree b_v p_key p_value p_left b_callee_v
    l0 (tree_delete' x_pre r0)).
  - dump_pre_spatial. exact PreH4.
  - dump_pre_spatial. split; [exact PreH5 | exact PreH6].
  - cancel.
Qed.

Lemma proof_of_delete_entail_wit_1 : delete_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct tr_low_level_spec as [| tree_l k_val v_val tree_r].
  - simpl. Intros_p Hzero. contradiction.
  - simpl. Intros pl. Intros pr.
    Exists pr. Exists pl. Exists tree_l. Exists v_val. Exists tree_r. Exists k_val.
    Exists b_pre_v.
    repeat (split_pure_spatial || split_pures).
    + cancel (b_pre # Ptr |-> b_pre_v).
      cancel (&(b_pre_v # "tree" ->ₛ "key") # Int |-> k_val).
      cancel (&(b_pre_v # "tree" ->ₛ "value") # Int |-> v_val).
      cancel (&(b_pre_v # "tree" ->ₛ "left") # Ptr |-> pl).
      cancel (&(b_pre_v # "tree" ->ₛ "right") # Ptr |-> pr).
      cancel (store_tree pl tree_l).
      cancel (store_tree pr tree_r).
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact (proj1 H0).
    + dump_pre_spatial. exact (proj2 H0).
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_delete_entail_wit_2 : delete_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst p tr_low_level_spec.
  assert (x_pre = p_key) by lia.
  subst x_pre.
  destruct l0_2 as [| l0_left k_val v_val r0_left].
  - simpl. Intros_p Hzero. contradiction.
  - simpl. Intros pl. Intros pr.
    Exists pr. Exists pl. Exists l0_left. Exists r0_left.
    Exists v_val. Exists k_val.
    Exists p_left_2. Exists p_right_2. Exists (make_tree l0_left k_val v_val r0_left).
    Exists p_value_2. Exists r0_2. Exists p_key. Exists b_v_2.
    repeat (split_pure_spatial || split_pures).
    + cancel (b_pre # Ptr |-> b_v_2).
      cancel (&(b_v_2 # "tree" ->ₛ "key") # Int |-> p_key).
      cancel (&(b_v_2 # "tree" ->ₛ "value") # Int |-> p_value_2).
      cancel (&(b_v_2 # "tree" ->ₛ "right") # Ptr |-> p_right_2).
      cancel (store_tree p_right_2 r0_2).
      cancel (&(b_v_2 # "tree" ->ₛ "left") # Ptr |-> p_left_2).
      cancel (&(p_left_2 # "tree" ->ₛ "key") # Int |-> k_val).
      cancel (&(p_left_2 # "tree" ->ₛ "value") # Int |-> v_val).
      cancel (&(p_left_2 # "tree" ->ₛ "left") # Ptr |-> pl).
      cancel (store_tree pl l0_left).
      cancel (&(p_left_2 # "tree" ->ₛ "right") # Ptr |-> pr).
      cancel (store_tree pr r0_left).
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact (proj1 H0).
    + dump_pre_spatial. exact (proj2 H0).
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_delete_derive_high_level_spec_by_low_level_spec :
  delete_derive_high_level_spec_by_low_level_spec.
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
