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
From SimpleC.EE.QCP_demos_human Require Import bst_fp_delete_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import bst_fp_lib.
Local Open Scope sac.

Lemma proof_of_replace_min_entail_wit_1 : replace_min_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists b_pre_v.
	Exists nil.
	Exists tr.
	simpl.
	split_pure_spatial.
	- repeat cancel.
	- split_pures.
	  + dump_pre_spatial.
	    reflexivity.
	  + dump_pre_spatial.
	    reflexivity.
	  + dump_pre_spatial.
	    reflexivity.
	  + dump_pre_spatial.
	    exact PreH4.
	  + dump_pre_spatial.
	    reflexivity.
	  + dump_pre_spatial.
	    exact PreH1.
	  + dump_pre_spatial.
	    exact PreH2.
	  + dump_pre_spatial.
	    exact PreH3.
	  + dump_pre_spatial.
	    exact PreH4.
	  + dump_pre_spatial.
	    reflexivity.
	  + dump_pre_spatial.
	    reflexivity.
Qed.

Lemma proof_of_replace_min_entail_wit_2 : replace_min_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply (store_tree_not_zero b_v_left b_v_2 l0);
	  [ | exact PreH1 ].
	Intros l1.
	  Intros k0.
	  Intros v0.
	  Intros r1.
	  Intros b_v_left_left.
	  Intros b_v_left_right.
	  sep_apply (store_ptb_LH b b_v_2 b_v_right fa b_v_key b_v_value r0);
	    [ | lia | exact PreH8 ].
	  sep_apply store_ptb_app.
	  Exists b_v_left.
	  Exists (LH b_v_key b_v_value r0 :: pt0_2).
	  Exists (make_tree l1 k0 v0 r1).
	  split_pure_spatial.
	  + sep_apply_l_atomic (store_tree_make_tree b_v_left k0 v0
	      b_v_left_left b_v_left_right b_v_2 l1 r1).
	    * dump_pre_spatial.
	      exact H2.
	    * dump_pre_spatial.
	      lia.
	    * change ((LH b_v_key b_v_value r0 :: nil) ++ pt0_2) with
	        (LH b_v_key b_v_value r0 :: pt0_2).
	      cancel (&((b_v_2)  # "tree" ->ₛ "left") # Ptr |-> b_v_left).
	      cancel (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2
	        ptr_pre (LH b_v_key b_v_value r0 :: pt0_2)).
	      cancel (store_tree b_v_left b_v_2 (make_tree l1 k0 v0 r1)).
	      cancel (&((ptr_pre)  # "tree" ->ₛ "key") # Int |-> k).
	      cancel (&((ptr_pre)  # "tree" ->ₛ "value") # Int |-> v).
	  + split_pures.
	    * dump_pre_spatial.
	      rewrite PreH5, PreH4, H0.
	      simpl.
	      reflexivity.
	    * dump_pre_spatial.
	      rewrite PreH6, PreH4, H0.
	      simpl.
	      reflexivity.
	    * dump_pre_spatial.
	      rewrite PreH7, PreH4, H0.
	      simpl.
	      reflexivity.
	    * dump_pre_spatial.
	      exact PreH1.
	    * dump_pre_spatial.
	      rewrite PreH9, PreH4, H0.
	      simpl.
	      reflexivity.
	    * dump_pre_spatial.
	      exact PreH10.
	    * dump_pre_spatial.
	      exact PreH11.
	    * dump_pre_spatial.
	      exact PreH12.
	    * dump_pre_spatial.
	      exact PreH13.
Qed.

Lemma proof_of_replace_min_return_wit_1 : replace_min_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply (store_tree_make_tree b_v_right b_v_right_key b_v_right_value
	  b_v_right_left b_v_right_right fa l0_2 r0_2);
	  [ | lia | exact PreH4 ].
	rewrite <- PreH3.
	sep_apply (store_tree_zero b_v_left b_v l0);
	  [ | exact PreH5 ].
	Intros_p Hempty.
	sep_apply store_ptb_store_tree.
	Intros p_root.
	Exists p_root.
	Exists b_v_value.
	Exists b_v_key.
	rewrite PreH13.
	rewrite PreH8.
	rewrite Hempty.
	simpl.
	repeat (split_pure_spatial || split_pures).
	* cancel (&((ptr_pre)  # "tree" ->ₛ "key") # Int |-> b_v_key).
	  cancel (&((ptr_pre)  # "tree" ->ₛ "value") # Int |-> b_v_value).
	  cancel (b_pre # Ptr |-> p_root).
	  cancel (store_tree p_root ptr_pre (combine_tree pt0 r0)).
	* dump_pre_spatial.
	  rewrite PreH10, PreH8, Hempty.
	  simpl.
	  reflexivity.
	* dump_pre_spatial.
	  rewrite PreH11, PreH8, Hempty.
	  simpl.
	  reflexivity.
	* dump_pre_spatial.
	  exact PreH6.
	* dump_pre_spatial.
	  exact PreH7.
Qed.

Lemma proof_of_replace_min_return_wit_2 : replace_min_return_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (store_tree_zero b_v_right b_v r0).
	- dump_pre_spatial.
	  tauto.
	- Intros_p Hr0empty.
	  rewrite PreH1.
	  sep_apply_l_atomic (store_tree_zero b_v_left b_v l0).
	  {
	    dump_pre_spatial.
	    tauto.
	  }
	  Intros_p Hl0empty.
	  assert (Hb : (b # Ptr |-> 0) |-- (b # Ptr |-> 0 ** store_tree 0 fa empty)).
	  {
	    simpl.
	    repeat (split_pure_spatial || split_pures).
	    - cancel.
	    - dump_pre_spatial.
	      reflexivity.
	  }
	  sep_apply Hb.
	  sep_apply store_ptb_store_tree.
	  Intros p_root.
	  Exists p_root.
	  Exists b_v_value.
	  Exists b_v_key.
	  rewrite PreH10.
	  rewrite PreH5.
	  rewrite Hl0empty in *.
	  rewrite Hr0empty in *.
	  simpl in *.
	  repeat (split_pure_spatial || split_pures).
	  + cancel (&((ptr_pre)  # "tree" ->ₛ "key") # Int |-> b_v_key).
	    cancel (&((ptr_pre)  # "tree" ->ₛ "value") # Int |-> b_v_value).
	    cancel (b_pre # Ptr |-> p_root).
	    cancel (store_tree p_root ptr_pre (combine_tree pt0 empty)).
	  + dump_pre_spatial.
	    symmetry.
	    rewrite PreH7.
	    rewrite PreH5.
	    simpl.
	    reflexivity.
	  + dump_pre_spatial.
	    symmetry.
	    rewrite PreH8.
	    rewrite PreH5.
	    simpl.
	    reflexivity.
	  + dump_pre_spatial.
	    exact PreH3.
	  + dump_pre_spatial.
	    exact PreH4.
Qed.

Lemma proof_of_replace_min_which_implies_wit_1 : replace_min_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_not_zero; [ | try tauto .. ].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  split_pure_spatial.
  - cancel (b # Ptr |-> b_v).
    cancel (&((b_v)  # "tree" ->ₛ "key") # Int |-> k).
    cancel (&((b_v)  # "tree" ->ₛ "father") # Ptr |-> fa).
    cancel (&((b_v)  # "tree" ->ₛ "value") # Int |-> v).
    cancel (&((b_v)  # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl b_v l0).
    cancel (&((b_v)  # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pr b_v r0).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact H0.
Qed.

Lemma proof_of_replace_min_which_implies_wit_2 : replace_min_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  cancel.
  sep_apply store_tree_not_zero; [ | try tauto .. ].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  split_pure_spatial.
  - cancel (b # Ptr |-> b_v).
    cancel (&((b_v)  # "tree" ->ₛ "right") # Ptr |-> b_v_right).
    cancel (&((b_v_right)  # "tree" ->ₛ "key") # Int |-> k).
    cancel (&((b_v_right)  # "tree" ->ₛ "value") # Int |-> v).
    cancel (&((b_v_right)  # "tree" ->ₛ "father") # Ptr |-> b_v).
    cancel (&((b_v_right)  # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl b_v_right l0).
    cancel (&((b_v_right)  # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pr b_v_right r0).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact H0.
Qed.

Lemma proof_of_Delete_entail_wit_1 : Delete_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists b_pre_v.
	Exists nil.
	Exists tr_low_level_spec.
	split_pure_spatial.
	- simpl.
	  cancel (b_pre # Ptr |-> b_pre_v).
	  cancel (store_tree b_pre_v 0 tr_low_level_spec).
	  split_pure_spatial.
	  + cancel.
	  + split_pures.
	    * dump_pre_spatial.
	      simpl.
	      reflexivity.
	    * dump_pre_spatial.
	      simpl.
	      reflexivity.
	- split_pures.
	  + dump_pre_spatial.
	    simpl.
	    reflexivity.
	  + dump_pre_spatial.
	    exact PreH1.
	  + dump_pre_spatial.
	    exact PreH2.
Qed.

Lemma proof_of_Delete_entail_wit_2_1 : Delete_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (store_ptb_LH b b_v_2); [ | try tauto .. ].
  sep_apply store_ptb_app.
  Exists
    b_v_left
    (LH b_v_key b_v_value r0 :: pt0_2)
    l0.
  split_pure_spatial.
  - change ((LH b_v_key b_v_value r0 :: nil) ++ pt0_2) with
      (LH b_v_key b_v_value r0 :: pt0_2).
    cancel (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 0
      (LH b_v_key b_v_value r0 :: pt0_2)).
    cancel (&((b_v_2)  # "tree" ->ₛ "left") # Ptr |-> b_v_left).
    cancel (store_tree b_v_left b_v_2 l0).
  - split_pures.
    + dump_pre_spatial.
      rewrite <- PreH6.
      rewrite PreH4.
      simpl.
      f_equal.
      destruct (Key.dec x_pre b_v_key) as [[? | ?] | ?];
        first [reflexivity | Key.order].
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
Qed.

Lemma proof_of_Delete_entail_wit_2_2 : Delete_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (store_ptb_RH b b_v_2); [ | try tauto .. ].
  sep_apply store_ptb_app.
  Exists
    b_v_right
    (RH b_v_key b_v_value l0 :: pt0_2)
    r0.
  split_pure_spatial.
  - change ((RH b_v_key b_v_value l0 :: nil) ++ pt0_2) with
      (RH b_v_key b_v_value l0 :: pt0_2).
    cancel (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre b_v_2 0
      (RH b_v_key b_v_value l0 :: pt0_2)).
    cancel (&((b_v_2)  # "tree" ->ₛ "right") # Ptr |-> b_v_right).
    cancel (store_tree b_v_right b_v_2 r0).
  - split_pures.
    + dump_pre_spatial.
      rewrite <- PreH7.
      rewrite PreH5.
      simpl.
      f_equal.
      destruct (Key.dec x_pre b_v_key) as [[? | ?] | ?];
        first [reflexivity | Key.order].
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
Qed.

Lemma proof_of_Delete_return_wit_4 : Delete_return_wit_4.
Proof.
	LLM_pre_process ltac:(int_auto).
	assert (Hleft_key : INT_MIN <= b_v_left_key <= INT_MAX) by lia.
	sep_apply_l_atomic (store_tree_make_tree b_v_left b_v_left_key b_v_left_value b_v_left_left b_v_left_right fa l0_2 r0_2).
	- dump_pre_spatial.
	  try exact PreH4; exact PreH7.
	- dump_pre_spatial.
	  exact Hleft_key.
	- sep_apply_l_atomic (store_tree_zero b_v_right b_v r0).
	  + dump_pre_spatial.
	    try exact PreH5; exact PreH8.
	  + Intros_p Hempty.
	    sep_apply store_ptb_store_tree.
	    Intros p_root.
	    Exists p_root.
	    match goal with
	    | H : combine_tree pt0 (tree_delete x_pre tr0) = tree_delete x_pre tr_low_level_spec |- _ =>
	        rewrite <- H
	    end.
	    match goal with
	    | H : tr0 = make_tree l0 b_v_key b_v_value r0 |- _ => rewrite H
	    end.
	    match goal with
	    | H : l0 = make_tree l0_2 b_v_left_key b_v_left_value r0_2 |- _ => rewrite H
	    end.
	    assert (Heqkey : x_pre = b_v_key) by lia.
	    subst x_pre.
	    rewrite Hempty.
	    unfold tree_delete.
	    destruct (Key.dec b_v_key b_v_key) as [[Hlt | Hgt] | Heq].
	    * exfalso.
	      Key.order.
	    * exfalso.
	      Key.order.
	    * simpl.
	      cancel.
Qed.

Lemma proof_of_Delete_return_wit_5 : Delete_return_wit_5.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (store_tree_zero b_v_right b_v r0).
	- dump_pre_spatial.
	  exact PreH2.
	- Intros_p Hempty_r.
	  sep_apply_l_atomic (store_tree_zero b_v_left b_v l0).
	  + dump_pre_spatial.
	    exact PreH1.
	  + Intros_p Hempty_l.
	    rewrite PreH1.
	    assert (Hb : (b # Ptr |-> 0) |-- (b # Ptr |-> 0 ** store_tree 0 fa empty)).
	    {
	      simpl.
	      repeat (split_pure_spatial || split_pures).
	      - cancel (b # Ptr |-> 0).
	      - dump_pre_spatial.
	        reflexivity.
	    }
	    sep_apply Hb.
	    sep_apply store_ptb_store_tree.
	    Intros p_root.
	    Exists p_root.
	    match goal with
	    | H : combine_tree pt0 (tree_delete x_pre tr0) = tree_delete x_pre tr_low_level_spec |- _ =>
	        rewrite <- H
	    end.
	    match goal with
	    | H : tr0 = make_tree l0 b_v_key b_v_value r0 |- _ => rewrite H
	    end.
	    assert (Heqkey : x_pre = b_v_key) by lia.
	    subst x_pre.
	    rewrite Hempty_l.
	    rewrite Hempty_r.
	    unfold tree_delete.
	    destruct (Key.dec b_v_key b_v_key) as [[Hlt | Hgt] | Heq].
	    * exfalso.
	      Key.order.
	    * exfalso.
	      Key.order.
	    * simpl.
	      cancel.
Qed.

Lemma proof_of_Delete_return_wit_3 : Delete_return_wit_3.
Proof.
	LLM_pre_process ltac:(int_auto).
	assert (Hright_key : INT_MIN <= b_v_right_key <= INT_MAX) by lia.
	sep_apply_l_atomic (store_tree_make_tree b_v_right b_v_right_key b_v_right_value b_v_right_left b_v_right_right fa l0_2 r0_2).
	- dump_pre_spatial.
	  try exact PreH4; try exact PreH7; exact PreH9.
	- dump_pre_spatial.
	  exact Hright_key.
	- sep_apply_l_atomic (store_tree_zero b_v_left b_v l0).
	  + dump_pre_spatial.
	    try exact PreH5; exact PreH8.
	  + Intros_p Hempty.
	    sep_apply store_ptb_store_tree.
	    Intros p_root.
	    Exists p_root.
	    match goal with
	    | H : combine_tree pt0 (tree_delete x_pre tr0) = tree_delete x_pre tr_low_level_spec |- _ =>
	        rewrite <- H
	    end.
	    match goal with
	    | H : tr0 = make_tree l0 b_v_key b_v_value r0 |- _ => rewrite H
	    end.
	    match goal with
	    | H : r0 = make_tree l0_2 b_v_right_key b_v_right_value r0_2 |- _ => rewrite H
	    end.
	    assert (Heqkey : x_pre = b_v_key) by lia.
	    subst x_pre.
	    rewrite Hempty.
	    unfold tree_delete.
	    destruct (Key.dec b_v_key b_v_key) as [[Hlt | Hgt] | Heq].
	    * exfalso.
	      Key.order.
	    * exfalso.
	      Key.order.
	    * simpl.
	      cancel.
Qed.

Lemma proof_of_Delete_return_wit_2 : Delete_return_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	assert (Hkey : INT_MIN <= ptr_callee_key <= INT_MAX) by lia.
	sep_apply (store_tree_not_zero b_v_left b_v l0);
	  [ | try exact PreH8; exact PreH11 ].
	Intros l_left.
	Intros k_left.
	Intros v_left.
	Intros r_left.
	Intros p_left_left.
	Intros p_left_right.
	sep_apply_l_atomic (store_tree_make_tree b_v_left k_left v_left
	  p_left_left p_left_right b_v l_left r_left).
	- dump_pre_spatial.
	  try exact H2; lia.
	- dump_pre_spatial.
	  lia.
	-
	sep_apply_l_atomic (store_tree_make_tree b_v ptr_callee_key ptr_callee_value
	  b_v_left b_callee_v fa (make_tree l_left k_left v_left r_left)
	  (delete_min (make_tree l0_2 b_v_right_key b_v_right_value r0_2))).
	+ dump_pre_spatial.
	  try exact PreH15; exact PreH18.
	+ dump_pre_spatial.
	  exact Hkey.
	+ sep_apply store_ptb_store_tree.
	  Intros p_root.
	  Exists p_root.
	  assert (Hcombine_delete : combine_tree pt0
	    (make_tree (make_tree l_left k_left v_left r_left)
	      ptr_callee_key ptr_callee_value
	      (delete_min (make_tree l0_2 b_v_right_key b_v_right_value r0_2))) =
	    tree_delete x_pre tr_low_level_spec).
	  {
		match goal with
		| H : combine_tree pt0 (tree_delete x_pre tr0) =
		    tree_delete x_pre tr_low_level_spec |- _ => rewrite <- H
		end.
		match goal with
		| H : tr0 = make_tree l0 b_v_key b_v_value r0 |- _ => rewrite H
		end.
		match goal with
		| H : l0 = make_tree l_left k_left v_left r_left |- _ => rewrite H
		end.
		assert (Heqkey : x_pre = b_v_key) by lia.
		subst x_pre.
		match goal with
		| H : r0 = make_tree l0_2 b_v_right_key b_v_right_value r0_2 |- _ =>
		    rewrite H
		end.
		unfold tree_delete.
		destruct (Key.dec b_v_key b_v_key) as [[Hlt | Hgt] | Heq].
		+ exfalso.
		Key.order.
		+ exfalso.
		Key.order.
		+ simpl.
		  match goal with
		  | H : ptr_callee_key =
		      min_key b_v_key (make_tree l0_2 b_v_right_key b_v_right_value r0_2)
		    |- _ => rewrite H
		  end.
		  match goal with
		  | H : ptr_callee_value =
		      min_value b_v_value (make_tree l0_2 b_v_right_key b_v_right_value r0_2)
		    |- _ => rewrite H
		  end.
		  reflexivity.
	  }
	  rewrite Hcombine_delete.
	  cancel.
Qed.

Lemma proof_of_Delete_return_wit_1 : Delete_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply (store_tree_zero b_v fa tr0 PreH1).
	Intros_p Htr0.
	assert (Hb : (b # Ptr |-> b_v) |-- (b # Ptr |-> b_v ** store_tree b_v fa tr0)).
	{
	  rewrite PreH1.
	  rewrite Htr0.
	  simpl.
	  split_pure_spatial.
	  - cancel.
	  - dump_pre_spatial.
	    unfold NULL.
	    reflexivity.
	}
	sep_apply Hb.
	sep_apply store_ptb_store_tree.
	Intros p_root.
	Exists p_root.
	rewrite <- PreH2.
	rewrite Htr0.
	simpl.
	cancel.
Qed.

Lemma proof_of_Delete_which_implies_wit_1 : Delete_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_not_zero; [ | try tauto].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  split_pure_spatial.
  - try cancel (b # Ptr |-> b_v).
    cancel (&((b_v)  # "tree" ->ₛ "key") # Int |-> k).
    cancel (&((b_v)  # "tree" ->ₛ "father") # Ptr |-> fa).
    cancel (&((b_v)  # "tree" ->ₛ "value") # Int |-> v).
    cancel (&((b_v)  # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl b_v l0).
    cancel (&((b_v)  # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pr b_v r0).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact H0.
Qed.

Lemma proof_of_Delete_which_implies_wit_2 : Delete_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_not_zero; [ | try tauto].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  split_pure_spatial.
  - try cancel (b # Ptr |-> b_v).
    try cancel (&((b_v)  # "tree" ->ₛ "left") # Ptr |-> b_v_left).
    cancel (&((b_v_left)  # "tree" ->ₛ "key") # Int |-> k).
    cancel (&((b_v_left)  # "tree" ->ₛ "father") # Ptr |-> b_v).
    cancel (&((b_v_left)  # "tree" ->ₛ "value") # Int |-> v).
    cancel (&((b_v_left)  # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl b_v_left l0).
    cancel (&((b_v_left)  # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pr b_v_left r0).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact H0.
Qed.

Lemma proof_of_Delete_which_implies_wit_3 : Delete_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_not_zero; [ | try tauto].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  split_pure_spatial.
  - try cancel (b # Ptr |-> b_v).
    try cancel (&((b_v)  # "tree" ->ₛ "right") # Ptr |-> b_v_right).
    cancel (&((b_v_right)  # "tree" ->ₛ "key") # Int |-> k).
    cancel (&((b_v_right)  # "tree" ->ₛ "father") # Ptr |-> b_v).
    cancel (&((b_v_right)  # "tree" ->ₛ "value") # Int |-> v).
    cancel (&((b_v_right)  # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl b_v_right l0).
    cancel (&((b_v_right)  # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pr b_v_right r0).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact H0.
Qed.

Lemma proof_of_Delete_which_implies_wit_4 : Delete_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_not_zero; [ | try tauto].
  Intros l0 k v r0 pl.
  Intros pr.
  Exists pr pl l0 v r0.
  Exists k.
  split_pure_spatial.
  - try cancel (b # Ptr |-> b_v).
    try cancel (&((b_v)  # "tree" ->ₛ "right") # Ptr |-> b_v_right).
    cancel (&((b_v_right)  # "tree" ->ₛ "key") # Int |-> k).
    cancel (&((b_v_right)  # "tree" ->ₛ "father") # Ptr |-> b_v).
    cancel (&((b_v_right)  # "tree" ->ₛ "value") # Int |-> v).
    cancel (&((b_v_right)  # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl b_v_right l0).
    cancel (&((b_v_right)  # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pr b_v_right r0).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact H0.
Qed.

Lemma proof_of_Delete_derive_high_level_spec_by_low_level_spec : Delete_derive_high_level_spec_by_low_level_spec.
Proof.
	LLM_pre_process ltac:(int_auto).
	Intros b_pre_v.
	unfold Bst.store_map.
	Intros tr.
	Exists tr.
	Exists b_pre_v.
	repeat (split_pure_spatial || split_pures).
	- cancel (store_tree b_pre_v 0 tr).
	  cancel (b_pre # Ptr |-> b_pre_v).
	  apply derivable1_wand_sepcon_adjoint.
	  Intros b_post_v.
	  Exists b_post_v.
	  Exists (tree_delete x_pre tr).
	  repeat (split_pure_spatial || split_pures).
	  + cancel (b_pre # Ptr |-> b_post_v).
	    cancel (store_tree b_post_v 0 (tree_delete x_pre tr)).
	  + dump_pre_spatial.
	    apply delete_SearchTree.
	    exact H1.
	  + dump_pre_spatial.
	    apply delete_Abs.
	    exact H1.
	    exact H2.
	- dump_pre_spatial.
	  exact H.
	- dump_pre_spatial.
	  exact H0.
Qed.
