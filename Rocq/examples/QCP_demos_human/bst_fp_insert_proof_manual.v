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
From SimpleC.EE.QCP_demos_human Require Import bst_fp_insert_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import bst_fp_lib.
Local Open Scope sac.

Lemma proof_of_insert_entail_wit_1 : insert_entail_wit_1.
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
	      reflexivity.
	    * dump_pre_spatial.
	      reflexivity.
	- repeat split_pures; dump_pre_spatial; try exact PreH1; try exact PreH2; simpl; reflexivity.
Qed.

Lemma proof_of_insert_entail_wit_2_1 : insert_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (store_ptb_LH b b_v_2); [ | try tauto .. ].
  sep_apply store_ptb_app.
  Exists
    b_v_left
    (LH b_v_key b_v_value r0 ::  pt0_2)
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
      subst.
      rewrite <- PreH6.
      simpl.
      f_equal.
      destruct (Key.dec x_pre b_v_key) as [[? | ?] | ?];
        first [reflexivity | Key.order].
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
Qed.

Lemma proof_of_insert_entail_wit_2_2 : insert_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (store_ptb_RH b b_v_2); [ | try tauto .. ].
  sep_apply store_ptb_app.
  Exists
    b_v_right
    (RH b_v_key b_v_value l0 ::  pt0_2)
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
      subst.
      rewrite <- PreH7.
      simpl.
      f_equal.
      destruct (Key.dec x_pre b_v_key) as [[? | ?] | ?];
        first [reflexivity | Key.order].
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
Qed.

Lemma proof_of_insert_return_wit_2 : insert_return_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	subst b_v.
	sep_apply (store_tree_zero 0 fa tr0).
	- Intros_p Hempty.
	  rewrite Hempty in PreH3.
	  simpl in PreH3.
	  sep_apply_l_atomic (store_tree_size_1 retval fa x_pre value_pre).
	  + dump_pre_spatial.
	    exact PreH1.
	  + dump_pre_spatial.
	    lia.
	  + sep_apply (store_ptb_store_tree b_pre b retval fa 0 pt0
	      (make_tree empty x_pre value_pre empty)).
	    Intros b_pre_v.
	    Exists b_pre_v.
	    rewrite PreH3.
	    cancel.
	- reflexivity.
Qed.

Lemma proof_of_insert_return_wit_1 : insert_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply store_tree_make_tree; [ | tauto ..].
	sep_apply store_ptb_store_tree.
	Intros p_root.
	Exists p_root.
	cancel.
	assert (Hins : combine_tree pt0 (make_tree l0 b_v_key value_pre
r0) = tree_insert x_pre value_pre
tr_low_level_spec).
	{
		rewrite PreH5 in PreH7.
		simpl in PreH7.
		simpl.
		destruct (Key.dec x_pre b_v_key) as [[Hlt | Hgt] | Heq]; try Key.order.
		subst.
		auto.
	}
	rewrite Hins.
	cancel.
Qed.

Lemma proof_of_insert_which_implies_wit_1 : insert_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_tree_not_zero; [ | tauto].
  Intros x.
  Intros k.
  Intros v.
  Intros r0. 
  Intros pl pr.
  Exists pr pl x v.
  Exists r0 k.
  split_pure_spatial.
  - cancel (b # Ptr |-> b_v).
    cancel (&((b_v)  # "tree" ->ₛ "key") # Int |-> k).
    cancel (&((b_v)  # "tree" ->ₛ "father") # Ptr |-> fa).
    cancel (&((b_v)  # "tree" ->ₛ "value") # Int |-> v).
    cancel (&((b_v)  # "tree" ->ₛ "left") # Ptr |-> pl).
    cancel (store_tree pl b_v x).
    cancel (&((b_v)  # "tree" ->ₛ "right") # Ptr |-> pr).
    cancel (store_tree pr b_v r0).
  - split_pures.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      exact H0.
Qed.

Lemma proof_of_insert_derive_high_level_spec_by_low_level_spec : insert_derive_high_level_spec_by_low_level_spec.
Proof.
	LLM_pre_process ltac:(int_auto).
	Intros b_pre_v.
	unfold Bst.store_map.
	Intros tr.
	Exists tr.
	Exists b_pre_v.
	split_pure_spatial.
	- cancel (store_tree b_pre_v 0 tr).
	  cancel (b_pre # Ptr |-> b_pre_v).
	  apply derivable1_wand_sepcon_adjoint.
	  Intros retval_2.
	  Exists retval_2.
	  unfold Bst.store_map.
	  Exists (tree_insert x_pre value_pre tr).
	  split_pure_spatial.
	  + cancel.
	  + split_pures.
	    * dump_pre_spatial.
	      eapply insert_SearchTree; eauto.
	    * dump_pre_spatial.
	      eapply insert_Abs; eauto.
	- split_pures.
	  + dump_pre_spatial.
	    exact H.
	  + dump_pre_spatial.
	    exact H0.
Qed.
