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
From SimpleC.EE.QCP_demos_LLM Require Import bst_insert_rec_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.bst_lib.
Import get_right_most.
Local Open Scope sac.

Lemma proof_of_insert_entail_wit_1 : insert_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply store_tree_not_zero; [ | tauto].
	Intros l0.
	Intros k.
	Intros v.
	Intros r0.
	Intros pl.
	Intros pr.
	Exists pr.
	Exists pl.
	Exists l0.
	Exists v.
	Exists r0.
	Exists k.
	Exists (make_tree l0 k v r0).
	repeat (split_pure_spatial || split_pures).
	+ cancel (&(b_pre # "tree" ->ₛ "key") # Int |-> k).
	  cancel (&(b_pre # "tree" ->ₛ "value") # Int |-> v).
	  cancel (&(b_pre # "tree" ->ₛ "left") # Ptr |-> pl).
	  cancel (store_tree pr r0).
	  cancel.
	+ dump_pre_spatial.
	  tauto.
	+ dump_pre_spatial.
	  assumption.
	+ dump_pre_spatial.
	  lia.
	+ dump_pre_spatial.
	  lia.
	+ dump_pre_spatial.
	  reflexivity.
Qed.

Lemma proof_of_insert_return_wit_1 : insert_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	subst.
	simpl.
	destruct (Key.dec x_pre b_key) as [[Hlt | Hgt] | Heq]; try Key.order.
	simpl.
	subst.
	Exists b_left.
	Exists b_right.
	repeat (split_pure_spatial || split_pures).
	+ cancel (&(b # "tree" ->ₛ "key") # Int |-> b_key).
	  cancel (&(b # "tree" ->ₛ "value") # Int |-> value_pre).
	  cancel (&(b # "tree" ->ₛ "left") # Ptr |-> b_left).
	  cancel (store_tree b_right r0).
	  cancel.
	+ dump_pre_spatial.
	  assumption.
	+ dump_pre_spatial.
	  lia.
Qed.

Lemma proof_of_insert_return_wit_2 : insert_return_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	subst.
	simpl.
	destruct (Key.dec x_pre b_key) as [[Hlt | Hgt] | Heq]; try Key.order.
	simpl.
	Exists b_left.
	Exists retval.
	repeat (split_pure_spatial || split_pures).
	+ cancel (&(b # "tree" ->ₛ "key") # Int |-> b_key).
	  cancel (&(b # "tree" ->ₛ "value") # Int |-> b_value).
	  cancel (&(b # "tree" ->ₛ "left") # Ptr |-> b_left).
	  cancel (store_tree retval (tree_insert x_pre value_pre r0)).
	  cancel.
	+ dump_pre_spatial.
	  tauto.
	+ dump_pre_spatial.
	  lia.
Qed.

Lemma proof_of_insert_return_wit_3 : insert_return_wit_3.
Proof.
	LLM_pre_process ltac:(int_auto).
	subst.
	simpl.
	destruct (Key.dec x_pre b_key) as [[Hlt | Hgt] | Heq]; try Key.order.
	simpl.
	Exists retval.
	Exists b_right.
	repeat (split_pure_spatial || split_pures).
	+ cancel (store_tree retval (tree_insert x_pre value_pre l0)).
	  cancel (&(b # "tree" ->ₛ "key") # Int |-> b_key).
	  cancel (&(b # "tree" ->ₛ "value") # Int |-> b_value).
	  cancel (&(b # "tree" ->ₛ "left") # Ptr |-> retval).
	  cancel (&(b # "tree" ->ₛ "right") # Ptr |-> b_right).
	  cancel (store_tree b_right r0).
	+ dump_pre_spatial.
	  tauto.
	+ dump_pre_spatial.
	  lia.
Qed.

Lemma proof_of_insert_return_wit_4 : insert_return_wit_4.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (store_tree_zero b_pre tr_low_level_spec).
	- dump_pre_spatial.
	  assumption.
	- Intros_p Hempty.
	  subst.
	  simpl.
	  Exists 0.
	  Exists 0.
	  repeat (split_pure_spatial || split_pures).
	  + cancel (&(retval # "tree" ->ₛ "key") # Int |-> x_pre).
	    cancel (&(retval # "tree" ->ₛ "value") # Int |-> value_pre).
	    cancel (&(retval # "tree" ->ₛ "left") # Ptr |-> 0).
	    cancel (&(retval # "tree" ->ₛ "right") # Ptr |-> 0).
	  + dump_pre_spatial.
	    assumption.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    reflexivity.
	  + dump_pre_spatial.
	    reflexivity.
Qed.

Lemma proof_of_insert_derive_high_level_spec_by_low_level_spec : insert_derive_high_level_spec_by_low_level_spec.
Proof.
	LLM_pre_process ltac:(int_auto).
	unfold Bst.store_map.
	Intros tr.
	Exists tr.
	repeat split_pure_spatial.
	- cancel (store_tree b_pre tr).
	  apply derivable1_wand_sepcon_adjoint.
	  Intros retval_2.
	  Exists retval_2.
	  unfold Bst.store_map.
	  Exists (tree_insert x_pre value_pre tr).
	  repeat (split_pure_spatial || split_pures).
	  + cancel.
	  + dump_pre_spatial.
	    eapply insert_SearchTree; eauto.
	  + dump_pre_spatial.
	    eapply insert_Abs; eauto.
	- split_pures.
	  + dump_pre_spatial.
	    exact H.
	  + dump_pre_spatial.
	    exact H0.
Qed.
