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
From SimpleC.EE.QCP_demos_LLM Require Import bst_fp_delete_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.bst_fp_lib.
Local Open Scope sac.

Lemma proof_of_replace_min_entail_wit_1 : replace_min_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists b_pre_v.
	Exists nil.
	Exists tr.
	simpl.
	repeat (split_pure_spatial || split_pures).
	- repeat cancel.
	- dump_pre_spatial.
	  exact PreH1.
	- dump_pre_spatial.
	  reflexivity.
	- dump_pre_spatial.
	  reflexivity.
	- dump_pre_spatial.
	  reflexivity.
	- dump_pre_spatial.
	  exact PreH4.
	- dump_pre_spatial.
	  reflexivity.
	- dump_pre_spatial.
	  reflexivity.
	- dump_pre_spatial.
	  reflexivity.
Qed. 

Lemma proof_of_replace_min_entail_wit_2 : replace_min_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (store_tree_not_zero b_v_2 fa tr0_2).
	- dump_pre_spatial.
	  lia.
	- Intros l0.
	  Intros k0.
	  Intros v0.
	  Intros r0.
	  Intros b_v_left.
	  Intros b_v_right.
	  Exists b_v_right.
	  Exists b_v_left.
	  Exists l0.
	  Exists v0.
	  Exists r0.
	  Exists fa.
	  Exists k0.
	  Exists b_v_2.
	  Exists pt0_2.
	  Exists tr0_2.
	  repeat (split_pure_spatial || split_pures).
	  + repeat cancel.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    auto.
	  + dump_pre_spatial.
	    auto.
	  + dump_pre_spatial.
	    auto.
	  + dump_pre_spatial.
	    auto.
	  + dump_pre_spatial.
	    auto.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    auto.
Qed. 

Lemma proof_of_replace_min_entail_wit_3 : replace_min_entail_wit_3.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (store_tree_not_zero b_v_right_2 b_v r0_2).
	- dump_pre_spatial.
	  tauto.
	- Intros l0.
	  Intros b_v_right_key.
	  Intros b_v_right_value.
	  Intros r0.
	  Intros b_v_right_left.
	  Intros b_v_right_right.
	  Exists b_v_right_right.
	  Exists b_v_right_left.
	  Exists b_v.
	  Exists l0.
	  Exists b_v_right_value.
	  Exists r0.
	  Exists b_v_right_key.
	  Exists b_v_right_2.
	  Exists l0_2.
	  Exists b_v_value_2.
	  Exists r0_2.
	  Exists b_v_father_2.
	  Exists b_v_key_2.
	  Exists b_v_left_2.
	  Exists b_v.
	  Exists pt0_2.
	  Exists tr0_2.
	  repeat (split_pure_spatial || split_pures).
	  + repeat cancel.
	  + dump_pre_spatial.
	    exact PreH3.
	  + dump_pre_spatial.
	    exact PreH4.
	  + dump_pre_spatial.
	    exact PreH5.
	  + dump_pre_spatial.
	    exact PreH6.
	  + dump_pre_spatial.
	    reflexivity.
	  + dump_pre_spatial.
	    exact PreH7.
	  + dump_pre_spatial.
	    exact PreH2.
	  + dump_pre_spatial.
	    exact PreH8.
	  + dump_pre_spatial.
	    exact PreH9.
	  + dump_pre_spatial.
	    exact PreH10.
	  + dump_pre_spatial.
	    exact PreH11.
	  + dump_pre_spatial.
	    exact PreH12.
	  + dump_pre_spatial.
	    exact PreH1.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact H.
	  + dump_pre_spatial.
	    reflexivity.
Qed. 

Lemma proof_of_replace_min_entail_wit_4 : replace_min_entail_wit_4.
Proof.
	LLM_pre_process ltac:(int_auto).
	subst b_v_father.
	sep_apply_l_atomic (store_tree_not_zero b_v_left b_v_2 l0).
	- dump_pre_spatial.
	  tauto.
	- Intros l1.
	  Intros k0.
	  Intros v0.
	  Intros r1.
	  Intros pl.
	  Intros pr.
	  Exists b_v_left.
	  Exists (LH b_v_key b_v_value r0 :: pt0_2).
	  Exists (make_tree l1 k0 v0 r1).
	  repeat (split_pure_spatial || split_pures).
	  + sep_apply_l_atomic (store_tree_make_tree b_v_left k0 v0 pl pr b_v_2 l1 r1).
	    * dump_pre_spatial.
	      lia.
	    * dump_pre_spatial.
	      lia.
	    * sep_apply (store_ptb_LH b b_v_2 b_v_right fa b_v_key b_v_value r0).
	      { sep_apply (store_ptb_app (&((b_v_2) # "tree" ->ₛ "left")) b b_pre b_v_2 fa ptr_pre
	          (LH b_v_key b_v_value r0 :: nil) pt0_2).
	        simpl.
	        cancel. }
	      { lia. }
	      { exact PreH6. }
	  + dump_pre_spatial.
	    exact PreH2.
	  + dump_pre_spatial.
	    rewrite PreH11 in PreH3.
	    match goal with
	    | Htree : l0 = make_tree _ _ _ _ |- _ => rewrite Htree in PreH3
	    end.
	    simpl in PreH3.
	    exact PreH3.
	  + dump_pre_spatial.
	    rewrite PreH11 in PreH4.
	    match goal with
	    | Htree : l0 = make_tree _ _ _ _ |- _ => rewrite Htree in PreH4
	    end.
	    simpl in PreH4.
	    exact PreH4.
	  + dump_pre_spatial.
	    rewrite PreH11 in PreH5.
	    match goal with
	    | Htree : l0 = make_tree _ _ _ _ |- _ => rewrite Htree in PreH5
	    end.
	    simpl in PreH5.
	    exact PreH5.
	  + dump_pre_spatial.
	    exact PreH1.
	  + dump_pre_spatial.
	    rewrite PreH11 in PreH7.
	    match goal with
	    | Htree : l0 = make_tree _ _ _ _ |- _ => rewrite Htree in PreH7
	    end.
	    simpl in PreH7.
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
	  rewrite PreH8.
	  rewrite PreH12 in *.
	  rewrite Hl0empty in *.
	  rewrite Hr0empty in *.
	  simpl in *.
	  repeat (split_pure_spatial || split_pures).
	  + repeat cancel.
	  + dump_pre_spatial.
	    symmetry.
	    exact PreH5.
	  + dump_pre_spatial.
	    symmetry.
	    exact PreH6.
	  + dump_pre_spatial.
	    exact PreH9.
	  + dump_pre_spatial.
	    exact PreH10.
Qed. 

Lemma proof_of_replace_min_return_wit_1 : replace_min_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	subst b_v_father.
	sep_apply_l_atomic (store_tree_make_tree b_v_right b_v_right_key b_v_right_value b_v_right_left b_v_right_right fa l0 r0).
	- dump_pre_spatial.
	  exact PreH13.
	- dump_pre_spatial.
	  lia.
	- rewrite <- PreH16.
	  sep_apply store_ptb_store_tree.
	  Intros p_root.
	  Exists p_root.
	  Exists b_v_value.
	  Exists b_v_key.
	  sep_apply_l_atomic (store_tree_zero b_v_left b_v l1).
	  + dump_pre_spatial.
	    exact PreH7.
	  + Intros_p Hempty.
	    rewrite PreH8.
	    rewrite PreH12.
	    rewrite Hempty.
	    simpl.
	  repeat (split_pure_spatial || split_pures).
	    * cancel.
	    * dump_pre_spatial.
	      rewrite PreH12 in *.
	      rewrite Hempty in *.
	      simpl in *.
	      first [exact PreH9 | exact PreH10 | exact PreH3 | exact PreH4 | symmetry; exact PreH3 | symmetry; exact PreH4].
	    * dump_pre_spatial.
	      rewrite PreH12 in *.
	      rewrite Hempty in *.
	      simpl in *.
	      first [exact PreH9 | exact PreH10 | exact PreH3 | exact PreH4 | symmetry; exact PreH3 | symmetry; exact PreH4].
	    * dump_pre_spatial.
	      rewrite PreH12 in *.
	      rewrite Hempty in *.
	      simpl in *.
	      first [exact PreH9 | exact PreH10 | exact PreH3 | exact PreH4 | symmetry; exact PreH3 | symmetry; exact PreH4].
	    * dump_pre_spatial.
	      rewrite PreH12 in *.
	      rewrite Hempty in *.
	      simpl in *.
	      first [exact PreH9 | exact PreH10 | exact PreH3 | exact PreH4 | symmetry; exact PreH3 | symmetry; exact PreH4].
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
	- dump_pre_spatial.
	  simpl.
	  reflexivity.
Qed. 

Lemma proof_of_Delete_entail_wit_2 : Delete_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (store_tree_not_zero b_v_2 fa tr0_2).
	- dump_pre_spatial.
	  tauto.
	- Intros l0.
	  Intros b_v_key.
	  Intros b_v_value.
	  Intros r0.
	  Intros b_v_left.
	  Intros b_v_right.
	  Exists b_v_right.
	  Exists b_v_left.
	  Exists l0.
	  Exists b_v_value.
	  Exists r0.
	  Exists fa.
	  Exists b_v_key.
	  Exists pt0_2.
	  Exists tr0_2.
	  Exists b_v_2.
	  split_pure_spatial.
	  + simpl.
	    cancel (b # Ptr |-> b_v_2).
	    cancel ((&((b_v_2) # "tree" ->ₛ "key")) # Int |-> b_v_key).
	    cancel ((&((b_v_2) # "tree" ->ₛ "father")) # Ptr |-> fa).
	    cancel ((&((b_v_2) # "tree" ->ₛ "value")) # Int |-> b_v_value).
	    cancel (store_ptb b b_pre fa 0 pt0_2).
	    cancel ((&((b_v_2) # "tree" ->ₛ "left")) # Ptr |-> b_v_left).
	    cancel (store_tree b_v_left b_v_2 l0).
	    cancel ((&((b_v_2) # "tree" ->ₛ "right")) # Ptr |-> b_v_right).
	    cancel (store_tree b_v_right b_v_2 r0).
	  + repeat split_pures.
	    * dump_pre_spatial.
	      exact PreH1.
	    * dump_pre_spatial.
	      exact PreH2.
	    * dump_pre_spatial.
	      lia.
	    * dump_pre_spatial.
	      lia.
	    * dump_pre_spatial.
	      reflexivity.
	    * dump_pre_spatial.
	      exact H.
Qed. 

Lemma proof_of_Delete_entail_wit_3 : Delete_entail_wit_3.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (store_tree_not_zero b_v_left_2 b_v l0_2).
	- dump_pre_spatial.
	  tauto.
	- Intros l0.
	  Intros b_v_left_key.
	  Intros b_v_left_value.
	  Intros r0.
	  Intros b_v_left_left.
	  Intros b_v_left_right.
	  Exists b_v_left_right.
	  Exists b_v_left_left.
	  Exists l0.
	  Exists b_v_left_value.
	  Exists r0.
	  Exists b_v.
	  Exists b_v_left_key.
	  Exists b_v_left_2.
	  Exists l0_2.
	  Exists b_v_value_2.
	  Exists r0_2.
	  Exists b_v_father_2.
	  Exists pt0_2.
	  Exists tr0_2.
	    Exists b_v_key_2.
	  Exists b_v_right_2.
	  Exists b_v.
	  split_pure_spatial.
	  + simpl.
	    cancel (b # Ptr |-> b_v).
	    cancel ((&((b_v) # "tree" ->ₛ "right")) # Ptr |-> b_v_right_2).
	    cancel ((&((b_v) # "tree" ->ₛ "key")) # Int |-> b_v_key_2).
	    cancel ((&((b_v) # "tree" ->ₛ "father")) # Ptr |-> b_v_father_2).
	    cancel ((&((b_v) # "tree" ->ₛ "value")) # Int |-> b_v_value_2).
	    cancel (store_ptb b b_pre fa 0 pt0_2).
	    cancel (store_tree b_v_right_2 b_v r0_2).
	    cancel ((&((b_v) # "tree" ->ₛ "left")) # Ptr |-> b_v_left_2).
	    cancel ((&((b_v_left_2) # "tree" ->ₛ "key")) # Int |-> b_v_left_key).
	    cancel ((&((b_v_left_2) # "tree" ->ₛ "father")) # Ptr |-> b_v).
	    cancel ((&((b_v_left_2) # "tree" ->ₛ "value")) # Int |-> b_v_left_value).
	    cancel ((&((b_v_left_2) # "tree" ->ₛ "left")) # Ptr |-> b_v_left_left).
	    cancel (store_tree b_v_left_left b_v_left_2 l0).
	    cancel ((&((b_v_left_2) # "tree" ->ₛ "right")) # Ptr |-> b_v_left_right).
	    cancel (store_tree b_v_left_right b_v_left_2 r0).
	  + repeat split_pures.
	    * dump_pre_spatial.
	      reflexivity.
	    * dump_pre_spatial.
	      exact PreH5.
	    * dump_pre_spatial.
	      exact PreH2.
	    * dump_pre_spatial.
	      exact PreH3.
	    * dump_pre_spatial.
	      exact PreH4.
	    * dump_pre_spatial.
	      exact PreH6.
	    * dump_pre_spatial.
	      exact PreH7.
	    * dump_pre_spatial.
	      exact PreH8.
	    * dump_pre_spatial.
	      exact PreH9.
	    * dump_pre_spatial.
	      exact PreH10.
	    * dump_pre_spatial.
	      exact PreH1.
	    * dump_pre_spatial.
	      lia.
	    * dump_pre_spatial.
	      lia.
	    * dump_pre_spatial.
	      reflexivity.
	    * dump_pre_spatial.
	      exact H.
Qed. 

Lemma proof_of_Delete_entail_wit_4 : Delete_entail_wit_4.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (store_tree_not_zero b_v_right_2 b_v r0_2).
	- dump_pre_spatial.
	  tauto.
	- Intros l0.
	  Intros b_v_right_key.
	  Intros b_v_right_value.
	  Intros r0.
	  Intros b_v_right_left.
	  Intros b_v_right_right.
	  Exists b_v_right_right.
	  Exists b_v_right_left.
	  Exists l0.
	  Exists b_v_right_value.
	  Exists r0.
	  Exists b_v.
	  Exists b_v_right_key.
	  Exists b_v_right_2.
	  Exists l0_2.
	  Exists b_v_value_2.
	  Exists r0_2.
	  Exists b_v_father_2.
	  Exists pt0_2.
	  Exists tr0_2.
	  Exists b_v_key_2.
	  Exists b_v_left_2.
	  Exists b_v.
	  split_pure_spatial.
	  + simpl.
	    cancel (b # Ptr |-> b_v).
	    cancel ((&((b_v) # "tree" ->ₛ "left")) # Ptr |-> b_v_left_2).
	    cancel ((&((b_v) # "tree" ->ₛ "key")) # Int |-> b_v_key_2).
	    cancel ((&((b_v) # "tree" ->ₛ "father")) # Ptr |-> b_v_father_2).
	    cancel ((&((b_v) # "tree" ->ₛ "value")) # Int |-> b_v_value_2).
	    cancel (store_ptb b b_pre fa 0 pt0_2).
	    cancel (store_tree b_v_left_2 b_v l0_2).
	    cancel ((&((b_v) # "tree" ->ₛ "right")) # Ptr |-> b_v_right_2).
	    cancel ((&((b_v_right_2) # "tree" ->ₛ "key")) # Int |-> b_v_right_key).
	    cancel ((&((b_v_right_2) # "tree" ->ₛ "father")) # Ptr |-> b_v).
	    cancel ((&((b_v_right_2) # "tree" ->ₛ "value")) # Int |-> b_v_right_value).
	    cancel ((&((b_v_right_2) # "tree" ->ₛ "left")) # Ptr |-> b_v_right_left).
	    cancel (store_tree b_v_right_left b_v_right_2 l0).
	    cancel ((&((b_v_right_2) # "tree" ->ₛ "right")) # Ptr |-> b_v_right_right).
	    cancel (store_tree b_v_right_right b_v_right_2 r0).
	  + repeat split_pures;
	    try solve [dump_pre_spatial; reflexivity | dump_pre_spatial; assumption | dump_pre_spatial; lia].
Qed. 

Lemma proof_of_Delete_entail_wit_5 : Delete_entail_wit_5.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (store_tree_not_zero b_v_left_2 b_v_2 l0).
	- dump_pre_spatial.
	  exact PreH1.
	- Intros l1_left.
	  Intros l1_key.
	  Intros l1_value.
	  Intros l1_right.
	  Intros lpl.
	  Intros lpr.
	  sep_apply_l_atomic (store_tree_not_zero b_v_right_2 b_v_2 r0).
	  + dump_pre_spatial.
	    exact PreH2.
	  + Intros tr0_left.
	    Intros tr0_key.
	    Intros tr0_value.
	    Intros tr0_right.
	    Intros rpl.
	    Intros rpr.
	    Exists b_v_right_2.
	    Exists b_v_left_2.
	    Exists tr0_left.
	    Exists tr0_key.
	    Exists tr0_value.
	    Exists tr0_right.
	    Exists l1_left.
	    Exists l1_key.
	    Exists l1_value.
	    Exists l1_right.
	    Exists (make_tree l1_left l1_key l1_value l1_right).
	    Exists b_v_value_2.
	    Exists (make_tree tr0_left tr0_key tr0_value tr0_right).
	    Exists fa.
	    Exists pt0_2.
	    Exists tr0_2.
	    Exists b_v_key_2.
	    Exists b_v_2.
	    repeat (split_pure_spatial || split_pures).
	    * sep_apply_l_atomic (store_tree_make_tree b_v_left_2 l1_key l1_value lpl lpr b_v_2 l1_left l1_right).
	      { dump_pre_spatial. lia. }
	      { dump_pre_spatial. lia. }
	      sep_apply_l_atomic (store_tree_make_tree b_v_right_2 tr0_key tr0_value rpl rpr b_v_2 tr0_left tr0_right).
	      { dump_pre_spatial. lia. }
	      { dump_pre_spatial. lia. }
	      { rewrite <- H.
	        rewrite <- H3.
	        rewrite PreH9.
	        repeat cancel;
	        try solve [dump_pre_spatial; reflexivity | dump_pre_spatial; assumption | dump_pre_spatial; lia]. }
	    * dump_pre_spatial.
	      exact PreH5.
	    * dump_pre_spatial.
	      exact PreH3.
	    * dump_pre_spatial.
	      exact PreH4.
	    * dump_pre_spatial.
	      exact PreH6.
	    * dump_pre_spatial.
	      lia.
	    * dump_pre_spatial.
	      lia.
	    * dump_pre_spatial.
	      reflexivity.
	    * dump_pre_spatial.
	      rewrite PreH10.
	      rewrite H.
	      rewrite H3.
	      reflexivity.
	    * dump_pre_spatial.
	      reflexivity.
	    * dump_pre_spatial.
	      reflexivity.
	    * dump_pre_spatial.
	      exact PreH1.
	    * dump_pre_spatial.
	      exact PreH2.
Qed.

Lemma proof_of_Delete_entail_wit_6_2 : Delete_entail_wit_6_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	subst b_v_father.
	Exists b_v_right.
	Exists (RH b_v_key b_v_value l0 :: pt0_2).
	Exists r0.
	split_pure_spatial.
	- assert (Hnonnull : b_v_2 <> NULL).
	  { unfold NULL. exact PreH3. }
	  assert (Hrange : INT_MIN <= b_v_key <= INT_MAX).
	  { lia. }
	  sep_apply (store_ptb_RH b b_v_2 b_v_left fa b_v_key b_v_value l0 Hnonnull Hrange).
	  sep_apply (store_ptb_app (&((b_v_2) # "tree" ->ₛ "right")) b b_pre b_v_2 fa 0 (RH b_v_key b_v_value l0 :: nil) pt0_2).
	  cancel.
	  simpl.
	  cancel.
	- repeat match goal with
	  | H: (combine_tree pt0_2 (tree_delete x_pre tr0_2)) = (tree_delete x_pre tr_low_level_spec) |- _ => rewrite <- H
	  | H: tr0_2 = make_tree l0 b_v_key b_v_value r0 |- _ => rewrite H
	  end.
	  simpl.
	  dump_pre_spatial.
	  f_equal.
	  destruct (Key.dec x_pre b_v_key) as [[Hlt | Hgt] | Heq].
	  + exfalso.
	    Key.order.
	  + reflexivity.
	  + subst.
	    exfalso.
	    Key.order.
Qed. 

Lemma proof_of_Delete_entail_wit_6_1 : Delete_entail_wit_6_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	subst b_v_father.
	Exists b_v_left.
	Exists (LH b_v_key b_v_value r0 :: pt0_2).
	Exists l0.
	split_pure_spatial.
	- assert (Hnonnull : b_v_2 <> NULL).
	  { unfold NULL. lia. }
	  assert (Hrange : INT_MIN <= b_v_key <= INT_MAX).
	  { lia. }
	  sep_apply (store_ptb_LH b b_v_2 b_v_right fa b_v_key b_v_value r0 Hnonnull Hrange).
	  sep_apply (store_ptb_app (&((b_v_2) # "tree" ->ₛ "left")) b b_pre b_v_2 fa 0 (LH b_v_key b_v_value r0 :: nil) pt0_2).
	  cancel.
	  simpl.
	  cancel.
	- repeat match goal with
	  | H: (combine_tree pt0_2 (tree_delete x_pre tr0_2)) = (tree_delete x_pre tr_low_level_spec) |- _ => rewrite <- H
	  | H: tr0_2 = make_tree l0 b_v_key b_v_value r0 |- _ => rewrite H
	  end.
	  simpl.
	  dump_pre_spatial.
	  f_equal.
	  destruct (Key.dec x_pre b_v_key) as [[Hlt | Hgt] | Heq].
	  + reflexivity.
	  + exfalso.
	    Key.order.
	  + subst.
	    exfalso.
	    Key.order.
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

Lemma proof_of_Delete_return_wit_2 : Delete_return_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	subst b_v_father.
	assert (Hkey : INT_MIN <= ptr_callee_key <= INT_MAX) by lia.
	sep_apply_l_atomic (store_tree_make_tree b_v ptr_callee_key ptr_callee_value b_v_left b_callee_v fa l1 (delete_min tr0)).
	- dump_pre_spatial.
	  exact PreH5.
	- dump_pre_spatial.
	  exact Hkey.
	- sep_apply store_ptb_store_tree.
	  Intros p_root.
	  Exists p_root.
	  cancel.
	  assert (combine_tree pt0 (make_tree l1 ptr_callee_key ptr_callee_value (delete_min tr0)) = tree_delete x_pre tr_low_level_spec).
	  {
		rewrite <- PreH8.
		rewrite PreH12.
		assert (Heqkey : x_pre = b_v_key) by lia.
		subst x_pre.
		rewrite PreH13.
		rewrite PreH14.
		unfold tree_delete.
		destruct (Key.dec b_v_key b_v_key) as [[Hlt | Hgt] | Heq].
		+ exfalso.
		Key.order.
		+ exfalso.
		Key.order.
		+ rewrite PreH1 , PreH2.
		  rewrite PreH14.
		  auto.
	  }
	  rewrite H.
	  cancel.
Qed.

Lemma proof_of_Delete_return_wit_3 : Delete_return_wit_3.
Proof.
	LLM_pre_process ltac:(int_auto).
	assert (Hright_key : INT_MIN <= b_v_right_key <= INT_MAX) by lia.
	sep_apply_l_atomic (store_tree_make_tree b_v_right b_v_right_key b_v_right_value b_v_right_left b_v_right_right fa l0 r0).
	- dump_pre_spatial.
	  exact PreH11.
	- dump_pre_spatial.
	  exact Hright_key.
	- sep_apply_l_atomic (store_tree_zero b_v_left b_v l1).
	  + dump_pre_spatial.
	    exact PreH3.
	  + sep_apply store_ptb_store_tree.
	    Intros p_root.
	    Exists p_root.
	    rewrite <- PreH6.
	    rewrite PreH10.
	    rewrite PreH15.
	    assert (Heqkey : x_pre = b_v_key) by lia.
	    subst x_pre.
	    match goal with
	    | Hempty : l1 = empty |- _ => rewrite Hempty
	    end.
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
	    rewrite <- PreH6.
	    rewrite PreH10.
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

Lemma proof_of_Delete_return_wit_4 : Delete_return_wit_4.
Proof.
	LLM_pre_process ltac:(int_auto).
	assert (Hleft_key : INT_MIN <= b_v_left_key <= INT_MAX) by lia.
	sep_apply_l_atomic (store_tree_make_tree b_v_left b_v_left_key b_v_left_value b_v_left_left b_v_left_right fa l0 r0).
	- dump_pre_spatial.
	  exact PreH11.
	- dump_pre_spatial.
	  exact Hleft_key.
	- sep_apply_l_atomic (store_tree_zero b_v_right b_v r1).
	  + dump_pre_spatial.
	    exact PreH3.
	  + sep_apply store_ptb_store_tree.
	    Intros p_root.
	    Exists p_root.
	    rewrite <- PreH6.
	    rewrite PreH10.
	    rewrite PreH15.
	    assert (Heqkey : x_pre = b_v_key) by lia.
	    subst x_pre.
	    match goal with
	    | Hempty : r1 = empty |- _ => rewrite Hempty
	    end.
	    unfold tree_delete.
	    destruct (Key.dec b_v_key b_v_key) as [[Hlt | Hgt] | Heq].
	    * exfalso.
	      Key.order.
	    * exfalso.
	      Key.order.
	    * simpl.
	      cancel.
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
