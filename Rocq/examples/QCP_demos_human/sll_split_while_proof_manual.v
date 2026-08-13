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
From SimpleC.EE.QCP_demos_human Require Import sll_split_while_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import sll_lib.
From SimpleC.EE.QCP_demos_human Require Import sll_merge_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_split_while_entail_wit_2_2 : split_while_entail_wit_2_2.
Proof. 
  LLM_pre_process ltac:(int_auto).
  subst x_next.
  sep_apply (sll_zero 0 l1_new); [ | reflexivity].
  Intros_p Hl1nil.
  subst l1_new.
  Exists q_v_2 x (@nil Z) (x_data :: l1_2) l2_2.
  simpl (sll 0 nil).
  split_pure_spatial.
  - cancel (p_pre # Ptr |-> x).
    cancel (sll x (x_data :: l1_2)).
    cancel (q_pre # Ptr |-> q_v_2).
    cancel (sll q_v_2 l2_2).
    apply store_ptr_undef_store_ptr.
  - split_pures.
    + dump_pre_spatial.
      unfold split_rec_rel in *.
      rewrite (program_para_equiv (split_rec_rel_unfold)) in *.
      unfold split_rec_rel_f in *.
      rewrite bind_ret_left in PreH2.
      exact PreH2.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_split_while_return_wit_1 : split_while_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (sll_zero x l).
	- dump_pre_spatial.
		unfold NULL.
		lia.
	- Intros_p Hl.
		Exists q_v.
		Exists p_v.
		Exists l1.
		Exists l2.
		repeat split_pure_spatial.
		+ cancel (p_pre # Ptr |-> p_v).
			cancel (sll p_v l1).
			cancel (q_pre # Ptr |-> q_v).
			cancel (sll q_v l2).
		+ dump_pre_spatial.
			rewrite Hl in PreH2.
			unfold split_rec_rel in PreH2.
			erewrite (program_para_equiv (split_rec_rel_unfold)) in PreH2.
			unfold split_rec_rel_f in PreH2.
			unfold maketuple in PreH2.
			exact PreH2.
Qed.

Lemma proof_of_split_while_which_implies_wit_2_split_goal_1 :
  split_while_which_implies_wit_2_split_goal_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  subst.
  eapply  split_rel_eval_xnotnil;eauto.
Qed.

Lemma proof_of_split_while_which_implies_wit_2 : split_while_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_split_while_which_implies_wit_2_split_goal_1.
Qed.

Lemma proof_of_split_while_which_implies_wit_4_split_goal_1 :
  split_while_which_implies_wit_4_split_goal_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
  subst l.
  unfold split_rec_rel in PreH1.
  rewrite (program_para_equiv (split_rec_rel_unfold)) in PreH1.
  unfold split_rec_rel_f in PreH1. 
  rewrite bind_assoc in PreH1.
  rewrite bind_2_reversepair_equiv_Id in PreH1.
  rewrite bind_ret_right in PreH1.
  auto.
Qed.

Lemma proof_of_split_while_which_implies_wit_4 : split_while_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_split_while_which_implies_wit_4_split_goal_1.
Qed.
