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
From SimpleC.EE.QCP_demos_human Require Import poly_sll_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import poly_sll_lib.
Local Open Scope sac.

Lemma proof_of_reverse_entail_wit_1_split_goal_1 :
  reverse_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_reverse_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists (x :: l1_2).
	Exists xs.
	split_pure_spatial.
	- simpl sll.
		Exists v_data.
		Exists w.
		split_pure_spatial.
		+ cancel (sll storeA v_next xs).
			cancel (sll storeA w l1_2).
			cancel (((&((v)  # "list" ->ₛ "data")) # Ptr  |-> v_data)).
			cancel (((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)).
			cancel (storeA v_data x).
		+ dump_pre_spatial.
			exact PreH3.
	- dump_pre_spatial.
		subst l2_2.
		simpl.
		rewrite <- app_assoc.
		simpl.
		exact PreH2.
Qed.

Lemma proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply (sll_zero A storeA v l2); [ | tauto].
	Intros_p Hl2.
	rewrite Hl2 in PreH1.
	rewrite app_nil_r in PreH1.
	subst l.
	rewrite rev_involutive.
	cancel (sll storeA w l1).
Qed.
