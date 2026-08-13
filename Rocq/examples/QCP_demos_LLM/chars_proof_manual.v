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
From SimpleC.EE.QCP_demos_LLM Require Import chars_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_chars_initialize_entail_wit_1 : chars_initialize_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply CharArray.undef_full_to_undef_seg.
	unfold repeat_Z.
	simpl.
	rewrite (CharArray.full_empty a_pre 0).
	split_pure_spatial.
	- cancel (CharArray.undef_seg a_pre 0 n_pre).
	- split_pures.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact PreH1.
	  + dump_pre_spatial.
	    exact PreH1.
	  + dump_pre_spatial.
	    exact PreH2.
	  + dump_pre_spatial.
	    lia.
Qed.

Lemma proof_of_chars_initialize_entail_wit_2 : chars_initialize_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	rewrite repeat_Z_tail.
	split_pure_spatial.
	- cancel (CharArray.full a_pre (i + 1) (repeat_Z m_pre i ++ m_pre :: nil)).
	  cancel (CharArray.undef_seg a_pre (i + 1) n_pre).
	- split_pures.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact PreH4.
	  + dump_pre_spatial.
	    exact PreH5.
	- lia.
Qed.

Lemma proof_of_chars_initialize_return_wit_1 : chars_initialize_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	assert (i = n_pre) by lia.
	subst i.
	rewrite (CharArray.undef_seg_empty a_pre n_pre).
	rewrite sepcon_emp_equiv.
	cancel (CharArray.full a_pre n_pre (repeat_Z m_pre n_pre)).
Qed.
