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
From SimpleC.EE.QCP_demos_LLM Require Import sll_split_while_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
From SimpleC.EE.QCP_demos_LLM Require Import sll_merge_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_split_while_entail_wit_3 : split_while_entail_wit_3.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists pv.
	Exists qv_2.
	Exists x.
	Exists l_2.
	Exists l1_new.
	Exists l2_2.
	Exists x_data_2.
	Exists l1_2.
	repeat split_pure_spatial.
	- cancel (p_pre # Ptr |-> x).
		cancel (&(x # "list" ->ₛ "data") # Int |-> x_data_2).
		cancel (&(x # "list" ->ₛ "next") # Ptr |-> pv).
		cancel (sll pv l1_2).
		cancel (sll x_next l1_new).
		cancel (q_pre # Ptr |-> qv_2).
		cancel (sll qv_2 l2_2).
		sep_apply store_ptr_undef_store_ptr.
		cancel (&( "t") # Ptr |->_).
	- repeat split_pures.
		+ dump_pre_spatial.
		  rewrite PreH3 in PreH1.
		  unfold split_rec_rel in *.
		  apply split_rel_eval_xnotnil in PreH1.
		  exact PreH1.
		+ dump_pre_spatial.
		  exact PreH3.
		+ dump_pre_spatial.
		  exact PreH2.
Qed.

Lemma proof_of_split_while_entail_wit_5 : split_while_entail_wit_5.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists qv.
	Exists p_head_2.
	Exists x.
	Exists l_2.
	Exists l1_new.
	Exists x_data_2.
	Exists l1_2.
	Exists x_data2_2.
	Exists l2_2.
	repeat split_pure_spatial.
	- cancel (&(x # "list" ->ₛ "data") # Int |-> x_data2_2).
		cancel (p_pre # Ptr |-> p_head_2).
		cancel (sll p_head_2 (x_data_2 :: l1_2)).
		cancel (q_pre # Ptr |-> x).
		cancel (sll qv l2_2).
		cancel (&(x # "list" ->ₛ "next") # Ptr |-> qv).
		cancel (sll x_next l1_new).
		apply store_ptr_undef_store_ptr.
	- repeat split_pures.
		+ dump_pre_spatial.
		  rewrite PreH3 in PreH1.
		  unfold split_rec_rel in *.
		  erewrite (program_para_equiv (split_rec_rel_unfold)) in PreH1.
		  unfold split_rec_rel_f in PreH1.
		  rewrite bind_assoc in PreH1.
		  change (safeExec ATrue
		    (x0 <- split_rec_rel' (l1_new, x_data_2 :: l1_2, x_data2_2 :: l2_2) ;;
		     (fun p => z <- reversepair p ;; reversepair z) x0)
		    X_low_level_spec) in PreH1.
		  setoid_rewrite bind_2_reversepair_equiv_Id in PreH1.
		  rewrite bind_ret_right in PreH1.
		  exact PreH1.
		+ dump_pre_spatial.
		  exact PreH3.
		+ dump_pre_spatial.
		  exact PreH2.
Qed.

Lemma proof_of_split_while_entail_wit_6_2 : split_while_entail_wit_6_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (sll_zero x l_new).
	- dump_pre_spatial.
		unfold NULL.
		lia.
	- Intros_p Hl.
		Exists qv_2.
		Exists p_head.
		Exists nil.
		Exists (x_data :: l1_2).
		Exists l2_2.
		repeat split_pure_spatial.
		+ rewrite Hp.
		  cancel (q_pre # Ptr |-> qv_2).
		  cancel (sll qv_2 l2_2).
		  cancel (p_pre # Ptr |-> p_head).
		  simpl sll.
          Exists p_next.
          split_pure_spatial.
		  * cancel.
            cancel.
          * split_pures; dump_pre_spatial.
		    reflexivity.
            auto.
		+ dump_pre_spatial.
			rewrite Hl in PreH2.
			unfold split_rec_rel in *.
			erewrite (program_para_equiv (split_rec_rel_unfold)) in PreH2.
			unfold split_rec_rel_f in PreH2.
			unfold reversepair in PreH2.
			prog_nf in PreH2.
			unfold split_rec_rel'.
			erewrite (program_para_equiv (split_rec_rel_unfold)).
			unfold split_rec_rel_f.
			exact PreH2.
Qed.

Lemma proof_of_split_while_return_wit_1 : split_while_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (sll_zero x l).
	- dump_pre_spatial.
		unfold NULL.
		lia.
	- Intros_p Hl.
		Exists qv.
		Exists pv.
		Exists l1.
		Exists l2.
		repeat split_pure_spatial.
		+ cancel (p_pre # Ptr |-> pv).
			cancel (sll pv l1).
			cancel (q_pre # Ptr |-> qv).
			cancel (sll qv l2).
		+ dump_pre_spatial.
			rewrite Hl in PreH2.
			unfold split_rec_rel in PreH2.
			erewrite (program_para_equiv (split_rec_rel_unfold)) in PreH2.
			unfold split_rec_rel_f in PreH2.
			unfold maketuple in PreH2.
			exact PreH2.
Qed.
