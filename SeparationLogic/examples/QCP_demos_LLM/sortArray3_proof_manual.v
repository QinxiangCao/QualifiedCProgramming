Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import sortArray3_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sortArray_lib.
Local Open Scope sac.

Lemma proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Proof.
	pre_process.
	Exists l nil l.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
		cancel ((returnSize_pre) # Int |-> numsSize_pre).
	- split_pures.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. simpl. rewrite app_nil_r. reflexivity.
		+ dump_pre_spatial. symmetry. exact PreH2.
		+ dump_pre_spatial. simpl. reflexivity.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. rewrite PreH2. lia.
		+ dump_pre_spatial. apply Permutation_refl.
		+ dump_pre_spatial.
			unfold prefix_suffix_sorted.
			intros x HIn.
			simpl.
			auto.
Qed.

Lemma proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Proof.
	pre_process.
	destruct l1_2.
	- rewrite Zlength_nil in PreH9. lia.
	- Exists nil z l1_2 l2_2 l3_2.
		split_pure_spatial.
		+ cancel ((returnSize_pre) # Int |-> numsSize_pre).
			cancel (IntArray.full nums_pre numsSize_pre l3_2).
		+ assert (Hlen_unsorted : numsSize_pre - i = Zlength (app nil (cons z l1_2))).
			{ simpl.
				assert (Heqsum : numsSize_pre = Zlength (z :: l1_2) + i).
				{ pose proof (Permutation_length PreH10) as Hperm.
					apply f_equal with (f := Z.of_nat) in Hperm.
					repeat rewrite <- Zlength_correct in Hperm.
					rewrite <- PreH5 in Hperm.
					rewrite PreH4 in Hperm.
					rewrite Zlength_app in Hperm.
					rewrite <- PreH6 in Hperm.
					exact Hperm. }
				lia. }
			assert (Hnil_ps : prefix_suffix_sorted nil (cons z nil)).
			{ unfold prefix_suffix_sorted.
				intros x HIn.
				inversion HIn. }
			split_pures.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. rewrite PreH4. simpl. reflexivity.
			* dump_pre_spatial. exact PreH5.
			* dump_pre_spatial. exact PreH6.
			* dump_pre_spatial. exact PreH7.
			* dump_pre_spatial. exact PreH8.
			* dump_pre_spatial. exact PreH1.
			* dump_pre_spatial. simpl. reflexivity.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. exact Hlen_unsorted.
			* dump_pre_spatial. exact PreH10.
			* dump_pre_spatial. exact PreH11.
			* dump_pre_spatial. exact PreH12.
			* dump_pre_spatial. exact Hnil_ps.
Qed.

Lemma proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1.
Proof.
	pre_process.
	destruct l2_2.
	- rewrite PreH11 in PreH2.
		rewrite PreH14 in PreH2.
		rewrite Zlength_app in PreH2.
		rewrite Zlength_cons in PreH2.
		rewrite Zlength_nil in PreH2.
		simpl in PreH2.
		lia.
	- assert (Hjkey : Znth j l3_2 0 = key_2).
		{ rewrite PreH5.
			rewrite app_Znth1 by (rewrite <- PreH14; lia).
			rewrite PreH11.
			rewrite app_Znth2 by lia.
			replace (Zlength l1_2 - Zlength l1_2) with 0 by lia.
			simpl.
			reflexivity. }
		assert (Hj1z : Znth (j + 1) l3_2 0 = z).
		{ rewrite PreH5.
			rewrite app_Znth1 by (rewrite <- PreH14; lia).
			rewrite PreH11.
			rewrite app_Znth2 by lia.
			replace (Zlength l1_2 + 1 - Zlength l1_2) with 1 by lia.
			change (Znth 1 (key_2 :: z :: l2_2) 0) with z.
			reflexivity. }
		assert (Hz : z < key_2) by (rewrite Hjkey, Hj1z in PreH1; lia).
		assert (Hsorted : prefix_suffix_sorted (l1_2 ++ z :: key_2 :: l2_2) l4_2).
		{ eapply prefix_suffix_sorted_prefix_perm_local.
			- apply (perm_swap_with_prefix l1_2 nil l2_2 key_2 z).
			- exact PreH17. }
		Exists (l1_2 ++ [z]) key_2 l2_2 l4_2 (replace_Znth (j + 1) key_2 (replace_Znth j z l3_2)).
		assert (Harray :
			replace_Znth (j + 1) key_2 (replace_Znth j z l3_2) =
			(l1_2 ++ [z]) ++ key_2 :: l2_2 ++ l4_2).
		{ rewrite PreH5.
			rewrite PreH11.
			assert (Hfirst :
				replace_Znth (Zlength l1_2) z ((l1_2 ++ key_2 :: z :: l2_2) ++ l4_2) =
				(l1_2 ++ z :: z :: l2_2) ++ l4_2).
			{ apply (replace_Znth_boundary_app_local l1_2 (z :: l2_2) l4_2 z key_2). }
			rewrite Hfirst.
			assert (Hprefix_len : Zlength (l1_2 ++ [z]) = Zlength l1_2 + 1).
			{ change [z] with (z :: nil).
				rewrite Zlength_app.
				rewrite Zlength_cons.
				rewrite Zlength_nil.
				lia. }
			replace ((l1_2 ++ z :: z :: l2_2) ++ l4_2) with (((l1_2 ++ [z]) ++ z :: l2_2) ++ l4_2) by (simpl; rewrite <- !app_assoc; reflexivity).
			rewrite <- Hprefix_len.
			replace ((l1_2 ++ [z]) ++ key_2 :: l2_2 ++ l4_2) with (((l1_2 ++ [z]) ++ key_2 :: l2_2) ++ l4_2) by (rewrite <- !app_assoc; reflexivity).
			apply (replace_Znth_boundary_app_local (l1_2 ++ [z]) l2_2 l4_2 key_2 z). }
		split_pure_spatial.
		+ cancel ((returnSize_pre) # Int |-> numsSize_pre).
			rewrite Hjkey, Hj1z.
			cancel (IntArray.full nums_pre numsSize_pre (replace_Znth (j + 1) key_2 (replace_Znth j z l3_2))).
		+ split_pures.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. rewrite Harray. simpl. rewrite <- !app_assoc. reflexivity.
			* dump_pre_spatial. exact PreH6.
			* dump_pre_spatial. exact PreH7.
			* dump_pre_spatial. exact PreH8.
			* dump_pre_spatial. exact PreH9.
			* dump_pre_spatial. exact PreH10.
			* dump_pre_spatial. rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. simpl. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial.
				rewrite PreH14.
				rewrite !Zlength_app.
				rewrite !Zlength_cons.
				rewrite Zlength_nil.
				simpl.
				lia.
			* dump_pre_spatial.
				rewrite PreH5 in PreH15.
				rewrite Harray.
				replace ((l1_2 ++ [z]) ++ key_2 :: l2_2 ++ l4_2) with ((l1_2 ++ z :: key_2 :: l2_2) ++ l4_2) by (simpl; rewrite <- !app_assoc; reflexivity).
				eapply Permutation_trans.
				{ exact PreH15. }
				{
					replace ((l1_2 ++ key_2 :: z :: l2_2) ++ l4_2) with (l1_2 ++ key_2 :: nil ++ z :: (l2_2 ++ l4_2)) by (simpl; rewrite <- !app_assoc; reflexivity).
					replace ((l1_2 ++ z :: key_2 :: l2_2) ++ l4_2) with (l1_2 ++ z :: nil ++ key_2 :: (l2_2 ++ l4_2)) by (simpl; rewrite <- !app_assoc; reflexivity).
					apply (perm_swap_with_prefix l1_2 nil (l2_2 ++ l4_2) key_2 z).
				}
			* dump_pre_spatial. exact PreH16.
			* dump_pre_spatial.
				replace (((l1_2 ++ [z]) ++ key_2 :: l2_2)) with (l1_2 ++ z :: key_2 :: l2_2) by (simpl; rewrite <- !app_assoc; reflexivity).
				exact Hsorted.
			* dump_pre_spatial.
				apply prefix_suffix_sorted_snoc_singleton_local.
				{ exact PreH18. }
				{ lia. }
Qed.

Lemma proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2.
Proof.
	pre_process.
	destruct l2_2.
	- rewrite PreH11 in PreH2.
		rewrite PreH14 in PreH2.
		rewrite Zlength_app in PreH2.
		rewrite Zlength_cons in PreH2.
		rewrite Zlength_nil in PreH2.
		simpl in PreH2.
		lia.
	- assert (Hz : key_2 <= z).
		{ assert (Hjkey : Znth j l3_2 0 = key_2).
			{ rewrite PreH5.
				rewrite app_Znth1 by (rewrite <- PreH14; lia).
				rewrite PreH11.
				rewrite app_Znth2 by lia.
				replace (Zlength l1_2 - Zlength l1_2) with 0 by lia.
				simpl.
				reflexivity. }
			assert (Hj1z : Znth (j + 1) l3_2 0 = z).
			{ rewrite PreH5.
				rewrite app_Znth1 by (rewrite <- PreH14; lia).
				rewrite PreH11.
				rewrite app_Znth2 by lia.
				replace (Zlength l1_2 + 1 - Zlength l1_2) with 1 by lia.
				change (Znth 1 (key_2 :: z :: l2_2) 0) with z.
				reflexivity. }
			rewrite Hjkey, Hj1z in PreH1.
			lia. }
		Exists (l1_2 ++ [key_2]) z l2_2 l4_2 l3_2.
		split_pure_spatial.
		+ cancel ((returnSize_pre) # Int |-> numsSize_pre).
			cancel (IntArray.full nums_pre numsSize_pre l3_2).
		+ split_pures.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. rewrite PreH5. simpl. rewrite <- !app_assoc. reflexivity.
			* dump_pre_spatial. exact PreH6.
			* dump_pre_spatial. exact PreH7.
			* dump_pre_spatial. exact PreH8.
			* dump_pre_spatial. exact PreH9.
			* dump_pre_spatial. exact PreH10.
			* dump_pre_spatial. rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. simpl. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial.
				rewrite PreH14.
				rewrite !Zlength_app.
				rewrite !Zlength_cons.
				rewrite Zlength_nil.
				simpl.
				lia.
			* dump_pre_spatial. exact PreH15.
			* dump_pre_spatial. exact PreH16.
			* dump_pre_spatial.
				replace (((l1_2 ++ [key_2]) ++ z :: l2_2)) with (l1_2 ++ key_2 :: z :: l2_2) by (simpl; rewrite <- !app_assoc; reflexivity).
				exact PreH17.
			* dump_pre_spatial.
				eapply prefix_suffix_sorted_snoc_singleton_local.
				{ eapply prefix_suffix_sorted_singleton_le_local.
					- exact PreH18.
					- exact Hz. }
				{ exact Hz. }
Qed.

Lemma proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Proof.
	pre_process.
	assert (Heq : j + 1 = numsSize_pre - i) by lia.
	assert (Hl2 : Zlength l2_2 = 0).
	{ rewrite PreH10 in Heq.
		rewrite PreH13 in Heq.
		rewrite Zlength_app in Heq.
		rewrite Zlength_cons in Heq.
		simpl in Heq.
		lia. }
	apply Zlength_nil_inv in Hl2.
	subst l2_2.
	assert (Hlb_key : lowerbound key l4).
	{ unfold prefix_suffix_sorted in PreH16.
		specialize (PreH16 key).
		simpl in PreH16.
		apply PreH16.
		rewrite in_app_iff.
		right.
		simpl.
		auto. }
	assert (Hinc : increasing (key :: l4)).
	{ apply increasing_cons_local; assumption. }
	assert (Hps : prefix_suffix_sorted l1_2 (key :: l4)).
	{ apply prefix_suffix_sorted_extend_suffix_local.
		- exact PreH17.
		- unfold prefix_suffix_sorted in *.
			intros x Hx.
			apply PreH16.
			simpl.
			rewrite in_app_iff.
			left.
			exact Hx. }
	Exists l1_2 (key :: l4) l3_2.
	split_pure_spatial.
	- cancel ((returnSize_pre) # Int |-> numsSize_pre).
		cancel (IntArray.full nums_pre numsSize_pre l3_2).
	- split_pures.
		+ dump_pre_spatial. exact PreH2.
		+ dump_pre_spatial. exact PreH3.
		+ dump_pre_spatial. rewrite PreH4. simpl. rewrite <- app_assoc. reflexivity.
		+ dump_pre_spatial. exact PreH5.
		+ dump_pre_spatial. rewrite PreH6. rewrite Zlength_cons. lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. rewrite <- PreH10. lia.
		+ dump_pre_spatial. exact PreH14.
		+ dump_pre_spatial. exact Hinc.
		+ dump_pre_spatial. exact Hps.
Qed.

Lemma proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Proof.
	pre_process.
	assert (Hi : i = numsSize_pre - 1) by lia.
	assert (Hlen_l3 : Zlength l3 = numsSize_pre).
	{ pose proof (Permutation_length PreH10) as Hperm.
		apply f_equal with (f := Z.of_nat) in Hperm.
		repeat rewrite <- Zlength_correct in Hperm.
		rewrite <- PreH5 in Hperm.
		symmetry.
		exact Hperm. }
	assert (Hlen_l1 : Zlength l1_2 = 1).
	{ rewrite PreH4 in Hlen_l3.
		rewrite Zlength_app in Hlen_l3.
		rewrite <- PreH6 in Hlen_l3.
		rewrite Hi in Hlen_l3.
		lia. }
	destruct l1_2.
	- rewrite Zlength_nil in PreH9. lia.
	- assert (Hlen_tail : Zlength l1_2 = 0).
		{ rewrite Zlength_cons in Hlen_l1. simpl in Hlen_l1. lia. }
		apply Zlength_nil_inv in Hlen_tail.
		subst l1_2.
		assert (Hlb : lowerbound z l2).
		{ unfold prefix_suffix_sorted in PreH12.
			apply PreH12.
			simpl.
			auto. }
		assert (Hinc : increasing (z :: l2)).
		{ apply increasing_cons_local; assumption. }
		Exists (z :: l2).
		split_pure_spatial.
		+ rewrite PreH4.
			simpl.
			cancel (IntArray.full nums_pre numsSize_pre (z :: l2)).
			cancel ((returnSize_pre) # Int |-> numsSize_pre).
		+ split_pures.
			* dump_pre_spatial. rewrite PreH4 in PreH10. simpl in PreH10. exact PreH10.
			* dump_pre_spatial. exact Hinc.
			* dump_pre_spatial. rewrite PreH4 in Hlen_l3. simpl in Hlen_l3. exact Hlen_l3.
Qed.

Lemma proof_of_sortArray_return_wit_2 : sortArray_return_wit_2.
Proof.
	pre_process.
	assert (numsSize_pre = 1) by lia.
	assert (Hlen_l : Zlength l = numsSize_pre) by exact PreH2.
	subst numsSize_pre.
	destruct l.
	- rewrite Zlength_nil in *. lia.
	- destruct l.
		+ Exists [z].
			split_pure_spatial.
			* cancel (IntArray.full nums_pre 1 [z]).
				cancel ((returnSize_pre) # Int |-> 1).
			* split_pures; [dump_pre_spatial; apply Permutation_refl | dump_pre_spatial; simpl; auto].
		+ pose proof (Zlength_nonneg l) as Hl_nonneg.
			exfalso.
			assert (Htwo : 2 <= Zlength (z :: z0 :: l)).
			{ rewrite !Zlength_cons. lia. }
			lia.
Qed.
