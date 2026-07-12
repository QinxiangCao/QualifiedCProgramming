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
Require Import Coq.micromega.Lia.
Import ListNotations.
From SimpleC.EE.QCP_demos_LLM Require Import sortArray2_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sortArray_lib.
Local Open Scope sac.

Lemma proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Proof.
	pre_process.
	Exists nil l l.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	  cancel ((returnSize_pre) # Int |-> numsSize_pre).
	- split_pures.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. simpl. reflexivity.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. simpl. reflexivity.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. apply Permutation_refl.
	  + dump_pre_spatial.
	    unfold prefix_suffix_sorted.
	    intros x HIn.
	    inversion HIn.
Qed.

Lemma proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Proof.
	pre_process.
	destruct l2_2 as [ | z l2_2 ].
	- pose proof (Permutation_length PreH9) as Hperm.
	  repeat rewrite Zlength_correct in *.
	  rewrite PreH4 in Hperm.
	  rewrite length_app in Hperm.
	  simpl in Hperm.
	  lia.
	- Exists l1_2 z nil l2_2 l3_2.
	  split_pure_spatial.
	  + cancel ((returnSize_pre) # Int |-> numsSize_pre).
	    cancel (IntArray.full nums_pre numsSize_pre l3_2).
	  + split_pures.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. rewrite PreH4. simpl. reflexivity.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial.
	      rewrite PreH6.
	      rewrite Zlength_app.
	      rewrite Zlength_cons.
	      rewrite Zlength_nil.
	      simpl.
	      lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. exact PreH9.
	    * dump_pre_spatial. exact PreH10.
	    * dump_pre_spatial. exact PreH11.
Qed.

Lemma proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1.
Proof.
	pre_process.
	destruct l4_2 as [ | z l4_2 ].
	- rewrite Zlength_correct in PreH6.
	  erewrite Permutation_length in PreH6 by exact PreH13.
	  rewrite PreH5 in PreH6.
	  repeat rewrite <- Zlength_correct in PreH6.
	  rewrite app_nil_r in PreH6.
	  rewrite <- PreH10 in PreH6.
	  lia.
	- assert (Hi : Znth i l3_2 0 = key_2).
	  { rewrite PreH7.
	    rewrite PreH5.
	    rewrite app_Znth2 by lia.
	    replace (Zlength l1_2 - Zlength l1_2) with 0 by lia.
	    simpl.
	    reflexivity. }
	  assert (Hjz : Znth j l3_2 0 = z).
	  { rewrite PreH10.
	    rewrite PreH5.
	    assert (Hshape : l1_2 ++ (key_2 :: l2_2) ++ z :: l4_2 =
	                     (l1_2 ++ key_2 :: l2_2) ++ z :: l4_2).
	    { rewrite <- app_assoc. reflexivity. }
	    rewrite Hshape.
	    rewrite app_Znth2 by (pose proof (Zlength_nonneg (z :: l4_2)) as Hlen; lia).
	    replace (Zlength (l1_2 ++ key_2 :: l2_2) - Zlength (l1_2 ++ key_2 :: l2_2)) with 0 by lia.
	    simpl.
	    reflexivity. }
	  assert (Hz : z < key_2) by (rewrite Hjz, Hi in PreH1; exact PreH1).
	  assert (Hzlb : lowerbound z l2_2).
	  { apply (lowerbound_trans z key_2 l2_2); [lia | exact PreH16]. }
	  assert (Hps : prefix_suffix_sorted l1_2 (z :: l2_2 ++ key_2 :: l4_2)).
	  { eapply prefix_suffix_sorted_perm_local.
	    - exact PreH15.
	    - simpl. apply (perm_swap_with_prefix nil l2_2 l4_2 key_2 z). }
	  Exists l1_2 z (l2_2 ++ [key_2]) l4_2 (replace_Znth j key_2 (replace_Znth i z l3_2)).
	  rewrite Hi.
	  rewrite Hjz.
	  assert (Harray :
	    replace_Znth j key_2 (replace_Znth i z l3_2) =
	    l1_2 ++ z :: l2_2 ++ key_2 :: l4_2).
	  { rewrite PreH5.
	    rewrite PreH7.
	    rewrite PreH10.
	    assert (Hfirst :
	      replace_Znth (Zlength l1_2) z (l1_2 ++ (key_2 :: l2_2) ++ z :: l4_2) =
	      l1_2 ++ z :: l2_2 ++ z :: l4_2).
	    { rewrite replace_Znth_app_r by lia.
	      rewrite replace_Znth_nothing by lia.
	      replace (Zlength l1_2 - Zlength l1_2) with 0 by lia.
	      unfold replace_Znth.
	      simpl.
	      reflexivity. }
	    rewrite Hfirst.
	    assert (Hshape : l1_2 ++ z :: l2_2 ++ z :: l4_2 = (l1_2 ++ z :: l2_2) ++ z :: l4_2).
	    { rewrite <- app_assoc. reflexivity. }
	    rewrite Hshape.
	    assert (Hpref_len : Zlength (l1_2 ++ key_2 :: l2_2) = Zlength (l1_2 ++ z :: l2_2)).
	    { rewrite !Zlength_app. rewrite !Zlength_cons. lia. }
	    rewrite Hpref_len.
	    rewrite replace_Znth_app_r by lia.
	    rewrite replace_Znth_nothing by (rewrite Zlength_app; rewrite Zlength_cons; lia).
	    replace (Zlength (l1_2 ++ z :: l2_2) - Zlength (l1_2 ++ z :: l2_2)) with 0 by lia.
	    unfold replace_Znth.
	    simpl.
	    rewrite <- app_assoc.
	    reflexivity. }
	  split_pure_spatial.
	  + cancel (IntArray.full nums_pre numsSize_pre (replace_Znth j key_2 (replace_Znth i z l3_2))).
	    cancel ((returnSize_pre) # Int |-> numsSize_pre).
	  + split_pures.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial.
	      rewrite Harray.
	      simpl.
	      rewrite <- app_assoc.
	      reflexivity.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial.
	      assert (Hj_len : j = Zlength l1_2 + Zlength l2_2 + 1).
	      { rewrite PreH10. rewrite Zlength_app. rewrite Zlength_cons. simpl. lia. }
	      assert (Hrhs_len : Zlength (l1_2 ++ z :: l2_2 ++ [key_2]) = Zlength l1_2 + Zlength l2_2 + 2).
	      {
	        replace (l1_2 ++ z :: l2_2 ++ [key_2]) with ((l1_2 ++ z :: l2_2) ++ [key_2]) by (rewrite <- app_assoc; reflexivity).
	        rewrite Zlength_app.
	        rewrite Zlength_app.
	        rewrite Zlength_cons.
	        rewrite Zlength_cons.
	        simpl.
	        lia.
	      }
	      lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial.
	      rewrite PreH5 in PreH13.
	      rewrite Harray.
	      eapply Permutation_trans with (l' := l1_2 ++ key_2 :: l2_2 ++ z :: l4_2).
	      { exact PreH13. }
	      { simpl. apply (perm_swap_with_prefix l1_2 l2_2 l4_2 key_2 z). }
	    * dump_pre_spatial. exact PreH14.
	    * dump_pre_spatial.
	      replace ((z :: l2_2 ++ [key_2]) ++ l4_2) with (z :: l2_2 ++ key_2 :: l4_2) by (simpl; rewrite <- app_assoc; reflexivity).
	      exact Hps.
	    * dump_pre_spatial.
	      apply lowerbound_app_cons; [exact Hzlb | lia].
Qed.

Lemma proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2.
Proof.
	pre_process.
	destruct l4_2 as [ | z l4_2 ].
	- rewrite Zlength_correct in PreH6.
	  erewrite Permutation_length in PreH6 by exact PreH13.
	  rewrite PreH5 in PreH6.
	  repeat rewrite <- Zlength_correct in PreH6.
	  rewrite app_nil_r in PreH6.
	  rewrite <- PreH10 in PreH6.
	  lia.
	- assert (Hz : key_2 <= z).
	  { assert (Hi : Znth i l3_2 0 = key_2).
	    { rewrite PreH7.
	      rewrite PreH5.
	      rewrite app_Znth2 by lia.
	      replace (Zlength l1_2 - Zlength l1_2) with 0 by lia.
	      simpl.
	      reflexivity. }
	    assert (Hjz : Znth j l3_2 0 = z).
	    { rewrite PreH10.
	      rewrite PreH5.
	      assert (Hshape : l1_2 ++ (key_2 :: l2_2) ++ z :: l4_2 =
	                       (l1_2 ++ key_2 :: l2_2) ++ z :: l4_2).
	      { rewrite <- app_assoc. reflexivity. }
	      rewrite Hshape.
	      rewrite app_Znth2 by (pose proof (Zlength_nonneg (z :: l4_2)) as Hlen; lia).
	      replace (Zlength (l1_2 ++ key_2 :: l2_2) - Zlength (l1_2 ++ key_2 :: l2_2)) with 0 by lia.
	      simpl.
	      reflexivity. }
	    rewrite Hjz, Hi in PreH1.
	    lia. }
	  Exists l1_2 key_2 (l2_2 ++ [z]) l4_2 l3_2.
	  split_pure_spatial.
	  + cancel ((returnSize_pre) # Int |-> numsSize_pre).
	    cancel (IntArray.full nums_pre numsSize_pre l3_2).
	  + split_pures.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial.
	      rewrite PreH5.
	      simpl.
	      rewrite <- app_assoc.
	      reflexivity.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial.
	      rewrite PreH10.
	      replace (l1_2 ++ key_2 :: l2_2 ++ [z]) with ((l1_2 ++ key_2 :: l2_2) ++ [z]) by (rewrite <- app_assoc; reflexivity).
	      assert (Hlen_snoc : Zlength ((l1_2 ++ key_2 :: l2_2) ++ [z]) = Zlength (l1_2 ++ key_2 :: l2_2) + 1).
	      { rewrite Zlength_app. rewrite Zlength_cons. simpl. lia. }
	      rewrite Hlen_snoc.
	      lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. exact PreH13.
	    * dump_pre_spatial. exact PreH14.
	    * dump_pre_spatial.
	      replace ((key_2 :: l2_2 ++ [z]) ++ l4_2) with ((key_2 :: l2_2) ++ z :: l4_2) by (simpl; rewrite <- app_assoc; reflexivity).
	      exact PreH15.
	    * dump_pre_spatial.
	      apply lowerbound_app_cons; [exact PreH16 | exact Hz].
Qed.

Lemma proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Proof.
	pre_process.
	assert (Hj_eq : j = numsSize_pre) by lia.
	set (prefix := l1_2 ++ key :: l2_2).
	assert (Hprefix : Zlength prefix = numsSize_pre).
	{ unfold prefix. rewrite <- PreH9. lia. }
	assert (Hsplit : l3_2 = prefix ++ l4).
	{ unfold prefix. rewrite <- app_assoc. exact PreH4. }
	pose proof (Permutation_length PreH12) as Hperm.
	apply f_equal with (f := Z.of_nat) in Hperm.
	repeat rewrite <- Zlength_correct in Hperm.
	rewrite Hsplit in Hperm.
	rewrite Zlength_app in Hperm.
	assert (Hl4 : Zlength l4 = 0) by (rewrite <- PreH5 in Hperm; rewrite Hprefix in Hperm; lia).
	apply Zlength_nil_inv in Hl4.
	subst l4.
	assert (Hkey : match l1_2 with | nil => True | y :: l' => last_val_local y l' <= key end).
	{ rewrite app_nil_r in PreH14.
	  apply (prefix_suffix_sorted_last_local l1_2 key l2_2).
	  exact PreH14. }
	assert (Hinc : increasing (l1_2 ++ [key])).
	{ apply increasing_snoc_local.
	  - exact PreH13.
	  - exact Hkey. }
	assert (Hps : prefix_suffix_sorted (l1_2 ++ [key]) l2_2).
	{ rewrite app_nil_r in PreH14.
	  apply prefix_suffix_sorted_snoc_local.
	  - exact PreH14.
	  - exact PreH15. }
	Exists (l1_2 ++ [key]) l2_2 l3_2.
	split_pure_spatial.
	- cancel ((returnSize_pre) # Int |-> numsSize_pre).
	  cancel (IntArray.full nums_pre numsSize_pre l3_2).
	- split_pures.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. rewrite PreH4. rewrite app_nil_r. rewrite <- app_assoc. reflexivity.
	  + dump_pre_spatial. exact PreH5.
	  + dump_pre_spatial.
	    rewrite Zlength_app.
	    rewrite Zlength_cons.
	    rewrite Zlength_nil.
	    lia.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. exact PreH12.
	  + dump_pre_spatial. exact Hinc.
	  + dump_pre_spatial. exact Hps.
Qed.

Lemma proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Proof.
	pre_process.
	assert (Hlen1 : Zlength l1_2 = numsSize_pre) by lia.
	assert (Hi : i = numsSize_pre) by lia.
	subst i.
	pose proof (Permutation_length PreH9) as Hperm.
	apply f_equal with (f := Z.of_nat) in Hperm.
	repeat rewrite <- Zlength_correct in Hperm.
	rewrite PreH4 in Hperm.
	rewrite Zlength_app in Hperm.
	assert (Hl2 : Zlength l2 = 0) by (rewrite <- PreH5 in Hperm; rewrite Hlen1 in Hperm; lia).
	apply Zlength_nil_inv in Hl2.
	subst l2.
	subst l3.
	rewrite app_nil_r in PreH9.
	rewrite app_nil_r.
	Exists l1_2.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l1_2).
	  cancel ((returnSize_pre) # Int |-> numsSize_pre).
	- split_pures.
	  + dump_pre_spatial. exact PreH9.
	  + dump_pre_spatial. exact PreH10.
	  + dump_pre_spatial. exact Hlen1.
Qed.
