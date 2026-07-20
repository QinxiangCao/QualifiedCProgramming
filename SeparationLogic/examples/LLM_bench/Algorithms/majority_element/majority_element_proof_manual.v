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
From SimpleC.EE.LLM_bench.Algorithms.majority_element Require Import majority_element_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.LLM_bench.Algorithms.majority_element Require Import majority_element_lib.
Local Open Scope sac.

Ltac grab H pat :=
	match goal with
	| H0 : pat |- _ => pose proof H0 as H
	end.

Lemma proof_of_majorityElement_entail_wit_1 : majorityElement_entail_wit_1.
Proof.
	pre_process.
	Exists x_2.
	Exists nil.
	Exists l.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	- split_pures.
	  + dump_pre_spatial.
	    rewrite app_nil_l.
	    reflexivity.
	  + dump_pre_spatial.
	    rewrite Zlength_nil.
	    reflexivity.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact PreH2.
	  + dump_pre_spatial.
	    exact PreH3.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact PreH1.
	  + dump_pre_spatial.
	    apply majority_on_reduced_init.
	    exact PreH1.
Qed.

Lemma proof_of_majorityElement_entail_wit_2_1 : majorityElement_entail_wit_2_1.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength.
	Intros_p Hlen.
	assert (Hlt : i < Zlength (l1_2 ++ l2_2)).
	{ rewrite <- PreH3. rewrite Hlen. exact PreH2. }
	destruct (app_Znth_suffix_cons l1_2 l2_2 i 0 PreH4 Hlt) as [a [rest [Hl2 Hz]]].
	assert (Hzl : Znth i l 0 = a).
	{ rewrite PreH3. exact Hz. }
	unfold MajorityOnReduced in PreH12.
	destruct PreH12 as [Hvote Hmajor].
	Exists x_2.
	Exists ((l1_2 ++ a :: nil)%list).
	Exists rest.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	- split_pures.
	  + dump_pre_spatial.
	    rewrite PreH3.
	    rewrite Hl2.
	    rewrite <- app_assoc.
	    reflexivity.
	  + dump_pre_spatial.
	    rewrite Zlength_app, Zlength_cons, Zlength_nil.
	    rewrite PreH4.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact PreH7.
	  + dump_pre_spatial.
	    exact PreH8.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact PreH11.
	  + dump_pre_spatial.
	    rewrite Hzl.
	    rewrite PreH1.
	    rewrite Hl2 in Hmajor.
	    rewrite PreH1 in Hmajor.
	    apply (majority_on_reduced_reset x_2 candidate a rest).
	    exact Hmajor.
Qed.

Lemma proof_of_majorityElement_entail_wit_2_2 : majorityElement_entail_wit_2_2.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength.
	Intros_p Hlen.
	assert (Hlt : i < Zlength (l1_2 ++ l2_2)).
	{ rewrite <- PreH4. rewrite Hlen. exact PreH3. }
	destruct (app_Znth_suffix_cons l1_2 l2_2 i 0 PreH5 Hlt) as [a [rest [Hl2 Hz]]].
	rewrite PreH4 in PreH1.
	rewrite Hz in PreH1.
	unfold MajorityOnReduced in PreH13.
	destruct PreH13 as [Hvote Hmajor].
	assert (0 < vote) by lia.
	Exists x_2.
	Exists ((l1_2 ++ a :: nil)%list).
	Exists rest.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	- split_pures.
	  + dump_pre_spatial.
	    rewrite PreH4.
	    rewrite Hl2.
	    rewrite <- app_assoc.
	    reflexivity.
	  + dump_pre_spatial.
	    rewrite Zlength_app, Zlength_cons, Zlength_nil.
	    rewrite PreH5.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact PreH8.
	  + dump_pre_spatial.
	    exact PreH9.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact PreH12.
	  + dump_pre_spatial.
	    rewrite Hl2 in Hmajor.
	    rewrite PreH1 in Hmajor.
	    apply majority_on_reduced_same; [lia | exact Hmajor].
Qed.

Lemma proof_of_majorityElement_entail_wit_2_3 : majorityElement_entail_wit_2_3.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength.
	Intros_p Hlen.
	assert (Hlt : i < Zlength (l1_2 ++ l2_2)).
	{ rewrite <- PreH4. rewrite Hlen. exact PreH3. }
	destruct (app_Znth_suffix_cons l1_2 l2_2 i 0 PreH5 Hlt) as [a [rest [Hl2 Hz]]].
	assert (Hzl : Znth i l 0 = a).
	{ rewrite PreH4. exact Hz. }
	unfold MajorityOnReduced in PreH13.
	destruct PreH13 as [Hvote Hmajor].
	Exists x_2.
	Exists ((l1_2 ++ a :: nil)%list).
	Exists rest.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	- split_pures.
	  + dump_pre_spatial.
	    rewrite PreH4.
	    rewrite Hl2.
	    rewrite <- app_assoc.
	    reflexivity.
	  + dump_pre_spatial.
	    rewrite Zlength_app, Zlength_cons, Zlength_nil.
	    rewrite PreH5.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact PreH8.
	  + dump_pre_spatial.
	    exact PreH9.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact PreH12.
	  + dump_pre_spatial.
	    rewrite Hl2 in Hmajor.
	    apply majority_on_reduced_cancel with (a := a);
	      [lia | rewrite <- Hzl; exact PreH1 | exact Hmajor].
Qed.

Lemma proof_of_majorityElement_return_wit_1 : majorityElement_return_wit_1.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength.
	Intros_p Hlen.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	- dump_pre_spatial.
	  unfold MajorityOnReduced in PreH11.
	  destruct PreH11 as [Hvote Hmajor].
	  assert (Hi : i = numsSize_pre) by lia.
	  assert (Hl1len : Zlength l1 = numsSize_pre) by lia.
	  assert (Hl2len : Zlength l2 = 0).
	  { rewrite PreH2 in Hlen.
	    rewrite Zlength_app in Hlen.
	    rewrite Hl1len in Hlen.
	    lia. }
	  apply Zlength_nil_inv in Hl2len.
	  subst l2.
	  rewrite app_nil_r in PreH2.
	  subst l.
	  rewrite app_nil_r in Hmajor.
	  pose proof (majority_of_repeated_eq x candidate vote Hvote Hmajor) as Hxc.
	  subst candidate.
	  exact PreH10.
Qed.
