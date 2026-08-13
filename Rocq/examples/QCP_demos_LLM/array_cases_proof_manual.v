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
From SimpleC.EE.QCP_demos_LLM Require Import array_cases_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Local Open Scope sac.

Lemma replace_Znth_boundary_local {A: Type} :
	forall (prefix tail: list A) x y,
		replace_Znth (Zlength prefix) x (prefix ++ y :: tail) = prefix ++ x :: tail.
Proof.
	induction prefix; intros tail x y.
	- reflexivity.
	- simpl.
	  rewrite Zlength_cons.
	  pose proof (Zlength_nonneg prefix) as Hlen.
	  assert (Hpos : Z.succ (Zlength prefix) > 0) by lia.
	  rewrite (replace_Znth_cons (Z.succ (Zlength prefix)) x a (prefix ++ y :: tail)) by exact Hpos.
	  replace (Z.succ (Zlength prefix) - 1) with (Zlength prefix) by lia.
	  simpl.
	  f_equal.
	  apply IHprefix.
Qed.

Lemma replace_Znth_length_local {A: Type}:
	forall (l: list A) n a,
		Zlength (replace_Znth n a l) = Zlength l.
Proof.
	intros l n.
	unfold replace_Znth.
	remember (Z.to_nat n) as k; clear Heqk.
	revert k; induction l; intros.
	- destruct k; simpl; easy.
	- destruct k; simpl; repeat rewrite Zlength_cons; auto.
	  rewrite IHl; auto.
Qed.

Lemma Zlength_sublist_le_local {A: Type}:
	forall lo hi (l: list A),
		0 <= lo <= hi ->
		Zlength (sublist lo hi l) <= hi - lo.
Proof.
	intros lo hi l Hrange.
	rewrite Zlength_sublist'.
	destruct (Nat.leb (Z.to_nat hi) (length l)) eqn:Hcmp.
	- apply Nat.leb_le in Hcmp.
	  rewrite Nat.min_l by lia.
	  replace (hi - lo) with (Z.of_nat (Z.to_nat hi - Z.to_nat lo)).
	  2: {
		rewrite Nat2Z.inj_sub by lia.
		rewrite !Z2Nat.id by lia.
		lia.
	  }
	  lia.
	- apply Nat.leb_gt in Hcmp.
	  rewrite Nat.min_r by lia.
	  replace (hi - lo) with (Z.of_nat (Z.to_nat hi - Z.to_nat lo)).
	  2: {
		rewrite Nat2Z.inj_sub by lia.
		rewrite !Z2Nat.id by lia.
		lia.
	  }
	  apply Nat2Z.inj_le.
	  lia.
Qed.

Lemma sublist_full_length_inv_local {A: Type}:
	forall lo hi (l: list A),
		0 <= lo < hi ->
		Zlength (sublist lo hi l) = hi - lo ->
		hi <= Zlength l.
Proof.
	intros lo hi l Hrange Hlen.
	rewrite Zlength_sublist' in Hlen.
	replace (hi - lo) with (Z.of_nat (Z.to_nat hi - Z.to_nat lo)) in Hlen.
	2: {
	  rewrite Nat2Z.inj_sub by lia.
	  rewrite !Z2Nat.id by lia.
	  lia.
	}
	apply Nat2Z.inj in Hlen.
	destruct (Nat.leb (Z.to_nat hi) (length l)) eqn:Hcmp.
	- apply Nat.leb_le in Hcmp.
	  rewrite Zlength_correct.
	  apply Nat2Z.inj_le in Hcmp.
	  rewrite Z2Nat.id in Hcmp by lia.
	  exact Hcmp.
	- apply Nat.leb_gt in Hcmp.
	  rewrite Nat.min_r in Hlen by lia.
	  lia.
Qed.

Lemma proof_of_arr_sum_entail_wit_1 : arr_sum_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_arr_sum_entail_wit_2 : arr_sum_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply UIntArray.full_Zlength.
	Intros_p Hlen.
	split_pures.
	split_pure_spatial.
	- cancel (UIntArray.full a_pre n_pre l).
	- split_pures.
	  + dump_pre_spatial. exact PreH2.
	  + dump_pre_spatial. exact PreH3.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. exact PreH6.
	  + dump_pre_spatial.
	    rewrite PreH7.
	    rewrite (sublist_split 0 (i_2 + 1) i_2 l) by lia.
	    rewrite sum_app.
	    rewrite (sublist_single 0 i_2 l) by lia.
	    simpl.
	    assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH6.
	    destruct (Z.eq_dec i_2 0) as [Hi0 | Hi0].
	    * subst i_2. simpl in *. subst ret.
	      assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
	      rewrite unsigned_last_nbits_eq by lia.
	      replace (Znth 0 l 0 + 0) with (Znth 0 l 0) by lia.
	      reflexivity.
	    * assert (Hsublen : i_2 = Z.of_nat (length (sublist 0 i_2 l))) by (rewrite sublist_length; lia).
	      assert (Hret_bound : 0 <= sum (sublist 0 i_2 l) < i_2 * 100).
	      {
	        replace (i_2 * 100) with (Z.of_nat (length (sublist 0 i_2 l)) * 100).
	        2: { rewrite <- Hsublen. reflexivity. }
	        apply sum_bound_lt.
	        - intro Hnil. rewrite Hnil in Hsublen. simpl in Hsublen. lia.
	        - intros idx Hidx.
	          rewrite <- Hsublen in Hidx.
	          rewrite Znth_sublist_lt by lia.
	          apply Hrange.
	          lia.
	      }
	      assert (Hcur : 0 <= Znth i_2 l 0 < 100) by (apply Hrange; lia).
	      rewrite unsigned_last_nbits_eq by lia.
	      rewrite Z.add_0_r.
	      reflexivity.
Qed.

Lemma proof_of_arr_sum_return_wit_1 : arr_sum_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply UIntArray.full_length.
	Intros_p Hlen.
	split_pure_spatial.
	- cancel (UIntArray.full a_pre n_pre l).
	- dump_pre_spatial.
	  rewrite PreH7.
	  assert (Hi : i_2 = n_pre) by lia.
	  subst i_2.
	  rewrite <- Hlen.
	  unfold sublist.
	  simpl.
	  rewrite firstn_all2 by lia.
	  reflexivity.
Qed.

Lemma proof_of_array_copy1_entail_wit_1 : array_copy1_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (IntArray.undef_full_to_undef_seg dest_pre n_pre).
	change (sublist 0 0 l) with (@nil Z).
	rewrite (IntArray.seg_empty dest_pre 0 0).
	split_pure_spatial.
	- cancel (IntArray.undef_seg dest_pre 0 n_pre).
	  cancel (IntArray.full src_pre n_pre l).
	- split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_array_copy1_entail_wit_2 : array_copy1_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply (IntArray.full_Zlength src_pre).
	Intros_p Hlen.
	replace (sublist 0 (i + 1) l) with (sublist 0 i l ++ Znth i l 0 :: nil).
	2: {
		rewrite (sublist_split 0 (i + 1) i l) by lia.
		rewrite (sublist_single 0 i l) by lia.
		reflexivity.
	}
	split_pure_spatial.
	- cancel (IntArray.seg dest_pre 0 (i + 1) (sublist 0 i l ++ Znth i l 0 :: nil)).
	  cancel (IntArray.full src_pre n_pre l).
	  cancel (IntArray.undef_seg dest_pre (i + 1) n_pre).
	- split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_array_copy1_return_wit_1 : array_copy1_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply (IntArray.full_Zlength src_pre).
	Intros_p Hlen.
	assert (Hi : i = n_pre) by lia.
	subst i.
	assert (HlenZ : Zlength l = n_pre) by (pose proof (Zlength_correct l); lia).
	rewrite (sublist_self l n_pre) by exact (eq_sym HlenZ).
	rewrite IntArray.undef_seg_empty.
	sep_apply (IntArray.seg_to_full dest_pre 0 n_pre l).
	replace (dest_pre + 0 * sizeof ( INT )) with dest_pre by lia.
	rewrite Z.sub_0_r.
	cancel (IntArray.full dest_pre n_pre l).
	cancel (IntArray.full src_pre n_pre l).
Qed.

Lemma proof_of_array_concat_entail_wit_1 : array_concat_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	sep_apply_l_atomic (IntArray.undef_full_to_undef_seg ret_pre (n_pre + m_pre)).
	change (sublist 0 0 l1) with (@nil Z).
	rewrite (IntArray.seg_empty ret_pre 0 0).
	split_pure_spatial.
	- cancel (IntArray.undef_seg ret_pre 0 (n_pre + m_pre)).
	  cancel (IntArray.full a_pre n_pre l1).
	  cancel (IntArray.full b_pre m_pre l2).
	- split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_array_concat_entail_wit_2 : array_concat_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply (IntArray.full_Zlength a_pre).
	Intros_p Hlen.
	replace (sublist 0 (i + 1) l1) with (sublist 0 i l1 ++ Znth i l1 0 :: nil).
	2: {
		rewrite (sublist_split 0 (i + 1) i l1) by lia.
		rewrite (sublist_single 0 i l1) by lia.
		reflexivity.
	}
	split_pure_spatial.
	- cancel (IntArray.seg ret_pre 0 (i + 1) (sublist 0 i l1 ++ Znth i l1 0 :: nil)).
	  cancel (IntArray.full a_pre n_pre l1).
	  cancel (IntArray.undef_seg ret_pre (i + 1) (n_pre + m_pre)).
	  cancel (IntArray.full b_pre m_pre l2).
	- split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_array_concat_entail_wit_3 : array_concat_entail_wit_3.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply (IntArray.full_length a_pre).
	Intros_p Hlen.
	assert (Hi : i = n_pre) by lia.
	subst i.
	assert (Hlen1 : Zlength l1 = n_pre) by (pose proof (Zlength_correct l1); lia).
	rewrite (sublist_self l1 n_pre) by exact (eq_sym Hlen1).
	change (sublist 0 0 l2) with (@nil Z).
	rewrite app_nil_r.
	replace (n_pre + 0) with n_pre by lia.
	split_pure_spatial.
	- cancel (IntArray.seg ret_pre 0 n_pre l1).
	  cancel (IntArray.full a_pre n_pre l1).
	  cancel (IntArray.undef_seg ret_pre n_pre (n_pre + m_pre)).
	  cancel (IntArray.full b_pre m_pre l2).
	- split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_array_concat_entail_wit_4 : array_concat_entail_wit_4.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply (IntArray.full_Zlength b_pre).
	Intros_p Hlen.
	replace (l1 ++ sublist 0 (i + 1) l2) with ((l1 ++ sublist 0 i l2) ++ Znth i l2 0 :: nil).
	2: {
		rewrite (sublist_split 0 (i + 1) i l2) by lia.
		rewrite (sublist_single 0 i l2) by lia.
		rewrite app_assoc.
		reflexivity.
	}
	replace (n_pre + (i + 1)) with (n_pre + i + 1) by lia.
	split_pure_spatial.
	- cancel (IntArray.seg ret_pre 0 (n_pre + i + 1) ((l1 ++ sublist 0 i l2) ++ Znth i l2 0 :: nil)).
	  cancel (IntArray.undef_seg ret_pre (n_pre + i + 1) (n_pre + m_pre)).
	  cancel (IntArray.full a_pre n_pre l1).
	  cancel (IntArray.full b_pre m_pre l2).
	- split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_array_concat_return_wit_1 : array_concat_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply (IntArray.full_length a_pre).
	Intros_p Hlen1.
	prop_apply (IntArray.full_length b_pre).
	Intros_p Hlen2.
	assert (Hi : i = m_pre) by lia.
	subst i.
	assert (Hlen2Z : Zlength l2 = m_pre) by (pose proof (Zlength_correct l2); lia).
	rewrite (sublist_self l2 m_pre) by exact (eq_sym Hlen2Z).
	rewrite IntArray.undef_seg_empty.
	sep_apply (IntArray.seg_to_full ret_pre 0 (n_pre + m_pre) (l1 ++ l2)).
	replace (ret_pre + 0 * sizeof ( INT )) with ret_pre by lia.
	replace (n_pre + m_pre - 0) with (n_pre + m_pre) by lia.
	cancel (IntArray.full a_pre n_pre l1).
	cancel (IntArray.full b_pre m_pre l2).
	cancel (IntArray.full ret_pre (n_pre + m_pre) (l1 ++ l2)).
Qed.

Lemma proof_of_array_swap_entail_wit_1 : array_swap_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply (IntArray.full_length a_pre n_pre l1).
	Intros_p Hlen1raw.
	prop_apply (IntArray.full_length b_pre n_pre l2).
	Intros_p Hlen2raw.
	assert (Hlen1 : Zlength l1 = n_pre) by (pose proof (Zlength_correct l1); lia).
	assert (Hlen2 : Zlength l2 = n_pre) by (pose proof (Zlength_correct l2); lia).
	change (sublist 0 0 l2) with (@nil Z).
	change (sublist 0 0 l1) with (@nil Z).
	rewrite (sublist_self l1 n_pre) by exact (eq_sym Hlen1).
	rewrite (sublist_self l2 n_pre) by exact (eq_sym Hlen2).
	simpl.
	split_pure_spatial.
	- cancel (IntArray.full a_pre n_pre l1).
	  cancel (IntArray.full b_pre n_pre l2).
	- split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_array_swap_entail_wit_2 : array_swap_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply (IntArray.full_length a_pre n_pre
		(replace_Znth i (Znth i (sublist 0 i l1 ++ sublist i n_pre l2) 0)
			(sublist 0 i l2 ++ sublist i n_pre l1))).
	Intros_p HlenA_raw.
	prop_apply (IntArray.full_length b_pre n_pre
		(replace_Znth i (Znth i (sublist 0 i l2 ++ sublist i n_pre l1) 0)
			(sublist 0 i l1 ++ sublist i n_pre l2))).
	Intros_p HlenB_raw.
	assert (HbaseA : Zlength (sublist 0 i l2 ++ sublist i n_pre l1) = n_pre).
	{
		pose proof (Zlength_correct
			(replace_Znth i (Znth i (sublist 0 i l1 ++ sublist i n_pre l2) 0)
				(sublist 0 i l2 ++ sublist i n_pre l1))) as Hz.
		rewrite replace_Znth_length_local in Hz.
		lia.
	}
	assert (HbaseB : Zlength (sublist 0 i l1 ++ sublist i n_pre l2) = n_pre).
	{
		pose proof (Zlength_correct
			(replace_Znth i (Znth i (sublist 0 i l2 ++ sublist i n_pre l1) 0)
				(sublist 0 i l1 ++ sublist i n_pre l2))) as Hz.
		rewrite replace_Znth_length_local in Hz.
		lia.
	}
	pose proof (Zlength_sublist_le_local 0 i l1 ltac:(lia)) as Hpre1_le0.
	pose proof (Zlength_sublist_le_local 0 i l2 ltac:(lia)) as Hpre2_le0.
	pose proof (Zlength_sublist_le_local i n_pre l1 ltac:(lia)) as Hsuf1_le.
	pose proof (Zlength_sublist_le_local i n_pre l2 ltac:(lia)) as Hsuf2_le.
	assert (Hpre1_le : Zlength (sublist 0 i l1) <= i) by lia.
	assert (Hpre2_le : Zlength (sublist 0 i l2) <= i) by lia.
	assert (Hsuf1_eq : Zlength (sublist i n_pre l1) = n_pre - i).
	{
		rewrite Zlength_app in HbaseA.
		lia.
	}
	assert (Hsuf2_eq : Zlength (sublist i n_pre l2) = n_pre - i).
	{
		rewrite Zlength_app in HbaseB.
		lia.
	}
	assert (Hpre1_eq : Zlength (sublist 0 i l1) = i).
	{
		rewrite Zlength_app in HbaseB.
		lia.
	}
	assert (Hpre2_eq : Zlength (sublist 0 i l2) = i).
	{
		rewrite Zlength_app in HbaseA.
		lia.
	}
	assert (Hlen1z : n_pre <= Zlength l1) by (eapply sublist_full_length_inv_local; eauto; lia).
	assert (Hlen2z : n_pre <= Zlength l2) by (eapply sublist_full_length_inv_local; eauto; lia).
	assert (Hlen1 : n_pre <= Z.of_nat (length l1)) by (rewrite <- Zlength_correct; exact Hlen1z).
	assert (Hlen2 : n_pre <= Z.of_nat (length l2)) by (rewrite <- Zlength_correct; exact Hlen2z).
	assert (Ha :
		replace_Znth i (Znth i (sublist 0 i l1 ++ sublist i n_pre l2) 0)
			(sublist 0 i l2 ++ sublist i n_pre l1) =
		(sublist 0 (i + 1) l2 ++ sublist (i + 1) n_pre l1)).
	{
		rewrite (sublist_split i n_pre (i + 1) l1).
		2: { lia. }
		2: { lia. }
		rewrite (sublist_single 0 i l1) by lia.
		assert (Hz : Znth i (sublist 0 i l1 ++ sublist i n_pre l2) 0 = Znth i l2 0).
		{
			assert (Hi_pre1 : i >= Zlength (sublist 0 i l1)) by lia.
			rewrite app_Znth2 by exact Hi_pre1.
			replace (i - Zlength (sublist 0 i l1)) with 0 by lia.
			rewrite Znth_sublist_lt by lia.
			f_equal; lia.
		}
		rewrite Hz.
		replace (sublist 0 (i + 1) l2 ++ sublist (i + 1) n_pre l1)
			with (sublist 0 i l2 ++ Znth i l2 0 :: sublist (i + 1) n_pre l1).
		2: {
			rewrite (sublist_split 0 (i + 1) i l2).
			2: { lia. }
			2: { lia. }
			rewrite (sublist_single 0 i l2) by lia.
			rewrite <- (app_assoc (sublist 0 i l2) (Znth i l2 0 :: nil) (sublist (i + 1) n_pre l1)).
			simpl.
			reflexivity.
		}
		simpl.
		replace i with (Zlength (sublist 0 i l2)) at 1 by exact Hpre2_eq.
		apply replace_Znth_boundary_local.
	}
	assert (Hb :
		replace_Znth i (Znth i (sublist 0 i l2 ++ sublist i n_pre l1) 0)
			(sublist 0 i l1 ++ sublist i n_pre l2) =
		(sublist 0 (i + 1) l1 ++ sublist (i + 1) n_pre l2)).
	{
		rewrite (sublist_split i n_pre (i + 1) l2).
		2: { lia. }
		2: { lia. }
		rewrite (sublist_single 0 i l2) by lia.
		assert (Hz : Znth i (sublist 0 i l2 ++ sublist i n_pre l1) 0 = Znth i l1 0).
		{
			assert (Hi_pre2 : i >= Zlength (sublist 0 i l2)) by lia.
			rewrite app_Znth2 by exact Hi_pre2.
			replace (i - Zlength (sublist 0 i l2)) with 0 by lia.
			rewrite Znth_sublist_lt by lia.
			f_equal; lia.
		}
		rewrite Hz.
		replace (sublist 0 (i + 1) l1 ++ sublist (i + 1) n_pre l2)
			with (sublist 0 i l1 ++ Znth i l1 0 :: sublist (i + 1) n_pre l2).
		2: {
			rewrite (sublist_split 0 (i + 1) i l1).
			2: { lia. }
			2: { lia. }
			rewrite (sublist_single 0 i l1) by lia.
			rewrite <- (app_assoc (sublist 0 i l1) (Znth i l1 0 :: nil) (sublist (i + 1) n_pre l2)).
			simpl.
			reflexivity.
		}
		simpl.
		replace i with (Zlength (sublist 0 i l1)) at 1 by exact Hpre1_eq.
		apply replace_Znth_boundary_local.
	}
	rewrite Ha.
	rewrite Hb.
	split_pure_spatial.
	- cancel (IntArray.full a_pre n_pre (sublist 0 (i + 1) l2 ++ sublist (i + 1) n_pre l1)).
	  cancel (IntArray.full b_pre n_pre (sublist 0 (i + 1) l1 ++ sublist (i + 1) n_pre l2)).
	- split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_array_swap_return_wit_1 : array_swap_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	assert (Hi : i = n_pre) by lia.
	subst i.
	rewrite (sublist_self l2 n_pre) by lia.
	rewrite (sublist_self l1 n_pre) by lia.
	rewrite (Zsublist_nil l1 n_pre n_pre) by lia.
	rewrite (Zsublist_nil l2 n_pre n_pre) by lia.
	simpl.
	repeat rewrite app_nil_r.
	cancel (IntArray.full a_pre n_pre l2).
	cancel (IntArray.full b_pre n_pre l1).
Qed.

Lemma proof_of_array_vector_sum_entail_wit_1 : array_vector_sum_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists (@nil Z).
	sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg ret_pre n_pre).
	rewrite (UIntArray.seg_empty ret_pre 0 0).
	split_pure_spatial.
	- cancel (UIntArray.full a_pre n_pre l1).
	  cancel (UIntArray.full b_pre n_pre l2).
	  cancel (UIntArray.undef_seg ret_pre 0 n_pre).
	- split_pures.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; reflexivity.
	  + dump_pre_spatial; exact PreH3.
	  + dump_pre_spatial; exact PreH4.
	  + dump_pre_spatial. intros k_3 Hk3. lia.
	  + dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_array_vector_sum_entail_wit_2_split_goal_1 :
  array_vector_sum_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_array_vector_sum_entail_wit_2 : array_vector_sum_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_array_vector_sum_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_array_vector_sum_return_wit_1 : array_vector_sum_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists l3_2.
	assert (Hi : i_2 = n_pre) by lia.
	rewrite Hi in *.
	rewrite UIntArray.undef_seg_empty.
	sep_apply (UIntArray.seg_to_full ret_pre 0 n_pre l3_2).
	replace (ret_pre + 0 * sizeof ( UINT )) with ret_pre by lia.
	replace (n_pre - 0) with n_pre by lia.
	split_pure_spatial.
	- cancel (UIntArray.full a_pre n_pre l1).
	  cancel (UIntArray.full b_pre n_pre l2).
	  cancel (UIntArray.full ret_pre n_pre l3_2).
	- split_pures; dump_pre_spatial.
	  + exact PreH6.
	  + exact PreH9.
Qed.

Lemma proof_of_pointwise_mul_entail_wit_1 : pointwise_mul_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists (@nil Z).
	sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg c_pre n_pre).
	rewrite (UIntArray.seg_empty c_pre 0 0).
	split_pure_spatial.
	- cancel (UIntArray.full a_pre n_pre l1).
	  cancel (UIntArray.full b_pre n_pre l2).
	  cancel (UIntArray.undef_seg c_pre 0 n_pre).
	- split_pures.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; reflexivity.
	  + dump_pre_spatial; exact PreH3.
	  + dump_pre_spatial; exact PreH4.
	  + dump_pre_spatial. intros k_3 Hk3.
	    lia.
	  + dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_pointwise_mul_entail_wit_2_split_goal_1 :
  pointwise_mul_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_pointwise_mul_entail_wit_2 : pointwise_mul_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pointwise_mul_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_pointwise_mul_return_wit_1 : pointwise_mul_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists l3_2.
	assert (Hi : i_2 = n_pre) by lia.
	rewrite Hi in *.
	rewrite UIntArray.undef_seg_empty.
	sep_apply (UIntArray.seg_to_full c_pre 0 n_pre l3_2).
	replace (c_pre + 0 * sizeof ( UINT )) with c_pre by lia.
	replace (n_pre - 0) with n_pre by lia.
	split_pure_spatial.
	- cancel (UIntArray.full a_pre n_pre l1).
	  cancel (UIntArray.full b_pre n_pre l2).
	  cancel (UIntArray.full c_pre n_pre l3_2).
	- split_pures; dump_pre_spatial.
	  + exact PreH6.
	  + exact PreH9.
Qed.

Lemma proof_of_array_max_entail_wit_1_split_goal_1 : array_max_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_array_max_entail_wit_1 : array_max_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_array_max_entail_wit_2_1 : array_max_entail_wit_2_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	split_pure_spatial.
	- cancel (IntArray.full a_pre n_pre l).
	- split_pures.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; exact PreH5.
	  + dump_pre_spatial; exact PreH6.
	  + dump_pre_spatial; exact PreH7.
	  + dump_pre_spatial.
	    intros Hi1.
	    lia.
	  + dump_pre_spatial.
	    intros Hi1.
	    exists i.
	    split; [split; [lia | reflexivity]|
	      intros k3 Hk3;
	      destruct (Z.eq_dec k3 i) as [Hki | Hki];
	      [subst k3; lia |
	       assert (k3 < i) by lia;
	       destruct (Z.eq_dec i 0) as [Hi0 | Hi0];
	       [subst i; lia |
	        assert (Hi_pos : 0 < i) by lia;
	        specialize (PreH9 Hi_pos);
	        destruct PreH9 as [k0 [[Hk0 Hv] Hmax]];
	        specialize (Hmax k3);
	        lia]]].
Qed.


Lemma proof_of_array_max_entail_wit_2_2 : array_max_entail_wit_2_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	split_pure_spatial.
	- cancel (IntArray.full a_pre n_pre l).
	- split_pures.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; exact PreH5.
	  + dump_pre_spatial; exact PreH6.
	  + dump_pre_spatial; exact PreH7.
	  + dump_pre_spatial.
	    intros Hi1.
	    lia.
	  + dump_pre_spatial.
	    intros _.
	    destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
	    * subst i.
	      exfalso.
	      specialize (PreH7 0).
	      assert (0 <= Znth 0 l 0) by (apply PreH7; lia).
	      pose proof (PreH8 eq_refl).
	      lia.
	    * assert (Hi_pos : 0 < i) by lia.
	      specialize (PreH9 Hi_pos).
	      destruct PreH9 as [k0 [[Hk0 Hv] Hmax]].
	      exists k0.
	      split.
	      { split; [lia | exact Hv]. }
	      intros k3 Hk3.
	      destruct (Z.eq_dec k3 i) as [Hki | Hki].
	      { subst k3. exact PreH1. }
	      apply Hmax.
	      lia.
Qed.
Lemma proof_of_array_max_return_wit_1 : array_max_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	split_pure_spatial.
	- cancel (IntArray.full a_pre n_pre l).
	- split_pures.
	  + dump_pre_spatial.
	    intros Hn0.
	    apply PreH7.
	    lia.
	  + dump_pre_spatial.
	    intros Hnpos.
	    assert (Hi : i_3 = n_pre) by lia.
	    subst i_3.
	    specialize (PreH8 Hnpos).
	    exact PreH8.
Qed.

Lemma proof_of_memset_entail_wit_1 : memset_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists (@nil Z).
	sep_apply_l_atomic (IntArray.undef_full_to_undef_seg a_pre n_pre).
	rewrite (IntArray.seg_empty a_pre 0 0).
	split_pure_spatial.
	- cancel (IntArray.undef_seg a_pre 0 n_pre).
	- split_pures.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; compute; reflexivity.
	  + dump_pre_spatial. intros k Hk.
	    lia.
	  + dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_memset_entail_wit_2 : memset_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists (l_2 ++ value_pre :: nil).
	split_pure_spatial.
	- cancel (IntArray.seg a_pre 0 (i + 1) (l_2 ++ value_pre :: nil)).
	  cancel (IntArray.undef_seg a_pre (i + 1) n_pre).
	- split_pures.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; exact PreH4.
	  + dump_pre_spatial; exact PreH5.
	  + dump_pre_spatial.
	    rewrite Zlength_app, Zlength_cons, Zlength_nil.
	    rewrite PreH6.
	    lia.
	  + dump_pre_spatial. intros k Hk.
	    destruct (Z_lt_ge_dec k i).
	    * rewrite app_Znth1 by lia.
	      apply PreH7.
	      lia.
	    * assert (k = i) by lia.
	      subst k.
	      rewrite app_Znth2 by lia.
	      rewrite PreH6.
	      rewrite Z.sub_diag.
	      simpl.
	      reflexivity.
Qed.

Lemma proof_of_memset_return_wit_1 : memset_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists l_2.
	assert (Hi : i_2 = n_pre) by lia.
	subst i_2.
	rewrite Hi.
	rewrite IntArray.undef_seg_empty.
	sep_apply (IntArray.seg_to_full a_pre 0 n_pre l_2).
	replace (a_pre + 0 * sizeof ( INT )) with a_pre by lia.
	replace (n_pre - 0) with n_pre by lia.
	split_pure_spatial.
	- cancel (IntArray.full a_pre n_pre l_2).
	- split_pures; dump_pre_spatial.
	  + reflexivity.
	  + intros i Hi'.
	    apply PreH7.
	    lia.
Qed.

Lemma proof_of_array_to_list_entail_wit_1 : array_to_list_entail_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	Exists (Znth 0 l 0).
	rewrite PreH2.
	change (sublist 0 (1 - 1) l) with (@nil Z).
	simpl.
	split_pure_spatial.
	- cancel (&( retval # "list" ->ₛ"data") # Int |-> Znth 0 l 0).
	  cancel (&( retval # "list" ->ₛ"next") # Ptr |-> 0).
	  cancel (IntArray.full a_pre n_pre l).
	- split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_array_to_list_entail_wit_2 : array_to_list_entail_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply IntArray.full_Zlength.
	Intros_p Hlen.
	Exists (Znth i l 0).
	split_pure_spatial.
	- rewrite PreH2.
	  cancel (&( retval # "list" ->ₛ"data") # Int |-> Znth i l 0).
	  cancel (&( retval # "list" ->ₛ"next") # Ptr |-> 0).
	  sep_apply (sllseg_len1 tail v_2 retval).
	  2: { easy. }
	  sep_apply (sllseg_sllseg head tail retval (sublist 0 (i - 1) l) (v_2 :: nil)).
	  assert (Hsubl : sublist 0 (i + 1 - 1) l = sublist 0 (i - 1) l ++ v_2 :: nil).
	  {
		subst v_2.
		assert (Hsingle : sublist (i - 1) i l = (Znth (i - 1) l 0 :: nil)%list).
		{
		  replace i with ((i - 1) + 1) by lia.
		  replace (((i - 1) + 1) - 1) with (i - 1) by lia.
		  apply sublist_single.
		  lia.
		}
		replace (i + 1 - 1) with i by lia.
		rewrite (sublist_split 0 i (i - 1) l) by lia.
		rewrite Hsingle.
		reflexivity.
	  }
	  rewrite <- Hsubl.
	  cancel (sllseg head retval (sublist 0 (i + 1 - 1) l)).
	  cancel (IntArray.full a_pre n_pre l).
	- split_pures.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; lia.
	  + dump_pre_spatial; exact PreH6.
	  + dump_pre_spatial; exact PreH1.
	  + dump_pre_spatial; exact PreH8.
	  + dump_pre_spatial; exact PreH9.
	  + dump_pre_spatial; replace (i + 1 - 1) with i by lia.
	    reflexivity.
Qed.

Lemma proof_of_array_to_list_return_wit_1 : array_to_list_return_wit_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply IntArray.full_Zlength.
	Intros_p Hlen.
	assert (Hi : i = n_pre) by lia.
	subst i.
	sep_apply (sllseg_len1 tail v 0).
	2: { easy. }
	sep_apply sllseg_0_sll.
	sep_apply (sllseg_sll head tail (sublist 0 (n_pre - 1) l) (v :: nil)).
	replace (sublist 0 (n_pre - 1) l ++ v :: nil) with l.
	2: {
	  subst v.
	  rewrite <- (sublist_self l n_pre) at 1 by (pose proof (Zlength_correct l); lia).
	  rewrite (sublist_split 0 n_pre (n_pre - 1) l) by lia.
	  replace n_pre with ((n_pre - 1) + 1) in * by lia.
	  replace (n_pre - 1 + 1 - 1) with (n_pre - 1) by lia.
	  rewrite (sublist_single 0 (n_pre - 1) l) by (pose proof (Zlength_correct l); lia).
	  reflexivity.
	}
	cancel (sll head l).
	cancel (IntArray.full a_pre n_pre l).
Qed.

Lemma proof_of_array_to_list_return_wit_2 : array_to_list_return_wit_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	prop_apply IntArray.full_length.
	Intros_p Hlen.
	assert (Hlen0 : Zlength l = 0) by (pose proof (Zlength_correct l); lia).
	apply Zlength_nil_inv in Hlen0.
	subst l.
	simpl.
	split_pure_spatial.
	- cancel (IntArray.full a_pre n_pre nil).
	- dump_pre_spatial.
	  unfold NULL.
	  lia.
Qed.
