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
From SimpleC.EE.QCP_demos_human Require Import sum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.

Local Open Scope sac.

Lemma proof_of_arr_sum_entail_wit_1 : arr_sum_entail_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_arr_sum_entail_wit_2 : arr_sum_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite PreH4.
      rewrite (sublist_split 0 (i_2 + 1) i_2 l) by lia.
      rewrite sum_app.
      rewrite (sublist_single 0 i_2 l) by lia.
      simpl.
      assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH7.
      destruct (Z.eq_dec i_2 0) as [Hi0 | Hi0].
      * subst i_2. simpl in *. subst ret.
        assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
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
        rewrite Z.add_0_r.
        reflexivity.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
Qed.

Lemma proof_of_arr_sum_return_wit_1 : arr_sum_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by (rewrite Zlength_correct; exact Hlen).
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - dump_pre_spatial.
    rewrite PreH4.
    assert (Hi : i_2 = n_pre) by lia.
    subst i_2.
    rewrite sublist_self by (symmetry; exact HlenZ).
    reflexivity.
Qed.

Lemma proof_of_arr_sum_safety_wit_3 : arr_sum_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by (rewrite Zlength_correct; exact Hlen).
  assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH7.
  destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
  - subst i. simpl in *. subst ret.
    assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
  - assert (0 <= ret < i * 100).
    {
      subst ret.
      assert (Hsublen0 : length (sublist 0 i l) = Z.to_nat (i - 0))
        by (apply sublist_length; lia).
      assert (Hsublen : i = Z.of_nat (length (sublist 0 i l))).
      { rewrite Hsublen0. lia. }
      rewrite Hsublen at 3.
      apply sum_bound_lt.
      - intro Hnil. rewrite Hnil in Hsublen. simpl in *; lia.
      - intros idx Hidx.
        rewrite <- Hsublen in Hidx.
        rewrite Znth_sublist_lt by lia.
        apply Hrange. lia.
    }
    assert (Hcur : 0 <= Znth i l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_arr_sum_do_while_entail_wit_2 : arr_sum_do_while_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by (rewrite Zlength_correct; exact Hlen).
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite (sublist_single 0 0 l) by (rewrite HlenZ; lia).
      unfold sum.
      simpl.
      lia.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
Qed.

Lemma proof_of_arr_sum_do_while_entail_wit_1 : arr_sum_do_while_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  assert (Hlt : i_2 < n_pre) by lia.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite PreH4.
      rewrite (sublist_split 0 (i_2 + 1) i_2 l) by lia.
      rewrite sum_app.
      rewrite (sublist_single 0 i_2 l) by lia.
      simpl.
      assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH7.
      destruct (Z.eq_dec i_2 0) as [Hi0 | Hi0].
      * subst i_2. simpl in *. subst ret.
        assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
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
        rewrite Z.add_0_r.
        reflexivity.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
Qed. 

Lemma proof_of_arr_sum_do_while_return_wit_1 : arr_sum_do_while_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by (rewrite Zlength_correct; exact Hlen).
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - dump_pre_spatial.
    rewrite PreH4.
    assert (Hi : i_2 = n_pre) by lia.
    subst i_2.
    rewrite sublist_self by (symmetry; exact HlenZ).
    reflexivity.
Qed. 

Lemma proof_of_arr_sum_do_while_safety_wit_6 : arr_sum_do_while_safety_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by (rewrite Zlength_correct; exact Hlen).
  assert (Hlt : i < n_pre) by lia.
  assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH7.
  destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
  - subst i. simpl in *. subst ret.
    assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
  - assert (0 <= ret < i * 100).
    {
      subst ret.
      assert (Hsublen0 : length (sublist 0 i l) = Z.to_nat (i - 0))
        by (apply sublist_length; lia).
      assert (Hsublen : i = Z.of_nat (length (sublist 0 i l))).
      { rewrite Hsublen0. lia. }
      rewrite Hsublen at 3.
      apply sum_bound_lt.
      - intro Hnil. rewrite Hnil in Hsublen. simpl in *; lia.
      - intros idx Hidx.
        rewrite <- Hsublen in Hidx.
        rewrite Znth_sublist_lt by lia.
        apply Hrange. lia.
    }
    assert (Hcur : 0 <= Znth i l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_arr_sum_for_entail_wit_1 : arr_sum_for_entail_wit_1.
Proof.
   LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_arr_sum_for_entail_wit_2 : arr_sum_for_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite PreH4.
      rewrite (sublist_split 0 (i_2 + 1) i_2 l) by lia.
      rewrite sum_app.
      rewrite (sublist_single 0 i_2 l) by lia.
      simpl.
      assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH7.
      destruct (Z.eq_dec i_2 0) as [Hi0 | Hi0].
      * subst i_2. simpl in *. subst ret.
        assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
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
        rewrite Z.add_0_r.
        reflexivity.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
Qed. 

Lemma proof_of_arr_sum_for_return_wit_1 : arr_sum_for_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by (rewrite Zlength_correct; exact Hlen).
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - dump_pre_spatial.
    rewrite PreH4.
    assert (Hi : i_2 = n_pre) by lia.
    subst i_2.
    rewrite sublist_self by (symmetry; exact HlenZ).
    reflexivity.
Qed.

Lemma proof_of_arr_sum_for_safety_wit_3 : arr_sum_for_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by (rewrite Zlength_correct; exact Hlen).
  assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH7.
  destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
  - subst i. simpl in *. subst ret.
    assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
  - assert (0 <= ret < i * 100).
    {
      subst ret.
      assert (Hsublen0 : length (sublist 0 i l) = Z.to_nat (i - 0))
        by (apply sublist_length; lia).
      assert (Hsublen : i = Z.of_nat (length (sublist 0 i l))).
      { rewrite Hsublen0. lia. }
      rewrite Hsublen at 3.
      apply sum_bound_lt.
      - intro Hnil. rewrite Hnil in Hsublen. simpl in *; lia.
      - intros idx Hidx.
        rewrite <- Hsublen in Hidx.
        rewrite Znth_sublist_lt by lia.
        apply Hrange. lia.
    }
    assert (Hcur : 0 <= Znth i l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_arr_sum_which_implies_entail_wit_1 : arr_sum_which_implies_entail_wit_1.
Proof. 
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_arr_sum_which_implies_entail_wit_2 : arr_sum_which_implies_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite PreH6.
      rewrite (sublist_split 0 (i_2 + 1) i_2 l) by lia.
      rewrite sum_app.
      rewrite (sublist_single 0 i_2 l) by lia.
      simpl.
      assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH9.
      destruct (Z.eq_dec i_2 0) as [Hi0 | Hi0].
      * subst i_2. simpl in *. subst ret.
        assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
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
        rewrite Z.add_0_r.
        reflexivity.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. exact PreH9.
Qed. 

Lemma proof_of_arr_sum_which_implies_return_wit_1 : arr_sum_which_implies_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by (rewrite Zlength_correct; exact Hlen).
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - dump_pre_spatial.
    rewrite PreH4.
    assert (Hi : i_2 = n_pre) by lia.
    subst i_2.
    rewrite sublist_self by (symmetry; exact HlenZ).
    reflexivity.
Qed. 

Lemma proof_of_arr_sum_which_implies_which_implies_wit_2 : arr_sum_which_implies_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  split_pure_spatial.
  - cancel (IntArray.full a n_pre l).
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_arr_sum_which_implies_safety_wit_3 : arr_sum_which_implies_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by (rewrite Zlength_correct; exact Hlen).
  assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH7.
  destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
  - subst i. simpl in *. subst ret.
    assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
  - assert (0 <= ret < i * 100).
    {
      subst ret.
      assert (Hsublen0 : length (sublist 0 i l) = Z.to_nat (i - 0))
        by (apply sublist_length; lia).
      assert (Hsublen : i = Z.of_nat (length (sublist 0 i l))).
      { rewrite Hsublen0. lia. }
      rewrite Hsublen at 3.
      apply sum_bound_lt.
      - intro Hnil. rewrite Hnil in Hsublen. simpl in *; lia.
      - intros idx Hidx.
        rewrite <- Hsublen in Hidx.
        rewrite Znth_sublist_lt by lia.
        apply Hrange. lia.
    }
    assert (Hcur : 0 <= Znth i l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_arr_sum_update_entail_wit_1 : arr_sum_update_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by exact Hlen.
  replace (zeros 0 ++ sublist 0 n_pre l) with l.
  2: {
    unfold zeros.
    simpl.
    rewrite sublist_self by (symmetry; exact HlenZ).
    reflexivity.
  }
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact (eq_sym HlenZ).
    + dump_pre_spatial. rewrite Zsublist_nil by lia. reflexivity.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
Qed.

Lemma proof_of_arr_sum_update_entail_wit_2 : arr_sum_update_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hbase_zi :
    Znth i_2 (zeros i_2 ++ sublist i_2 n_pre l) 0 = Znth i_2 l 0).
  {
    rewrite app_Znth2 by (rewrite Zlength_correct; unfold zeros; rewrite repeat_length; lia).
    rewrite Zlength_correct; unfold zeros; rewrite repeat_length.
    replace (i_2 - Z.of_nat (Z.to_nat i_2)) with 0 by lia.
    rewrite Znth_sublist by lia.
    replace (0 + i_2) with i_2 by lia.
    apply Znth_indep. lia.
  }
  assert (Hinner :
    replace_Znth i_2 (Znth i_2 l 0) (zeros i_2 ++ sublist i_2 n_pre l) =
    zeros i_2 ++ sublist i_2 n_pre l).
  {
    rewrite <- Hbase_zi.
    rewrite replace_Znth_Znth by
      (rewrite Zlength_app, Zlength_correct, repeat_length, Zlength_sublist; lia).
    reflexivity.
  }
  assert (Hrewrite :
    replace_Znth i_2 0
      (replace_Znth i_2 (Znth i_2 l 0) (zeros i_2 ++ sublist i_2 n_pre l)) =
    zeros (i_2 + 1) ++ sublist (i_2 + 1) n_pre l).
  {
    rewrite Hinner.
    assert (Hzlen : Zlength (zeros i_2) = i_2).
    { rewrite Zlength_correct; unfold zeros; rewrite repeat_length; lia. }
    rewrite replace_Znth_app_r; try lia.
    rewrite replace_Znth_nothing; try lia.
    replace (i_2 - Zlength (zeros i_2)) with 0 by lia.
    replace (zeros (i_2 + 1)) with (zeros i_2 ++ (0 :: nil)).
    2: {
      unfold zeros.
      replace (Z.to_nat (i_2 + 1)) with (Z.to_nat i_2 + 1)%nat by lia.
      rewrite repeat_app. simpl. reflexivity.
    }
    rewrite sublist_split with (mid := (i_2 + 1)) ; try lia.
    rewrite sublist_single with (d := 0) ; try lia.
    simpl.
    unfold replace_Znth. simpl.
    rewrite <- app_assoc. simpl.
    reflexivity.
  }
  rewrite Hrewrite.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre (zeros (i_2 + 1) ++ sublist (i_2 + 1) n_pre l)).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial.
      assert (Hzi :
        Znth i_2
          (replace_Znth i_2 (Znth i_2 l 0) (zeros i_2 ++ sublist i_2 n_pre l)) 0 =
        Znth i_2 l 0).
      {
        rewrite Hinner.
        exact Hbase_zi.
      }
      rewrite Hzi.
      rewrite PreH5.
      rewrite (sublist_split 0 (i_2 + 1) i_2 l) by lia.
      rewrite sum_app.
      rewrite (sublist_single 0 i_2 l) by lia.
      simpl.
      assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH8.
      destruct (Z.eq_dec i_2 0) as [Hi0 | Hi0].
      * subst i_2. simpl in *. subst ret.
        assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
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
            apply Hrange. lia.
        }
        assert (Hcur : 0 <= Znth i_2 l 0 < 100) by (apply Hrange; lia).
        rewrite Z.add_0_r.
        reflexivity.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
Qed. 

Lemma proof_of_arr_sum_update_return_wit_1 : arr_sum_update_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i_2 = n_pre) by lia.
  subst i_2.
  replace (zeros n_pre ++ sublist n_pre n_pre l) with (zeros n_pre).
  2: { rewrite Zsublist_nil by lia. rewrite app_nil_r. reflexivity. }
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre (zeros n_pre)).
  - split_pures.
    + dump_pre_spatial.
      rewrite <- (sublist_self l n_pre) by exact PreH4.
      exact PreH5.
Qed.

Lemma proof_of_arr_sum_update_which_implies_wit_1 : arr_sum_update_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (IntArray.full_split_to_missing_i a_pre i) ; try lia.
  replace (Znth i (zeros i ++ sublist i n_pre l) 0) with (Znth i l 0).
  cancel.
  rewrite app_Znth2 ; rewrite Zlength_correct ; unfold zeros; rewrite repeat_length ; try lia.
  replace (i - Z.of_nat (Z.to_nat i)) with 0 by lia.
  rewrite Znth_sublist ; try lia.
  replace (0 + i) with i by lia.
  apply Znth_indep. lia.
Qed. 

Lemma proof_of_arr_sum_update_safety_wit_3 : arr_sum_update_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hzi :
    Znth i (replace_Znth i (Znth i l 0) (zeros i ++ sublist i n_pre l)) 0 =
    Znth i l 0).
  {
    assert (Hzlen : Zlength (zeros i) = i).
    { rewrite Zlength_correct; unfold zeros; rewrite repeat_length; lia. }
    rewrite Znth_replace_Znth_Same by
      (rewrite Zlength_app, Hzlen, Zlength_sublist; lia).
    reflexivity.
  }
  assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH8.
  destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
  - subst i. simpl in *. subst ret.
    assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. rewrite Hzi. lia.
    + dump_pre_spatial. rewrite Hzi. lia.
  - assert (0 <= ret < i * 100).
    {
      subst ret.
      assert (Hsublen0 : length (sublist 0 i l) = Z.to_nat (i - 0))
        by (apply sublist_length; lia).
      assert (Hsublen : i = Z.of_nat (length (sublist 0 i l))).
      { rewrite Hsublen0. lia. }
      rewrite Hsublen at 3.
      apply sum_bound_lt.
      - intro Hnil. rewrite Hnil in Hsublen. simpl in *; lia.
      - intros idx Hidx.
        rewrite <- Hsublen in Hidx.
        rewrite Znth_sublist_lt by lia.
        apply Hrange. lia.
    }
    assert (Hcur : 0 <= Znth i l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. rewrite Hzi. lia.
    + dump_pre_spatial. rewrite Hzi. lia.
Qed.

Lemma proof_of_arr_sum_pointer_entail_wit_1: arr_sum_pointer_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_arr_sum_pointer_entail_wit_2: arr_sum_pointer_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - split_pures.
    + dump_pre_spatial.
      intro Hi.
      apply PreH1.
      rewrite Hi.
      replace (a_pre + n_pre * sizeof ( INT ) - (a_pre + n_pre * sizeof ( INT ))) with 0 by lia.
      rewrite Z.quot_0_l.
      { reflexivity. }
      { rewrite sizeof_int; lia. }
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
Qed.

Lemma proof_of_arr_sum_pointer_entail_wit_3: arr_sum_pointer_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite PreH5.
      rewrite (sublist_split 0 (i_2 + 1) i_2 l) by lia.
      rewrite sum_app.
      rewrite (sublist_single 0 i_2 l) by lia.
      simpl.
      assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH8.
      destruct (Z.eq_dec i_2 0) as [Hi0 | Hi0].
      * subst i_2. simpl in *. subst ret.
        assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
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
        rewrite Z.add_0_r.
        reflexivity.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH8.
Qed.

Lemma proof_of_arr_sum_pointer_return_wit_1: arr_sum_pointer_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre l).
  - dump_pre_spatial.
    assert (Hi : i_2 = n_pre).
    {
      destruct (Z.eq_dec i_2 n_pre) as [Heq | Hneq].
      - exact Heq.
      - assert (i_2 < n_pre) by lia.
        exfalso.
        rewrite sizeof_int in PreH1.
        replace (a_pre + n_pre * 4 - (a_pre + i_2 * 4)) with ((n_pre - i_2) * 4) in PreH1 by lia.
        rewrite Z.quot_mul in PreH1 by lia.
        lia.
    }
    subst i_2 ret.
    unfold sublist.
    simpl.
    rewrite firstn_all2 by lia.
    reflexivity.
Qed.

Lemma proof_of_arr_sum_pointer_safety_wit_4: arr_sum_pointer_safety_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_length.
  Intros_p Hlen.
  assert (HlenZ : Zlength l = n_pre) by (rewrite Zlength_correct; exact Hlen).
  assert (Hrange : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 < 100) by exact PreH8.
  destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
  - subst i. simpl in *. subst ret.
    assert (Hcur : 0 <= Znth 0 l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
  - assert (0 <= ret < i * 100).
    {
      subst ret.
      assert (Hsublen0 : length (sublist 0 i l) = Z.to_nat (i - 0))
        by (apply sublist_length; lia).
      assert (Hsublen : i = Z.of_nat (length (sublist 0 i l))).
      { rewrite Hsublen0. lia. }
      rewrite Hsublen at 3.
      apply sum_bound_lt.
      - intro Hnil. rewrite Hnil in Hsublen. simpl in *; lia.
      - intros idx Hidx.
        rewrite <- Hsublen in Hidx.
        rewrite Znth_sublist_lt by lia.
        apply Hrange. lia.
    }
    assert (Hcur : 0 <= Znth i l 0 < 100) by (apply Hrange; lia).
    split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.
