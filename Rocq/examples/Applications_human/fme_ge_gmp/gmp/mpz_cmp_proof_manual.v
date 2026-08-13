Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_cmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_cmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_cmp_safety_wit_5 : mpz_cmp_safety_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_range UINT_MOD aptr (Zabs za_neq) (- asize)).
  Intros.
  match goal with
  | H : 0 <= - asize <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_cmp_entail_wit_2_split_goal_spatial :
  mpz_cmp_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (Zabs a_size) with a_size by lia.
  replace (Zabs b_size) with a_size by lia.
  cancel (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs za_neq) a_size).
  cancel (UIntArray.undef_seg aptr_2 a_size acap_2).
  cancel (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs zb_neq) a_size).
  cancel (UIntArray.undef_seg bptr_2 a_size bcap_2).
Qed.

Lemma proof_of_mpz_cmp_entail_wit_2 : mpz_cmp_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_cmp_entail_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpz_cmp_entail_wit_3_split_goal_spatial :
  mpz_cmp_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (Zabs a_size) with (- a_size) by lia.
  replace (Zabs b_size) with (- a_size) by lia.
  cancel (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs za_neq) (- a_size)).
  cancel (UIntArray.undef_seg aptr_2 (- a_size) acap_2).
  cancel (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs zb_neq) (- a_size)).
  cancel (UIntArray.undef_seg bptr_2 (- a_size) bcap_2).
Qed.

Lemma proof_of_mpz_cmp_entail_wit_3 : mpz_cmp_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_cmp_entail_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_mpz_cmp_return_wit_1 : mpz_cmp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (za_neq < zb_neq).
  {
    assert (za_neq < 0) by (unfold same_sign in PreH5; lia).
    assert (zb_neq < 0) by (unfold same_sign in PreH7; lia).
    rewrite Z.abs_neq in PreH1 by lia.
    rewrite Z.abs_neq in PreH1 by lia.
    lia.
  }
  unfold store_Z.
  Exists aptr asize acap bptr bsize bcap.
  replace (Zabs asize) with (- asize) by lia.
  replace (Zabs bsize) with (- asize) by lia.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_cmp_return_wit_2 : mpz_cmp_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (za_neq = zb_neq).
  {
    assert (za_neq < 0) by (unfold same_sign in PreH5; lia).
    assert (zb_neq < 0) by (unfold same_sign in PreH7; lia).
    rewrite Z.abs_neq in PreH1 by lia.
    rewrite Z.abs_neq in PreH1 by lia.
    lia.
  }
  unfold store_Z.
  Exists aptr asize acap bptr bsize bcap.
  replace (Zabs asize) with (- asize) by lia.
  replace (Zabs bsize) with (- asize) by lia.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_cmp_return_wit_3 : mpz_cmp_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (za_neq > zb_neq).
  {
    assert (za_neq < 0) by (unfold same_sign in PreH5; lia).
    assert (zb_neq < 0) by (unfold same_sign in PreH7; lia).
    rewrite Z.abs_neq in PreH1 by lia.
    rewrite Z.abs_neq in PreH1 by lia.
    lia.
  }
  unfold store_Z.
  Exists aptr asize acap bptr bsize bcap.
  replace (Zabs asize) with (- asize) by lia.
  replace (Zabs bsize) with (- asize) by lia.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_cmp_return_wit_4 : mpz_cmp_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (za_neq < zb_neq).
  {
    assert (0 <= za_neq) by (unfold same_sign in PreH5; lia).
    assert (0 <= zb_neq) by (unfold same_sign in PreH7; lia).
    rewrite Z.abs_eq in PreH1 by lia.
    rewrite Z.abs_eq in PreH1 by lia.
    lia.
  }
  unfold store_Z.
  Exists aptr asize acap bptr bsize bcap.
  replace (Zabs asize) with asize by lia.
  replace (Zabs bsize) with asize by lia.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_cmp_return_wit_5 : mpz_cmp_return_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (za_neq = zb_neq).
  {
    assert (0 <= za_neq) by (unfold same_sign in PreH5; lia).
    assert (0 <= zb_neq) by (unfold same_sign in PreH7; lia).
    rewrite Z.abs_eq in PreH1 by lia.
    rewrite Z.abs_eq in PreH1 by lia.
    lia.
  }
  unfold store_Z.
  Exists aptr asize acap bptr bsize bcap.
  replace (Zabs asize) with asize by lia.
  replace (Zabs bsize) with asize by lia.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_cmp_return_wit_6 : mpz_cmp_return_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (za_neq > zb_neq).
  {
    assert (0 <= za_neq) by (unfold same_sign in PreH5; lia).
    assert (0 <= zb_neq) by (unfold same_sign in PreH7; lia).
    rewrite Z.abs_eq in PreH1 by lia.
    rewrite Z.abs_eq in PreH1 by lia.
    lia.
  }
  unfold store_Z.
  Exists aptr asize acap bptr bsize bcap.
  replace (Zabs asize) with asize by lia.
  replace (Zabs bsize) with asize by lia.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_cmp_return_wit_7 : mpz_cmp_return_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_to_is_compact_Z aptr (Zabs za_neq) (Zabs a_size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z bptr (Zabs zb_neq) (Zabs b_size)).
  Intros.
  assert (za_neq < zb_neq).
  {
    eapply same_sign_compact_size_lt_value_lt; eauto.
  }
  unfold store_Z.
  Exists aptr a_size acap bptr b_size bcap.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_cmp_return_wit_8 : mpz_cmp_return_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_to_is_compact_Z aptr (Zabs za_neq) (Zabs a_size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z bptr (Zabs zb_neq) (Zabs b_size)).
  Intros.
  assert (zb_neq < za_neq).
  {
    eapply same_sign_compact_size_lt_value_lt; eauto; lia.
  }
  unfold store_Z.
  Exists aptr a_size acap bptr b_size bcap.
  LLM_pre_process ltac:(int_auto).
Qed.
