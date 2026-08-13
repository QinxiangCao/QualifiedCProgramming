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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_neg_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_neg_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_neg_safety_wit_1_eq_split_goal_1 :
  mpz_neg_safety_wit_1_eq_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  prop_apply (mpd_store_Z_compact_range UINT_MOD ptr (Zabs z_eq) (Zabs size)).
  Intros.
  dump_pre_spatial.
  match goal with
  | H : 0 <= Zabs size <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H;
      intro Heq; subst size; cbn in H; lia
  end.
Qed.

Lemma proof_of_mpz_neg_safety_wit_1_eq : mpz_neg_safety_wit_1_eq.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_neg_safety_wit_1_eq_split_goal_1.
Qed.

Lemma proof_of_mpz_neg_safety_wit_2_neq_split_goal_1 :
  mpz_neg_safety_wit_2_neq_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  prop_apply (mpd_store_Z_compact_range UINT_MOD rptr (Zabs z_neq) (Zabs rsize)).
  Intros.
  dump_pre_spatial.
  match goal with
  | H : 0 <= Zabs rsize <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H;
      intro Heq; subst rsize; cbn in H; lia
  end.
Qed.

Lemma proof_of_mpz_neg_safety_wit_2_neq : mpz_neg_safety_wit_2_neq.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_neg_safety_wit_2_neq_split_goal_1.
Qed.

Lemma proof_of_mpz_neg_entail_wit_1_eq : mpz_neg_entail_wit_1_eq.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst rop_pre.
  unfold store_Z.
  Intros ptr size cap.
  Exists ptr cap size.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial.
    all: try assumption; try reflexivity.
Qed.

Lemma proof_of_mpz_neg_return_wit_1_eq_split_goal_spatial :
  mpz_neg_return_wit_1_eq_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst rop_pre.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs z_eq) (Zabs size)).
  Intros.
  unfold store_Z.
  Exists ptr (- size) cap.
  rewrite !Z.abs_opp.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial.
    all: try assumption.
    apply same_sign_opp_compact_abs; assumption.
Qed.

Lemma proof_of_mpz_neg_return_wit_1_eq : mpz_neg_return_wit_1_eq.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_neg_return_wit_1_eq_split_goal_spatial.
Qed.

Lemma proof_of_mpz_neg_return_wit_2_neq_split_goal_1 :
  mpz_neg_return_wit_2_neq_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_neg_return_wit_2_neq_split_goal_2 :
  mpz_neg_return_wit_2_neq_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_to_is_compact_Z rptr (Zabs z_neq) (Zabs rsize)).
  Intros.
  dump_pre_spatial.
  apply same_sign_opp_compact_abs; assumption.
Qed.

Lemma proof_of_mpz_neg_return_wit_2_neq_split_goal_spatial :
  mpz_neg_return_wit_2_neq_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite !Z.abs_opp.
  cancel.
Qed.

Lemma proof_of_mpz_neg_return_wit_2_neq : mpz_neg_return_wit_2_neq.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpz_neg_return_wit_2_neq_split_goal_spatial.
  + Goal_apply proof_of_mpz_neg_return_wit_2_neq_split_goal_1.
  + Goal_apply proof_of_mpz_neg_return_wit_2_neq_split_goal_2.
Qed.
