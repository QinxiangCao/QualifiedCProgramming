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

Lemma proof_of_mpz_neg_safety_wit_1_eq : mpz_neg_safety_wit_1_eq.
Proof.
  unfold mpz_neg_safety_wit_1_eq.
  left.
  intros.
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD ptr (Zabs z_eq) (Zabs size)).
  Intros.
  entailer!.
  match goal with
  | H : 0 <= Zabs size <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H;
      intro Heq; subst size; cbn in H; lia
  end.
Qed.

Lemma proof_of_mpz_neg_safety_wit_2_neq : mpz_neg_safety_wit_2_neq.
Proof.
  unfold mpz_neg_safety_wit_2_neq.
  left.
  intros.
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD rptr (Zabs z_neq) (Zabs rsize)).
  Intros.
  entailer!.
  match goal with
  | H : 0 <= Zabs rsize <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H;
      intro Heq; subst rsize; cbn in H; lia
  end.
Qed.

Lemma proof_of_mpz_neg_entail_wit_1_eq : mpz_neg_entail_wit_1_eq.
Proof.
  pre_process.
  subst rop_pre.
  unfold store_Z.
  Intros ptr size cap.
  Exists ptr cap size.
  entailer!.
Qed.

Lemma proof_of_mpz_neg_return_wit_1_eq : mpz_neg_return_wit_1_eq.
Proof.
  pre_process.
  subst rop_pre.
  prop_apply_p (mpd_store_Z_to_is_compact_Z ptr (Zabs z_eq) (Zabs size)).
  Intros.
  unfold store_Z.
  Exists ptr (- size) cap.
  rewrite !Z.abs_opp.
  entailer!.
  apply same_sign_opp_compact_abs; assumption.
Qed.

Lemma proof_of_mpz_neg_return_wit_2_neq : mpz_neg_return_wit_2_neq.
Proof.
  pre_process.
  prop_apply_p (mpd_store_Z_to_is_compact_Z rptr (Zabs z_neq) (Zabs rsize)).
  Intros.
  unfold store_Z.
  Exists rptr (- rsize) rcap.
  Exists optr osize ocap.
  rewrite !Z.abs_opp.
  entailer!.
  apply same_sign_opp_compact_abs; assumption.
Qed.
