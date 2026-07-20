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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_abs_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_abs_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_abs_entail_wit_1_eq : mpz_abs_entail_wit_1_eq.
Proof.
  pre_process.
  subst rop_pre.
  unfold store_Z.
  Intros ptr size cap.
  Exists ptr cap size.
  entailer!.
Qed.

Lemma proof_of_mpz_abs_return_wit_1_eq : mpz_abs_return_wit_1_eq.
Proof.
  pre_process.
  subst rop_pre.
  subst retval.
  unfold store_Z.
  Exists ptr (Zabs size) cap.
  replace (Zabs (Zabs z_eq)) with (Zabs z_eq)
    by (destruct (Z_lt_dec z_eq 0); rewrite ?Z.abs_neq, ?Z.abs_eq by lia; lia).
  replace (Zabs (Zabs size)) with (Zabs size)
    by (destruct (Z_lt_dec size 0); rewrite ?Z.abs_neq, ?Z.abs_eq by lia; lia).
  entailer!.
  unfold same_sign.
  lia.
Qed.

Lemma proof_of_mpz_abs_return_wit_2_neq : mpz_abs_return_wit_2_neq.
Proof.
  pre_process.
  subst retval.
  unfold store_Z.
  Exists rptr (Zabs rsize) rcap.
  Exists optr osize ocap.
  replace (Zabs (Zabs z_neq)) with (Zabs z_neq)
    by (destruct (Z_lt_dec z_neq 0); rewrite ?Z.abs_neq, ?Z.abs_eq by lia; lia).
  replace (Zabs (Zabs rsize)) with (Zabs rsize)
    by (destruct (Z_lt_dec rsize 0); rewrite ?Z.abs_neq, ?Z.abs_eq by lia; lia).
  entailer!.
  unfold same_sign.
  lia.
Qed.

Lemma proof_of_mpz_abs_partial_solve_wit_3_eq_pure : mpz_abs_partial_solve_wit_3_eq_pure.
Proof.
  unfold mpz_abs_partial_solve_wit_3_eq_pure.
  left.
  intros.
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD ptr (Zabs z_eq) (Zabs size)).
  Intros.
  assert (Hsize_bounds: size <= INT_MAX /\ INT_MIN < size).
  {
    pose proof H as Hrange.
    change Int.max_unsigned with 4294967295 in Hrange.
    assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.
    rewrite Hcalc in Hrange.
    split; [lia | assert (size <> INT_MIN) by (intro Heq; subst size; cbn in Hrange; lia); lia].
  }
  destruct Hsize_bounds as [Hsize_le Hsize_gt].
  entailer!.
Qed.

Lemma proof_of_mpz_abs_partial_solve_wit_4_neq_pure : mpz_abs_partial_solve_wit_4_neq_pure.
Proof.
  unfold mpz_abs_partial_solve_wit_4_neq_pure.
  left.
  intros.
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD rptr (Zabs z_neq) (Zabs rsize)).
  Intros.
  assert (Hrsize_bounds: rsize <= INT_MAX /\ INT_MIN < rsize).
  {
    pose proof H as Hrange.
    change Int.max_unsigned with 4294967295 in Hrange.
    assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.
    rewrite Hcalc in Hrange.
    split; [lia | assert (rsize <> INT_MIN) by (intro Heq; subst rsize; cbn in Hrange; lia); lia].
  }
  destruct Hrsize_bounds as [Hrsize_le Hrsize_gt].
  entailer!.
Qed.
