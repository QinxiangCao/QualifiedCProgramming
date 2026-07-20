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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_tdiv_r_entail_wit_1 : mpz_tdiv_r_entail_wit_1.
Proof.
  right.
  intros.
  unfold optional_store_Z.
  Left.
  entailer!.
Qed.

Lemma proof_of_mpz_tdiv_r_entail_wit_2 : mpz_tdiv_r_entail_wit_2.
Proof.
  unfold mpz_tdiv_r_entail_wit_2.
  intros d_pre n_pre r_pre zd zn qv_2 rv_2 retval
    Hr_eq Hmath Hret_low Hret_high Hret_ok Hr_eq2 Hn_nonnull Hzd_pre.
  unfold mpz_div_qr_math in Hmath.
  destruct Hmath as [Htrunc | [Hfloor | Hceil]].
  - unfold mpz_div_qr_math_trunc, GMP_DIV_TRUNC in Htrunc.
    destruct Htrunc as [Hzd [_ [Hdiv [Hrem Hsign]]]].
    destruct Hsign as [Hzero | Hsame].
    + Left.
      Exists rv_2 qv_2.
      entailer!.
    + Right.
      Exists rv_2 qv_2.
      entailer!.
  - unfold mpz_div_qr_math_floor, GMP_DIV_FLOOR in Hfloor.
    lia.
  - unfold mpz_div_qr_math_ceil, GMP_DIV_CEIL in Hceil.
    lia.
Qed.

Lemma proof_of_mpz_tdiv_r_return_wit_1 : mpz_tdiv_r_return_wit_1.
Proof.
  unfold mpz_tdiv_r_return_wit_1.
  intros d_pre n_pre r_pre zd zn qv_2 rv_2 Hr_eq Hzd Hdiv Hrem Hzero.
  Left.
  Exists rv_2 qv_2.
  unfold optional_store_Z.
  Split.
  - Intros_p Hnull. entailer!.
  - Intros_p Hnonnull. entailer!.
Qed.

Lemma proof_of_mpz_tdiv_r_return_wit_2 : mpz_tdiv_r_return_wit_2.
Proof.
  unfold mpz_tdiv_r_return_wit_2.
  intros d_pre n_pre r_pre zd zn qv_2 rv_2 Hr_eq Hzd Hdiv Hrem Hsame.
  Right.
  Exists rv_2 qv_2.
  unfold optional_store_Z.
  Split.
  - Intros_p Hnull. entailer!.
  - Intros_p Hnonnull. entailer!.
Qed.
