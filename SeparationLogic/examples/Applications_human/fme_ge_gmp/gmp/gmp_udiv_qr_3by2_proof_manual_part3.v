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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qr_3by2_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qr_3by2_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.
Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_6_1 : gmp_udiv_qr_3by2_entail_wit_6_1.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_6_1; intros.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  assert (Hqext_bounds: 1 <= qhat + 1 <= 4294967296) by abstract lia.
  assert (Heq_qhat:
    n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre =
    (qhat + 1) * (d1_pre * 4294967296 + d0_pre) + rpre1 * 4294967296 + rpre0).
  { rewrite <- PreH1. exact PreH26. }
  destruct (Z.eq_dec (qhat + 1) 4294967296) as [Hwrap | Hnowrap].
  - assert (Hlow: unsigned_last_nbits (qhat + 1) 32 = 0).
    { rewrite Hwrap.
      unfold unsigned_last_nbits.
      change (2 ^ 32) with 4294967296.
      apply Z.mod_same.
      lia. }
    assert (Heq_wrap:
      n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre =
      4294967296 * (d1_pre * 4294967296 + d0_pre) + rpre1 * 4294967296 + rpre0).
    { rewrite Hwrap in Heq_qhat. exact Heq_qhat. }
    Right.
    Exists 4294967296.
    split_pure_spatial.
    2: {
      split_pures.
      all: try (dump_pre_spatial;
        first [rewrite ?Hlow; reflexivity | exact PreH2 | exact PreH3 | exact PreH4 | exact PreH5 | exact PreH6 |
               exact PreH7 | exact PreH8 | exact PreH9 | exact PreH10 | exact PreH11 | exact PreH12 |
               exact PreH13 | exact PreH14 | exact PreH19 | exact PreH20 | exact PreH21 | exact PreH22 |
               exact PreH23 | exact PreH24 | exact PreH25 | exact PreH26 | exact Heq_wrap | lia]).
    }
    all: try cancel.
  - assert (Hlow: unsigned_last_nbits (qhat + 1) 32 = qhat + 1).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    Left.
    Exists (unsigned_last_nbits (qhat + 1) 32).
    split_pure_spatial.
    2: {
      split_pures.
      all: try (dump_pre_spatial;
        first [rewrite ?Hlow; reflexivity | exact PreH2 | exact PreH3 | exact PreH4 | exact PreH5 | exact PreH6 |
               exact PreH7 | exact PreH8 | exact PreH9 | exact PreH10 | exact PreH11 | exact PreH12 |
               exact PreH13 | exact PreH14 | exact PreH19 | exact PreH20 | exact PreH21 | exact PreH22 |
               exact PreH23 | exact PreH24 | exact PreH25 | exact PreH26 | rewrite Hlow; exact Heq_qhat | lia]).
    }
    all: try cancel.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_6_2 : gmp_udiv_qr_3by2_entail_wit_6_2.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_6_2; intros.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  assert (Hqext_bounds: 1 <= qhat + 1 <= 4294967296) by lia.
  assert (Heq_qhat:
    n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre + 4294967296 ^ 2 =
    (qhat + 1) * (d1_pre * 4294967296 + d0_pre) + rpre1 * 4294967296 + rpre0).
  { rewrite <- PreH1. exact PreH27. }
  destruct (Z.eq_dec (qhat + 1) 4294967296) as [Hwrap | Hnowrap].
  - assert (Hlow: unsigned_last_nbits (qhat + 1) 32 = 0).
    { rewrite Hwrap.
      unfold unsigned_last_nbits.
      change (2 ^ 32) with 4294967296.
      apply Z.mod_same.
      lia. }
    Right.
    assert (Heq_wrap:
      n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre + 4294967296 ^ 2 =
      4294967296 * (d1_pre * 4294967296 + d0_pre) + rpre1 * 4294967296 + rpre0).
    { rewrite Hwrap in Heq_qhat. exact Heq_qhat. }
    Exists 4294967296.
    split_pure_spatial.
    2: {
      split_pures.
      all: try (dump_pre_spatial;
        first [rewrite ?Hlow; reflexivity | exact PreH2 | exact PreH3 | exact PreH4 | exact PreH5 | exact PreH6 |
               exact PreH7 | exact PreH8 | exact PreH9 | exact PreH10 | exact PreH11 | exact PreH12 |
               exact PreH13 | exact PreH14 | exact PreH19 | exact PreH20 | exact PreH21 | exact PreH22 |
               exact PreH23 | exact PreH24 | exact PreH25 | exact PreH26 | exact Heq_wrap | lia]).
    }
    all: try cancel.
  - assert (Hlow: unsigned_last_nbits (qhat + 1) 32 = qhat + 1).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    Left.
    Exists (unsigned_last_nbits (qhat + 1) 32).
    split_pure_spatial.
    2: {
      split_pures.
      all: try (dump_pre_spatial;
        first [rewrite ?Hlow; reflexivity | exact PreH2 | exact PreH3 | exact PreH4 | exact PreH5 | exact PreH6 |
               exact PreH7 | exact PreH8 | exact PreH9 | exact PreH10 | exact PreH11 | exact PreH12 |
               exact PreH13 | exact PreH14 | exact PreH19 | exact PreH20 | exact PreH21 | exact PreH22 |
               exact PreH23 | exact PreH24 | exact PreH25 | exact PreH26 | rewrite Hlow; exact Heq_qhat | lia]).
    }
    all: try cancel.
Qed.

Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_6_3 : gmp_udiv_qr_3by2_entail_wit_6_3.
Proof.
  unfold gmp_udiv_qr_3by2_entail_wit_6_3; intros.
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  assert (Hqext_bounds: 1 <= qhat + 1 <= 4294967296) by lia.
  assert (Heq_qhat:
    n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre =
    (qhat + 1) * (d1_pre * 4294967296 + d0_pre) + rpre1 * 4294967296 + rpre0).
  { rewrite <- PreH1. exact PreH27. }
  destruct (Z.eq_dec (qhat + 1) 4294967296) as [Hwrap | Hnowrap].
  - assert (Hlow: unsigned_last_nbits (qhat + 1) 32 = 0).
    { rewrite Hwrap.
      unfold unsigned_last_nbits.
      change (2 ^ 32) with 4294967296.
      apply Z.mod_same.
      lia. }
    assert (Heq_wrap:
      n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre =
      4294967296 * (d1_pre * 4294967296 + d0_pre) + rpre1 * 4294967296 + rpre0).
    { rewrite Hwrap in Heq_qhat. exact Heq_qhat. }
    Right.
    Exists 4294967296.
    split_pure_spatial.
    2: {
      split_pures.
      all: try (dump_pre_spatial;
        first [rewrite ?Hlow; reflexivity | exact PreH2 | exact PreH3 | exact PreH4 | exact PreH5 | exact PreH6 |
               exact PreH7 | exact PreH8 | exact PreH9 | exact PreH10 | exact PreH11 | exact PreH12 |
               exact PreH13 | exact PreH14 | exact PreH19 | exact PreH20 | exact PreH21 | exact PreH22 |
               exact PreH23 | exact PreH24 | exact PreH25 | exact PreH26 | exact Heq_wrap | lia]).
    }
    all: try cancel.
  - assert (Hlow: unsigned_last_nbits (qhat + 1) 32 = qhat + 1).
    { apply unsigned_last_nbits_eq.
      change (2 ^ 32) with 4294967296.
      lia. }
    Left.
    Exists (unsigned_last_nbits (qhat + 1) 32).
    split_pure_spatial.
    2: {
      split_pures.
      all: try (dump_pre_spatial;
        first [rewrite ?Hlow; reflexivity | exact PreH2 | exact PreH3 | exact PreH4 | exact PreH5 | exact PreH6 |
               exact PreH7 | exact PreH8 | exact PreH9 | exact PreH10 | exact PreH11 | exact PreH12 |
               exact PreH13 | exact PreH14 | exact PreH19 | exact PreH20 | exact PreH21 | exact PreH22 |
               exact PreH23 | exact PreH24 | exact PreH25 | exact PreH26 | rewrite Hlow; exact Heq_qhat | lia]).
    }
    all: try cancel.
Qed.
