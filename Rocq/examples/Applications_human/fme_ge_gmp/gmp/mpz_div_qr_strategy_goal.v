Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition mpz_div_qr_strategy1 :=
  forall (p : Z) (l : (@list Z)) (full_cap : Z),
    TT &&
    emp **
    ((UIntArray.full p full_cap l))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (v : Z) (used : Z) (store_cap : Z),
      TT &&
      (“ (Z.le 0 used) ”) &&
      (“ (Z.le used full_cap) ”) &&
      (“ (full_cap = store_cap) ”) &&
      (“ (v = ( list_to_Z ( UINT_MOD) (@sublist Z 0 used l))) ”) &&
      (“ (is_compact_Z ( UINT_MOD) v used) ”) &&
      emp -*
      TT &&
      emp **
      ((mpd_store_Z_compact ( UINT_MOD) p v used)) **
      ((UIntArray.undef_seg p used store_cap))
      ).

Definition mpz_div_qr_strategy2 :=
  forall (v1 : Z) (s1 : Z) (p : Z),
    TT &&
    emp **
    ((mpd_store_Z_compact ( UINT_MOD) p v1 s1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (s2 : Z) (v2 : Z),
      TT &&
      (“ (v1 = v2) ”) &&
      (“ (s1 = s2) ”) &&
      emp -*
      TT &&
      emp **
      ((mpd_store_Z_compact ( UINT_MOD) p v2 s2))
      ).

Definition mpz_div_qr_strategy3 :=
  forall (p : Z) (hi : Z) (l : (@list Z)) (lo : Z),
    TT &&
    emp **
    ((UIntArray.seg p lo hi l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.undef_seg p lo hi))
    ).

Definition mpz_div_qr_strategy4 :=
  forall (lo : Z) (l : (@list Z)) (x : Z) (p : Z) (z : Z) (hi : Z),
    TT &&
    emp **
    ((UIntArray.undef_seg p x lo)) **
    ((UIntArray.seg p lo hi l)) **
    ((UIntArray.undef_seg p hi z))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (x_goal : Z) (z_goal : Z),
      TT &&
      (“ (x = x_goal) ”) &&
      (“ (z = z_goal) ”) &&
      (“ (Z.le x lo) ”) &&
      (“ (Z.le lo hi) ”) &&
      (“ (Z.le hi z) ”) &&
      emp -*
      TT &&
      emp **
      ((UIntArray.undef_seg p x_goal z_goal))
      ).

Module Type mpz_div_qr_Strategy_Correct.

  Axiom mpz_div_qr_strategy1_correctness : mpz_div_qr_strategy1.
  Axiom mpz_div_qr_strategy2_correctness : mpz_div_qr_strategy2.
  Axiom mpz_div_qr_strategy3_correctness : mpz_div_qr_strategy3.
  Axiom mpz_div_qr_strategy4_correctness : mpz_div_qr_strategy4.

End mpz_div_qr_Strategy_Correct.
