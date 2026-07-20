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

Definition mpz_tdiv_r_read0_strategy3 :=
  forall (p : Z) (s1 : Z) (v1 : Z),
    TT &&
    emp **
    ((mpd_store_Z_compact_read0 p v1 s1))
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
      ((mpd_store_Z_compact_read0 p v2 s2))
      ).

Definition mpz_tdiv_r_read0_strategy1 :=
  forall (n : Z) (x : Z),
    TT &&
    emp **
    ((store_Z_read0 x n))
    |--
    EX (ptr : Z) (size : Z) (cap : Z),
      (
      TT &&
      (“ (Z.le ( Zabs size) cap) ”) &&
      (“ (same_sign n size) ”) &&
      emp **
      ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") size)) **
      ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") cap)) **
      ((poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") ptr)) **
      ((mpd_store_Z_compact_read0 ptr ( Zabs n) ( Zabs size))) **
      ((UIntArray.undef_seg ptr ( Zmax ( Zabs size) 1) cap))
      ) ** (
      ALL (y : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") y) || (poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") y) || (poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") y)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") y) || (poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") y) || (poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") y))
        ).

Definition mpz_tdiv_r_read0_strategy2 :=
  forall (y : Z) (x : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") y) || (poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") y) || (poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") y) || (poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") y) || (poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") y))
    ) ** (
    ALL (size : Z) (n : Z) (cap : Z) (ptr : Z),
      TT &&
      (“ (Z.le ( Zabs size) cap) ”) &&
      (“ (same_sign n size) ”) &&
      emp **
      ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") size)) **
      ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") cap)) **
      ((poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") ptr)) **
      ((mpd_store_Z_compact_read0 ptr ( Zabs n) ( Zabs size))) **
      ((UIntArray.undef_seg ptr ( Zmax ( Zabs size) 1) cap)) -*
      TT &&
      emp **
      ((store_Z_read0 x n))
      ).

Module Type mpz_tdiv_r_read0_Strategy_Correct.

  Axiom mpz_tdiv_r_read0_strategy3_correctness : mpz_tdiv_r_read0_strategy3.
  Axiom mpz_tdiv_r_read0_strategy1_correctness : mpz_tdiv_r_read0_strategy1.
  Axiom mpz_tdiv_r_read0_strategy2_correctness : mpz_tdiv_r_read0_strategy2.

End mpz_tdiv_r_read0_Strategy_Correct.
