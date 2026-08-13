Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minigmp.GmpAux SimpleC.EE.Applications_human.minigmp.GmpNumber.
Import Aux.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition gmp_strategy1 :=
  forall (size : Z) (s : Z) (base : Z) (val : Z) (ptr : Z),
    TT &&
    (“ (size = s) ”) &&
    emp **
    ((mpd_store_Z_compact base ptr val size))
    |--
    (
    TT &&
    (“ (is_compact_Z base val size) ”) &&
    emp
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (val = v) ”) &&
      emp -*
      TT &&
      emp **
      ((mpd_store_Z base ptr v s))
      ).

Definition gmp_strategy2 :=
  forall (n : Z) (x : Z),
    TT &&
    emp **
    ((store_Z x n))
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
      ((mpd_store_Z_compact ( UINT_MOD) ptr ( Zabs n) ( Zabs size))) **
      ((UIntArray.undef_seg ptr ( Zabs size) cap))
      ) ** (
      ALL (y : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") y) || (poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") y) || (poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") y)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") y) || (poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") y) || (poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") y))
        ).

Definition gmp_strategy3 :=
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
      ((mpd_store_Z_compact ( UINT_MOD) ptr ( Zabs n) ( Zabs size))) **
      ((UIntArray.undef_seg ptr ( Zabs size) cap)) -*
      TT &&
      emp **
      ((store_Z x n))
      ).

Definition gmp_strategy4 :=
  forall (size : Z) (n : Z) (x : Z),
    TT &&
    emp **
    ((store_Z_remain_size x n size))
    |--
    EX (ptr : Z) (old_size : Z) (cap : Z),
      (
      TT &&
      (“ (Z.le ( Zabs size) cap) ”) &&
      (“ (same_sign n size) ”) &&
      emp **
      ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") old_size)) **
      ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") cap)) **
      ((poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") ptr)) **
      ((mpd_store_Z_compact ( UINT_MOD) ptr ( Zabs n) ( Zabs size))) **
      ((UIntArray.undef_seg ptr ( Zabs size) cap))
      ) ** (
      ALL (y : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") y) || (poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") y) || (poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") y)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_size") y) || (poly_store FET_int &( ((x)) # "__mpz_struct" ->ₛ "_mp_alloc") y) || (poly_store FET_ptr &( ((x)) # "__mpz_struct" ->ₛ "_mp_d") y))
        ).

Module Type gmp_Strategy_Correct.

  Axiom gmp_strategy1_correctness : gmp_strategy1.
  Axiom gmp_strategy2_correctness : gmp_strategy2.
  Axiom gmp_strategy3_correctness : gmp_strategy3.
  Axiom gmp_strategy4_correctness : gmp_strategy4.

End gmp_Strategy_Correct.
