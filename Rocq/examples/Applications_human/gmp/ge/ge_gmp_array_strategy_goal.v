From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Definition ge_gmp_array_strategy201 :=
  forall (p : Z) (n : Z) (i : Z) (l : (@list Z)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (p <> 0) ”) &&
    emp **
    ((mpz_array p n l))
    |--
    (
    TT &&
    emp **
    ((mpz_missing_i p i 0 n l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (@Znth Z i l 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((store_Z (p + (i * (sizeof_front_end_type (FET_alias ("__mpz_struct"))))) v))
      ).

Definition ge_gmp_array_strategy206 :=
  forall (p : Z) (n : Z) (i : Z) (l : (@list Z)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (p <> 0) ”) &&
    emp **
    ((mpz_missing_i p i 0 n l)) **
    ((store_Z (p + (i * (sizeof_front_end_type (FET_alias ("__mpz_struct"))))) (@Znth Z i l 0)))
    |--
    (
    TT &&
    emp **
    ((mpz_array p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ge_gmp_array_strategy204 :=
  forall (p : Z) (l1 : (@list Z)) (n : Z),
    TT &&
    emp **
    ((mpz_array p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((mpz_array p n l2))
      ).

Definition ge_gmp_array_strategy205 :=
  forall (p : Z) (lo : Z) (l : (@list Z)) (hi : Z) (i : Z),
    TT &&
    emp **
    ((mpz_missing_i p i lo hi l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((mpz_missing_i p i lo hi l))
    ).

Definition ge_gmp_array_strategy202 :=
  forall (p : Z) (n : Z) (i : Z) (l : (@list Z)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (p <> 0) ”) &&
    emp **
    ((mpz_missing_i p i 0 n l)) **
    ((store_Z (p + (i * (sizeof_front_end_type (FET_alias ("__mpz_struct"))))) (@Znth Z i l 0)))
    |--
    (
    TT &&
    emp **
    ((mpz_array p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ge_gmp_array_strategy203 :=
  forall (p : Z) (n : Z) (i : Z) (l : (@list Z)) (v : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (p <> 0) ”) &&
    emp **
    ((mpz_missing_i p i 0 n l)) **
    ((store_Z (p + (i * (sizeof_front_end_type (FET_alias ("__mpz_struct"))))) v))
    |--
    (
    TT &&
    emp **
    ((mpz_array p n (@replace_Znth Z i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type ge_gmp_array_Strategy_Correct.

  Axiom ge_gmp_array_strategy201_correctness : ge_gmp_array_strategy201.
  Axiom ge_gmp_array_strategy206_correctness : ge_gmp_array_strategy206.
  Axiom ge_gmp_array_strategy204_correctness : ge_gmp_array_strategy204.
  Axiom ge_gmp_array_strategy205_correctness : ge_gmp_array_strategy205.
  Axiom ge_gmp_array_strategy202_correctness : ge_gmp_array_strategy202.
  Axiom ge_gmp_array_strategy203_correctness : ge_gmp_array_strategy203.

End ge_gmp_array_Strategy_Correct.
