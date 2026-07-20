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

Definition gmp_optional_strategy1 :=
  forall (x : Z) (z : Z),
    TT &&
    (“ (x <> 0) ”) &&
    emp **
    ((optional_store_Z x z))
    |--
    (
    TT &&
    (“ (x <> 0) ”) &&
    emp **
    ((store_Z x z))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition gmp_optional_strategy2 :=
  forall (x : Z),
    TT &&
    (“ (x <> 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (x <> 0) ”) &&
    emp
    ) ** (
    ALL (z : Z),
      TT &&
      emp **
      ((store_Z x z)) -*
      TT &&
      emp **
      ((optional_store_Z x z))
      ).

Definition gmp_optional_strategy3 :=
  forall (x : Z) (z : Z),
    TT &&
    (“ (x = 0) ”) &&
    emp **
    ((optional_store_Z x z))
    |--
    (
    TT &&
    (“ (x = 0) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition gmp_optional_strategy4 :=
  forall (x : Z),
    TT &&
    (“ (x = 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (x = 0) ”) &&
    emp
    ) ** (
    ALL (z : Z),
      TT &&
      emp -*
      TT &&
      emp **
      ((optional_store_Z x z))
      ).

Definition gmp_optional_strategy5 :=
  forall (x : Z) (n : Z),
    TT &&
    (“ (x <> 0) ”) &&
    emp **
    ((optional_q_undef x n))
    |--
    (
    TT &&
    (“ (x <> 0) ”) &&
    emp **
    ((UIntArray.undef_full x n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition gmp_optional_strategy6 :=
  forall (x : Z),
    TT &&
    (“ (x <> 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (x <> 0) ”) &&
    emp
    ) ** (
    ALL (n : Z),
      TT &&
      emp **
      ((UIntArray.undef_full x n)) -*
      TT &&
      emp **
      ((optional_q_undef x n))
      ).

Definition gmp_optional_strategy7 :=
  forall (x : Z) (n : Z),
    TT &&
    (“ (x = 0) ”) &&
    emp **
    ((optional_q_undef x n))
    |--
    (
    TT &&
    (“ (x = 0) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition gmp_optional_strategy8 :=
  forall (x : Z),
    TT &&
    (“ (x = 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (x = 0) ”) &&
    emp
    ) ** (
    ALL (n : Z),
      TT &&
      emp -*
      TT &&
      emp **
      ((optional_q_undef x n))
      ).

Definition gmp_optional_strategy9 :=
  forall (x : Z) (l : (@list Z)) (n : Z),
    TT &&
    (“ (x <> 0) ”) &&
    emp **
    ((optional_q_full x n l))
    |--
    (
    TT &&
    (“ (x <> 0) ”) &&
    emp **
    ((UIntArray.full x n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition gmp_optional_strategy10 :=
  forall (x : Z),
    TT &&
    (“ (x <> 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (x <> 0) ”) &&
    emp
    ) ** (
    ALL (l : (@list Z)) (n : Z),
      TT &&
      emp **
      ((UIntArray.full x n l)) -*
      TT &&
      emp **
      ((optional_q_full x n l))
      ).

Definition gmp_optional_strategy11 :=
  forall (x : Z) (l : (@list Z)) (n : Z),
    TT &&
    (“ (x = 0) ”) &&
    emp **
    ((optional_q_full x n l))
    |--
    (
    TT &&
    (“ (x = 0) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition gmp_optional_strategy12 :=
  forall (x : Z),
    TT &&
    (“ (x = 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (x = 0) ”) &&
    emp
    ) ** (
    ALL (l : (@list Z)) (n : Z),
      TT &&
      emp -*
      TT &&
      emp **
      ((optional_q_full x n l))
      ).

Module Type gmp_optional_Strategy_Correct.

  Axiom gmp_optional_strategy1_correctness : gmp_optional_strategy1.
  Axiom gmp_optional_strategy2_correctness : gmp_optional_strategy2.
  Axiom gmp_optional_strategy3_correctness : gmp_optional_strategy3.
  Axiom gmp_optional_strategy4_correctness : gmp_optional_strategy4.
  Axiom gmp_optional_strategy5_correctness : gmp_optional_strategy5.
  Axiom gmp_optional_strategy6_correctness : gmp_optional_strategy6.
  Axiom gmp_optional_strategy7_correctness : gmp_optional_strategy7.
  Axiom gmp_optional_strategy8_correctness : gmp_optional_strategy8.
  Axiom gmp_optional_strategy9_correctness : gmp_optional_strategy9.
  Axiom gmp_optional_strategy10_correctness : gmp_optional_strategy10.
  Axiom gmp_optional_strategy11_correctness : gmp_optional_strategy11.
  Axiom gmp_optional_strategy12_correctness : gmp_optional_strategy12.

End gmp_optional_Strategy_Correct.
