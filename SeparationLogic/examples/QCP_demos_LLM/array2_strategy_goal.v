Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition array2_strategy1 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_Z : (@list Z)) (p : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (Z.le 0 j) ”) &&
    (“ (Z.lt j m) ”) &&
    emp **
    ((IntArray2.full p n m rows))
    |--
    (
    TT &&
    emp **
    ((IntArray2.missing_i p i 0 n m rows)) **
    ((IntArray.missing_i (Z.add p (Z.mul (Z.mul i m) (@sizeof_front_end_type FET_int))) j 0 m (Znth i rows __default_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (@Znth Z j (Znth i rows __default_app1_Z) 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int (Z.add (Z.add p (Z.mul (Z.mul i m) (@sizeof_front_end_type FET_int))) (Z.mul j (@sizeof_front_end_type FET_int))) v))
      ).

Definition array2_strategy6 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_Z : (@list Z)) (p : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (Z.le 0 j) ”) &&
    (“ (Z.lt j m) ”) &&
    emp **
    ((IntArray2.full p n m rows))
    |--
    (
    TT &&
    emp **
    ((IntArray2.missing_i p i 0 n m rows)) **
    ((IntArray.missing_i (Z.add p (Z.mul (Z.mul i m) (@sizeof_front_end_type FET_int))) j 0 m (Znth i rows __default_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (@Znth Z j (Znth i rows __default_app1_Z) 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int (Z.add p (Z.mul (Z.add (Z.mul i m) j) (@sizeof_front_end_type FET_int))) v))
      ).

Definition array2_strategy4 :=
  forall (p : Z) (m : Z) (rows1 : (@list (@list Z))) (n : Z),
    TT &&
    emp **
    ((IntArray2.full p n m rows1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (rows2 : (@list (@list Z))),
      TT &&
      (“ (rows1 = rows2) ”) &&
      emp -*
      TT &&
      emp **
      ((IntArray2.full p n m rows2))
      ).

Definition array2_strategy5 :=
  forall (p : Z) (lo : Z) (m : Z) (rows : (@list (@list Z))) (hi : Z) (i : Z),
    TT &&
    emp **
    ((IntArray2.missing_i p i lo hi m rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray2.missing_i p i lo hi m rows))
    ).

Definition array2_strategy2 :=
  forall (i : Z) (n : Z) (m : Z) (p : Z) (__default_app1_Z : (@list Z)) (rows : (@list (@list Z))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((IntArray2.missing_i p i 0 n m rows)) **
    ((IntArray.full (Z.add p (Z.mul (Z.mul i m) (@sizeof_front_end_type FET_int))) m (Znth i rows __default_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((IntArray2.full p n m rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type array2_Strategy_Correct.

  Axiom array2_strategy1_correctness : array2_strategy1.
  Axiom array2_strategy6_correctness : array2_strategy6.
  Axiom array2_strategy4_correctness : array2_strategy4.
  Axiom array2_strategy5_correctness : array2_strategy5.
  Axiom array2_strategy2_correctness : array2_strategy2.

End array2_Strategy_Correct.
