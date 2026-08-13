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

Definition array3_strategy1 :=
  forall (ak : Z) (k : Z) (i : Z) (n : Z) (m : Z) (am : Z) (p : Z) (cubes : (@list (@list (@list Z)))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    emp **
    ((IntArray3.full p n m k cubes))
    |--
    (
    TT &&
    emp **
    ((IntArray3.missing_i p i 0 n m k cubes))
    ) ** (
    ALL (plane : (@list (@list Z))) (__default_app1_app1_Z : (@list (@list Z))),
      TT &&
      (“ (plane = (Znth i cubes __default_app1_app1_Z)) ”) &&
      emp -*
      TT &&
      emp **
      ((IntArray2.full (Z.add p (Z.mul i (Z.mul (Z.mul (@sizeof_front_end_type FET_int) ak) am))) m k plane))
      ).

Definition array3_strategy2 :=
  forall (ak2 : Z) (k : Z) (am : Z) (m : Z) (n : Z) (i : Z) (j : Z) (l : Z) (ak : Z) (__default_app1_app1_Z : (@list (@list Z))) (p : Z) (cubes : (@list (@list (@list Z)))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (Z.le 0 j) ”) &&
    (“ (Z.lt j m) ”) &&
    (“ (Z.le 0 l) ”) &&
    (“ (Z.lt l k) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    (“ (ak2 = k) ”) &&
    emp **
    ((IntArray3.full p n m k cubes))
    |--
    (
    TT &&
    emp **
    ((IntArray3.missing_i p i 0 n m k cubes)) **
    ((IntArray2.full (Z.add p (Z.mul i (Z.mul (Z.mul (@sizeof_front_end_type FET_int) ak) am))) m k (Znth i cubes __default_app1_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_int (Z.add (Z.add (Z.add p (Z.mul i (Z.mul (Z.mul (@sizeof_front_end_type FET_int) ak) am))) (Z.mul j (Z.mul (@sizeof_front_end_type FET_int) ak2))) (Z.mul l (@sizeof_front_end_type FET_int))) v)) -*
      TT &&
      emp **
      ((poly_store FET_int (Z.add (Z.add (Z.add p (Z.mul i (Z.mul (Z.mul (@sizeof_front_end_type FET_int) ak) am))) (Z.mul j (Z.mul (@sizeof_front_end_type FET_int) ak2))) (Z.mul l (@sizeof_front_end_type FET_int))) v))
      ).

Definition array3_strategy6 :=
  forall (ak2 : Z) (k : Z) (am : Z) (m : Z) (n : Z) (i : Z) (ak : Z) (p : Z) (cubes : (@list (@list (@list Z)))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    (“ (ak2 = k) ”) &&
    emp **
    ((IntArray3.full p n m k cubes))
    |--
    (
    TT &&
    emp **
    ((IntArray3.missing_i p i 0 n m k cubes))
    ) ** (
    ALL (plane : (@list (@list Z))) (__default_app1_app1_Z : (@list (@list Z))),
      TT &&
      (“ (plane = (Znth i cubes __default_app1_app1_Z)) ”) &&
      emp -*
      TT &&
      emp **
      ((IntArray2.full (Z.add (Z.add p (Z.mul i (Z.mul (Z.mul (@sizeof_front_end_type FET_int) ak) am))) (Z.mul 0 (Z.mul (@sizeof_front_end_type FET_int) ak2))) m k plane))
      ).

Definition array3_strategy4 :=
  forall (p : Z) (m : Z) (cubes1 : (@list (@list (@list Z)))) (k : Z) (n : Z),
    TT &&
    emp **
    ((IntArray3.full p n m k cubes1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (cubes2 : (@list (@list (@list Z)))),
      TT &&
      (“ (cubes1 = cubes2) ”) &&
      emp -*
      TT &&
      emp **
      ((IntArray3.full p n m k cubes2))
      ).

Definition array3_strategy5 :=
  forall (p : Z) (lo : Z) (m : Z) (cubes : (@list (@list (@list Z)))) (k : Z) (hi : Z) (i : Z),
    TT &&
    emp **
    ((IntArray3.missing_i p i lo hi m k cubes))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray3.missing_i p i lo hi m k cubes))
    ).

Definition array3_strategy3 :=
  forall (ak : Z) (k : Z) (i : Z) (n : Z) (m : Z) (am : Z) (p : Z) (cubes : (@list (@list (@list Z)))) (__default_app1_app1_Z : (@list (@list Z))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    emp **
    ((IntArray3.missing_i p i 0 n m k cubes)) **
    ((IntArray2.full (Z.add p (Z.mul i (Z.mul (Z.mul (@sizeof_front_end_type FET_int) ak) am))) m k (Znth i cubes __default_app1_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((IntArray3.full p n m k cubes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array3_strategy7 :=
  forall (ak2 : Z) (k : Z) (am : Z) (m : Z) (n : Z) (i : Z) (ak : Z) (p : Z) (cubes : (@list (@list (@list Z)))) (__default_app1_app1_Z : (@list (@list Z))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    (“ (ak2 = k) ”) &&
    emp **
    ((IntArray3.missing_i p i 0 n m k cubes)) **
    ((IntArray2.full (Z.add (Z.add p (Z.mul i (Z.mul (Z.mul (@sizeof_front_end_type FET_int) ak) am))) (Z.mul 0 (Z.mul (@sizeof_front_end_type FET_int) ak2))) m k (Znth i cubes __default_app1_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((IntArray3.full p n m k cubes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type array3_Strategy_Correct.

  Axiom array3_strategy1_correctness : array3_strategy1.
  Axiom array3_strategy2_correctness : array3_strategy2.
  Axiom array3_strategy6_correctness : array3_strategy6.
  Axiom array3_strategy4_correctness : array3_strategy4.
  Axiom array3_strategy5_correctness : array3_strategy5.
  Axiom array3_strategy3_correctness : array3_strategy3.
  Axiom array3_strategy7_correctness : array3_strategy7.

End array3_Strategy_Correct.
