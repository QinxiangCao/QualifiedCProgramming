From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition array3_strategy1 :=
  forall (ak : Z) (k : Z) (i : Z) (n : Z) (m : Z) (am : Z) (p : Z) (cubes : (@list (@list (@list Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
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
      ((IntArray2.full (p + (i * (am * (ak * sizeof(INT))))) m k plane))
      ).

Definition array3_strategy2 :=
  forall (ak2 : Z) (k : Z) (am : Z) (m : Z) (n : Z) (i : Z) (j : Z) (l : Z) (ak : Z) (__default_app1_app1_Z : (@list (@list Z))) (p : Z) (cubes : (@list (@list (@list Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    (“ (0 <= l) ”) &&
    (“ (l < k) ”) &&
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
    ((IntArray2.full (p + (i * (am * (ak * sizeof(INT))))) m k (Znth i cubes __default_app1_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_int (((p + (i * (am * (ak * sizeof(INT))))) + (j * (ak2 * sizeof(INT)))) + (l * sizeof(INT))) v)) -*
      TT &&
      emp **
      ((poly_store FET_int (((p + (i * (am * (ak * sizeof(INT))))) + (j * (ak2 * sizeof(INT)))) + (l * sizeof(INT))) v))
      ).

Definition array3_strategy6 :=
  forall (ak2 : Z) (k : Z) (am : Z) (m : Z) (n : Z) (i : Z) (ak : Z) (p : Z) (cubes : (@list (@list (@list Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
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
      ((IntArray2.full ((p + (i * (am * (ak * sizeof(INT))))) + (0 * (ak2 * sizeof(INT)))) m k plane))
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
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    emp **
    ((IntArray3.missing_i p i 0 n m k cubes)) **
    ((IntArray2.full (p + (i * (am * (ak * sizeof(INT))))) m k (Znth i cubes __default_app1_app1_Z)))
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
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (am = m) ”) &&
    (“ (ak = k) ”) &&
    (“ (ak2 = k) ”) &&
    emp **
    ((IntArray3.missing_i p i 0 n m k cubes)) **
    ((IntArray2.full ((p + (i * (am * (ak * sizeof(INT))))) + (0 * (ak2 * sizeof(INT)))) m k (Znth i cubes __default_app1_app1_Z)))
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
