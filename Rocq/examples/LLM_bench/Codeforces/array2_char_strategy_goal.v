From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition array2_char_strategy1 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_Z : (@list Z)) (p : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((CharArray2.full p n m rows))
    |--
    (
    TT &&
    emp **
    ((CharArray2.missing_i p i 0 n m rows)) **
    ((CharArray.missing_i (p + ((i * m) * sizeof(CHAR))) j 0 m (Znth i rows __default_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (@Znth Z j (Znth i rows __default_app1_Z) 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_char ((p + ((i * m) * sizeof(CHAR))) + (j * sizeof(CHAR))) v))
      ).

Definition array2_char_strategy6 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_Z : (@list Z)) (p : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((CharArray2.full p n m rows))
    |--
    (
    TT &&
    emp **
    ((CharArray2.missing_i p i 0 n m rows)) **
    ((CharArray.missing_i (p + ((i * m) * sizeof(CHAR))) j 0 m (Znth i rows __default_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (@Znth Z j (Znth i rows __default_app1_Z) 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_char (p + (((i * m) + j) * sizeof(CHAR))) v))
      ).

Definition array2_char_strategy7 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (j : Z) (__default_app1_Z : (@list Z)) (p : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((CharArray2.full p n m rows))
    |--
    (
    TT &&
    emp **
    ((CharArray2.missing_i p i 0 n m rows)) **
    ((CharArray.missing_i (p + (i * (w * sizeof(CHAR)))) j 0 m (Znth i rows __default_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (@Znth Z j (Znth i rows __default_app1_Z) 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_char ((p + (i * (w * sizeof(CHAR)))) + (j * sizeof(CHAR))) v))
      ).

Definition array2_char_strategy4 :=
  forall (p : Z) (m : Z) (rows1 : (@list (@list Z))) (n : Z),
    TT &&
    emp **
    ((CharArray2.full p n m rows1))
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
      ((CharArray2.full p n m rows2))
      ).

Definition array2_char_strategy5 :=
  forall (p : Z) (lo : Z) (m : Z) (rows : (@list (@list Z))) (hi : Z) (i : Z),
    TT &&
    emp **
    ((CharArray2.missing_i p i lo hi m rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((CharArray2.missing_i p i lo hi m rows))
    ).

Definition array2_char_strategy2 :=
  forall (i : Z) (n : Z) (m : Z) (p : Z) (__default_app1_Z : (@list Z)) (rows : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((CharArray2.missing_i p i 0 n m rows)) **
    ((CharArray.full (p + ((i * m) * sizeof(CHAR))) m (Znth i rows __default_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((CharArray2.full p n m rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array2_char_strategy8 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (p : Z) (__default_app1_Z : (@list Z)) (rows : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((CharArray2.missing_i p i 0 n m rows)) **
    ((CharArray.full (p + (i * (w * sizeof(CHAR)))) m (Znth i rows __default_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((CharArray2.full p n m rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array2_char_strategy9 :=
  forall (i : Z) (n : Z) (m : Z) (p : Z) (__default_app1_Z : (@list Z)) (rows : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((CharArray2.missing_i p i 0 n m rows)) **
    ((CharArray.full (p + ((i * m) * sizeof(CHAR))) m (Znth i rows __default_app1_Z)))
    |--
    (
    TT &&
    emp **
    ((CharArray2.full p n m rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type array2_char_Strategy_Correct.

  Axiom array2_char_strategy1_correctness : array2_char_strategy1.
  Axiom array2_char_strategy6_correctness : array2_char_strategy6.
  Axiom array2_char_strategy7_correctness : array2_char_strategy7.
  Axiom array2_char_strategy4_correctness : array2_char_strategy4.
  Axiom array2_char_strategy5_correctness : array2_char_strategy5.
  Axiom array2_char_strategy2_correctness : array2_char_strategy2.
  Axiom array2_char_strategy8_correctness : array2_char_strategy8.
  Axiom array2_char_strategy9_correctness : array2_char_strategy9.

End array2_char_Strategy_Correct.
