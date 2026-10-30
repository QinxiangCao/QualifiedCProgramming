From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition short_array_shape_strategy1 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((ShortArray.full_shape p n))
    |--
    EX (x : Z),
      (
      TT &&
      emp **
      ((ShortArray.missing_i_shape p i 0 n)) **
      ((poly_store FET_short (p + (i * sizeof(SHORT))) x))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_short (p + (i * sizeof(SHORT))) v)) -*
        TT &&
        emp **
        ((poly_store FET_short (p + (i * sizeof(SHORT))) v))
        ).

Definition short_array_shape_strategy3 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x < y) ”) &&
    emp **
    ((ShortArray.seg_shape p x y))
    |--
    EX (v0 : Z),
      (
      TT &&
      emp **
      ((poly_store FET_short (p + (x * sizeof(SHORT))) v0)) **
      ((ShortArray.seg_shape p (x + 1) y))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_short (p + (x * sizeof(SHORT))) v)) -*
        TT &&
        emp **
        ((poly_store FET_short (p + (x * sizeof(SHORT))) v))
        ).

Definition short_array_shape_strategy6 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((ShortArray.seg_shape p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition short_array_shape_strategy7 :=
  forall (x : Z) (y : Z),
    TT &&
    (“ (x = y) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (p : Z),
      TT &&
      emp -*
      TT &&
      emp **
      ((ShortArray.seg_shape p x y))
      ).

Definition short_array_shape_strategy8 :=
  forall (n : Z),
    TT &&
    (“ (n = 0) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (p : Z),
      TT &&
      emp -*
      TT &&
      emp **
      ((ShortArray.full_shape p n))
      ).

Definition short_array_shape_strategy9 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((ShortArray.seg_shape p 0 i))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((ShortArray.full_shape p n))
    ).

Definition short_array_shape_strategy10 :=
  forall (x1 : Z) (x : Z) (y : Z) (y1 : Z) (p : Z),
    TT &&
    (“ (y1 = y) ”) &&
    (“ (x1 = x) ”) &&
    emp **
    ((ShortArray.seg_shape p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((ShortArray.seg_shape p x1 y1))
    ).

Definition short_array_shape_strategy2 :=
  forall (i : Z) (n : Z) (v : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((ShortArray.missing_i_shape p i 0 n)) **
    ((poly_store FET_short (p + (i * sizeof(SHORT))) v))
    |--
    (
    TT &&
    emp **
    ((ShortArray.full_shape p n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition short_array_shape_strategy4 :=
  forall (x : Z) (i : Z) (y : Z) (v : Z) (p : Z),
    TT &&
    (“ (x = (i + 1)) ”) &&
    emp **
    ((ShortArray.seg_shape p x y)) **
    ((poly_store FET_short (p + (i * sizeof(SHORT))) v))
    |--
    (
    TT &&
    emp **
    ((ShortArray.seg_shape p i y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition short_array_shape_strategy5 :=
  forall (y : Z) (v : Z) (p : Z) (z : Z),
    TT &&
    emp **
    ((ShortArray.seg_shape p y z)) **
    ((poly_store FET_short (p + (z * sizeof(SHORT))) v))
    |--
    (
    TT &&
    emp **
    ((ShortArray.seg_shape p y (z + 1)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type short_array_shape_Strategy_Correct.

  Axiom short_array_shape_strategy1_correctness : short_array_shape_strategy1.
  Axiom short_array_shape_strategy3_correctness : short_array_shape_strategy3.
  Axiom short_array_shape_strategy6_correctness : short_array_shape_strategy6.
  Axiom short_array_shape_strategy7_correctness : short_array_shape_strategy7.
  Axiom short_array_shape_strategy8_correctness : short_array_shape_strategy8.
  Axiom short_array_shape_strategy9_correctness : short_array_shape_strategy9.
  Axiom short_array_shape_strategy10_correctness : short_array_shape_strategy10.
  Axiom short_array_shape_strategy2_correctness : short_array_shape_strategy2.
  Axiom short_array_shape_strategy4_correctness : short_array_shape_strategy4.
  Axiom short_array_shape_strategy5_correctness : short_array_shape_strategy5.

End short_array_shape_Strategy_Correct.
