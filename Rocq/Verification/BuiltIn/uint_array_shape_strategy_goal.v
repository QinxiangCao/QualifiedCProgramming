From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition uint_array_shape_strategy1 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UIntArray.full_shape p n))
    |--
    EX (x : Z),
      (
      TT &&
      emp **
      ((UIntArray.missing_i_shape p i 0 n)) **
      ((poly_store FET_uint (p + (i * sizeof(UINT))) x))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_uint (p + (i * sizeof(UINT))) v)) -*
        TT &&
        emp **
        ((poly_store FET_uint (p + (i * sizeof(UINT))) v))
        ).

Definition uint_array_shape_strategy3 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x < y) ”) &&
    emp **
    ((UIntArray.seg_shape p x y))
    |--
    EX (v0 : Z),
      (
      TT &&
      emp **
      ((poly_store FET_uint (p + (x * sizeof(UINT))) v0)) **
      ((UIntArray.seg_shape p (x + 1) y))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_uint (p + (x * sizeof(UINT))) v)) -*
        TT &&
        emp **
        ((poly_store FET_uint (p + (x * sizeof(UINT))) v))
        ).

Definition uint_array_shape_strategy6 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((UIntArray.seg_shape p x y))
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

Definition uint_array_shape_strategy7 :=
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
      ((UIntArray.seg_shape p x y))
      ).

Definition uint_array_shape_strategy8 :=
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
      ((UIntArray.full_shape p n))
      ).

Definition uint_array_shape_strategy9 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((UIntArray.seg_shape p 0 i))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.full_shape p n))
    ).

Definition uint_array_shape_strategy10 :=
  forall (x1 : Z) (x : Z) (y : Z) (y1 : Z) (p : Z),
    TT &&
    (“ (y1 = y) ”) &&
    (“ (x1 = x) ”) &&
    emp **
    ((UIntArray.seg_shape p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.seg_shape p x1 y1))
    ).

Definition uint_array_shape_strategy2 :=
  forall (i : Z) (n : Z) (v : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UIntArray.missing_i_shape p i 0 n)) **
    ((poly_store FET_uint (p + (i * sizeof(UINT))) v))
    |--
    (
    TT &&
    emp **
    ((UIntArray.full_shape p n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_shape_strategy4 :=
  forall (x : Z) (i : Z) (y : Z) (v : Z) (p : Z),
    TT &&
    (“ (x = (i + 1)) ”) &&
    emp **
    ((UIntArray.seg_shape p x y)) **
    ((poly_store FET_uint (p + (i * sizeof(UINT))) v))
    |--
    (
    TT &&
    emp **
    ((UIntArray.seg_shape p i y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_shape_strategy5 :=
  forall (y : Z) (v : Z) (p : Z) (z : Z),
    TT &&
    emp **
    ((UIntArray.seg_shape p y z)) **
    ((poly_store FET_uint (p + (z * sizeof(UINT))) v))
    |--
    (
    TT &&
    emp **
    ((UIntArray.seg_shape p y (z + 1)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type uint_array_shape_Strategy_Correct.

  Axiom uint_array_shape_strategy1_correctness : uint_array_shape_strategy1.
  Axiom uint_array_shape_strategy3_correctness : uint_array_shape_strategy3.
  Axiom uint_array_shape_strategy6_correctness : uint_array_shape_strategy6.
  Axiom uint_array_shape_strategy7_correctness : uint_array_shape_strategy7.
  Axiom uint_array_shape_strategy8_correctness : uint_array_shape_strategy8.
  Axiom uint_array_shape_strategy9_correctness : uint_array_shape_strategy9.
  Axiom uint_array_shape_strategy10_correctness : uint_array_shape_strategy10.
  Axiom uint_array_shape_strategy2_correctness : uint_array_shape_strategy2.
  Axiom uint_array_shape_strategy4_correctness : uint_array_shape_strategy4.
  Axiom uint_array_shape_strategy5_correctness : uint_array_shape_strategy5.

End uint_array_shape_Strategy_Correct.
