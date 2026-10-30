From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition uint64_array_shape_strategy1 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UInt64Array.full_shape p n))
    |--
    EX (x : Z),
      (
      TT &&
      emp **
      ((UInt64Array.missing_i_shape p i 0 n)) **
      ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) x))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) v)) -*
        TT &&
        emp **
        ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) v))
        ).

Definition uint64_array_shape_strategy3 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x < y) ”) &&
    emp **
    ((UInt64Array.seg_shape p x y))
    |--
    EX (v0 : Z),
      (
      TT &&
      emp **
      ((poly_store FET_uint64 (p + (x * sizeof(UINT64))) v0)) **
      ((UInt64Array.seg_shape p (x + 1) y))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_uint64 (p + (x * sizeof(UINT64))) v)) -*
        TT &&
        emp **
        ((poly_store FET_uint64 (p + (x * sizeof(UINT64))) v))
        ).

Definition uint64_array_shape_strategy6 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((UInt64Array.seg_shape p x y))
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

Definition uint64_array_shape_strategy7 :=
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
      ((UInt64Array.seg_shape p x y))
      ).

Definition uint64_array_shape_strategy8 :=
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
      ((UInt64Array.full_shape p n))
      ).

Definition uint64_array_shape_strategy9 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((UInt64Array.seg_shape p 0 i))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.full_shape p n))
    ).

Definition uint64_array_shape_strategy10 :=
  forall (x1 : Z) (x : Z) (y : Z) (y1 : Z) (p : Z),
    TT &&
    (“ (y1 = y) ”) &&
    (“ (x1 = x) ”) &&
    emp **
    ((UInt64Array.seg_shape p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.seg_shape p x1 y1))
    ).

Definition uint64_array_shape_strategy2 :=
  forall (i : Z) (n : Z) (v : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UInt64Array.missing_i_shape p i 0 n)) **
    ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) v))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.full_shape p n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_shape_strategy4 :=
  forall (x : Z) (i : Z) (y : Z) (v : Z) (p : Z),
    TT &&
    (“ (x = (i + 1)) ”) &&
    emp **
    ((UInt64Array.seg_shape p x y)) **
    ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) v))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.seg_shape p i y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_shape_strategy5 :=
  forall (y : Z) (v : Z) (p : Z) (z : Z),
    TT &&
    emp **
    ((UInt64Array.seg_shape p y z)) **
    ((poly_store FET_uint64 (p + (z * sizeof(UINT64))) v))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.seg_shape p y (z + 1)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type uint64_array_shape_Strategy_Correct.

  Axiom uint64_array_shape_strategy1_correctness : uint64_array_shape_strategy1.
  Axiom uint64_array_shape_strategy3_correctness : uint64_array_shape_strategy3.
  Axiom uint64_array_shape_strategy6_correctness : uint64_array_shape_strategy6.
  Axiom uint64_array_shape_strategy7_correctness : uint64_array_shape_strategy7.
  Axiom uint64_array_shape_strategy8_correctness : uint64_array_shape_strategy8.
  Axiom uint64_array_shape_strategy9_correctness : uint64_array_shape_strategy9.
  Axiom uint64_array_shape_strategy10_correctness : uint64_array_shape_strategy10.
  Axiom uint64_array_shape_strategy2_correctness : uint64_array_shape_strategy2.
  Axiom uint64_array_shape_strategy4_correctness : uint64_array_shape_strategy4.
  Axiom uint64_array_shape_strategy5_correctness : uint64_array_shape_strategy5.

End uint64_array_shape_Strategy_Correct.
