From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition undef_uint_array_strategy13 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z),
    TT &&
    (“ (i = x) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UIntArray.undef_missing_i p i x y))
    |--
    (
    TT &&
    emp **
    ((UIntArray.undef_seg p (x + 1) y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition undef_uint_array_strategy14 :=
  forall (x : Z) (i : Z) (y : Z) (p : Z),
    TT &&
    (“ ((i + 1) = y) ”) &&
    (“ (x <= i) ”) &&
    emp **
    ((UIntArray.undef_missing_i p i x y))
    |--
    (
    TT &&
    emp **
    ((UIntArray.undef_seg p x i))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition undef_uint_array_strategy16 :=
  forall (p : Z) (n : Z),
    TT &&
    emp **
    ((UIntArray.undef_full p n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.undef_full p n))
    ).

Definition undef_uint_array_strategy17 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((UIntArray.undef_seg p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.undef_seg p x y))
    ).

Definition undef_uint_array_strategy3 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x < y) ”) &&
    emp **
    ((UIntArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((UIntArray.undef_seg p (x + 1) y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_uint (p + (x * sizeof(UINT)))))
    ).

Definition undef_uint_array_strategy4 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UIntArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((UIntArray.undef_missing_i p i x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_uint (p + (i * sizeof(UINT)))))
    ).

Definition undef_uint_array_strategy6 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((UIntArray.undef_seg p x y)) **
    ((UIntArray.undef_seg p y z))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.undef_seg p x z))
    ).

Definition undef_uint_array_strategy7 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((UIntArray.undef_seg p x z))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.undef_seg p x y)) **
    ((UIntArray.undef_seg p y z))
    ).

Definition undef_uint_array_strategy8 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z) (x : Z),
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.undef_seg p x x))
    ).

Definition undef_uint_array_strategy9 :=
  forall (p : Z) (n : Z),
    TT &&
    emp **
    ((UIntArray.undef_full p n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.undef_seg p 0 n))
    ).

Definition undef_uint_array_strategy10 :=
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
      ((UIntArray.undef_full p n))
      ).

Definition undef_uint_array_strategy11 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((UIntArray.undef_seg p x y))
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

Definition undef_uint_array_strategy12 :=
  forall (x1 : Z) (x : Z) (y : Z) (y1 : Z) (p : Z),
    TT &&
    (“ (y1 = y) ”) &&
    (“ (x1 = x) ”) &&
    emp **
    ((UIntArray.undef_seg p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.undef_seg p x1 y1))
    ).

Definition undef_uint_array_strategy15 :=
  forall (n : Z) (p : Z),
    TT &&
    (“ (0 < n) ”) &&
    emp **
    ((UIntArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((UIntArray.undef_seg p 1 n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_uint (p + (0 * sizeof(UINT)))))
    ).

Definition undef_uint_array_strategy2 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UIntArray.undef_missing_i p i 0 n)) **
    ((poly_undef_store FET_uint (p + (i * sizeof(UINT)))))
    |--
    (
    TT &&
    emp **
    ((UIntArray.undef_full p n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition undef_uint_array_strategy5 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UIntArray.undef_missing_i p i x y)) **
    ((poly_undef_store FET_uint (p + (i * sizeof(UINT)))))
    |--
    (
    TT &&
    emp **
    ((UIntArray.undef_seg p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition undef_uint_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UIntArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((UIntArray.undef_missing_i p i 0 n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_uint (p + (i * sizeof(UINT)))))
    ).

Module Type undef_uint_array_Strategy_Correct.

  Axiom undef_uint_array_strategy13_correctness : undef_uint_array_strategy13.
  Axiom undef_uint_array_strategy14_correctness : undef_uint_array_strategy14.
  Axiom undef_uint_array_strategy16_correctness : undef_uint_array_strategy16.
  Axiom undef_uint_array_strategy17_correctness : undef_uint_array_strategy17.
  Axiom undef_uint_array_strategy3_correctness : undef_uint_array_strategy3.
  Axiom undef_uint_array_strategy4_correctness : undef_uint_array_strategy4.
  Axiom undef_uint_array_strategy6_correctness : undef_uint_array_strategy6.
  Axiom undef_uint_array_strategy7_correctness : undef_uint_array_strategy7.
  Axiom undef_uint_array_strategy8_correctness : undef_uint_array_strategy8.
  Axiom undef_uint_array_strategy9_correctness : undef_uint_array_strategy9.
  Axiom undef_uint_array_strategy10_correctness : undef_uint_array_strategy10.
  Axiom undef_uint_array_strategy11_correctness : undef_uint_array_strategy11.
  Axiom undef_uint_array_strategy12_correctness : undef_uint_array_strategy12.
  Axiom undef_uint_array_strategy15_correctness : undef_uint_array_strategy15.
  Axiom undef_uint_array_strategy2_correctness : undef_uint_array_strategy2.
  Axiom undef_uint_array_strategy5_correctness : undef_uint_array_strategy5.
  Axiom undef_uint_array_strategy1_correctness : undef_uint_array_strategy1.

End undef_uint_array_Strategy_Correct.
