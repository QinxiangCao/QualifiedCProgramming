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

Definition array_shape_strategy1 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((UIntArray.full_shape p n))
    |--
    EX (x : Z),
      (
      TT &&
      emp **
      ((UIntArray.missing_i_shape p i 0 n)) **
      ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) x))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) v)) -*
        TT &&
        emp **
        ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) v))
        ).

Definition array_shape_strategy3 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (Z.lt x y) ”) &&
    emp **
    ((UIntArray.seg_shape p x y))
    |--
    EX (v0 : Z),
      (
      TT &&
      emp **
      ((UIntArray.seg_shape p (Z.add x 1) y)) **
      ((poly_store FET_uint (Z.add p (Z.mul x (@sizeof_front_end_type FET_uint))) v0))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_uint (Z.add p (Z.mul x (@sizeof_front_end_type FET_uint))) v)) -*
        TT &&
        emp **
        ((poly_store FET_uint (Z.add p (Z.mul x (@sizeof_front_end_type FET_uint))) v))
        ).

Definition array_shape_strategy6 :=
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

Definition array_shape_strategy7 :=
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

Definition array_shape_strategy8 :=
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

Definition array_shape_strategy9 :=
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

Definition array_shape_strategy10 :=
  forall (y1 : Z) (y : Z) (p : Z) (x : Z),
    TT &&
    (“ (y1 = y) ”) &&
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
    ((UIntArray.seg_shape p x y1))
    ).

Definition array_shape_strategy11 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((IntArray.full_shape p n))
    |--
    EX (x : Z),
      (
      TT &&
      emp **
      ((IntArray.missing_i_shape p i 0 n)) **
      ((poly_store FET_int (Z.add p (Z.mul i (@sizeof_front_end_type FET_int))) x))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_int (Z.add p (Z.mul i (@sizeof_front_end_type FET_int))) v)) -*
        TT &&
        emp **
        ((poly_store FET_int (Z.add p (Z.mul i (@sizeof_front_end_type FET_int))) v))
        ).

Definition array_shape_strategy13 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (Z.lt x y) ”) &&
    emp **
    ((IntArray.seg_shape p x y))
    |--
    EX (v0 : Z),
      (
      TT &&
      emp **
      ((poly_store FET_int (Z.add p (Z.mul x (@sizeof_front_end_type FET_int))) v0)) **
      ((IntArray.seg_shape p (Z.add x 1) y))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_int (Z.add p (Z.mul x (@sizeof_front_end_type FET_int))) v)) -*
        TT &&
        emp **
        ((poly_store FET_int (Z.add p (Z.mul x (@sizeof_front_end_type FET_int))) v))
        ).

Definition array_shape_strategy16 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((IntArray.seg_shape p x y))
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

Definition array_shape_strategy17 :=
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
      ((IntArray.seg_shape p x y))
      ).

Definition array_shape_strategy18 :=
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
      ((IntArray.full_shape p n))
      ).

Definition array_shape_strategy19 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((IntArray.seg_shape p 0 i))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray.full_shape p n))
    ).

Definition array_shape_strategy20 :=
  forall (y1 : Z) (y : Z) (p : Z) (x : Z),
    TT &&
    (“ (y1 = y) ”) &&
    emp **
    ((IntArray.seg_shape p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray.seg_shape p x y1))
    ).

Definition array_shape_strategy2 :=
  forall (i : Z) (n : Z) (v : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((UIntArray.missing_i_shape p i 0 n)) **
    ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) v))
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

Definition array_shape_strategy4 :=
  forall (x : Z) (i : Z) (y : Z) (v : Z) (p : Z),
    TT &&
    (“ (x = (Z.add i 1)) ”) &&
    emp **
    ((UIntArray.seg_shape p x y)) **
    ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) v))
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

Definition array_shape_strategy5 :=
  forall (y : Z) (v : Z) (p : Z) (z : Z),
    TT &&
    emp **
    ((UIntArray.seg_shape p y z)) **
    ((poly_store FET_uint (Z.add p (Z.mul z (@sizeof_front_end_type FET_uint))) v))
    |--
    (
    TT &&
    emp **
    ((UIntArray.seg_shape p y (Z.add z 1)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array_shape_strategy12 :=
  forall (i : Z) (n : Z) (v : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((IntArray.missing_i_shape p i 0 n)) **
    ((poly_store FET_int (Z.add p (Z.mul i (@sizeof_front_end_type FET_int))) v))
    |--
    (
    TT &&
    emp **
    ((IntArray.full_shape p n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array_shape_strategy14 :=
  forall (x : Z) (i : Z) (y : Z) (v : Z) (p : Z),
    TT &&
    (“ (x = (Z.add i 1)) ”) &&
    emp **
    ((IntArray.seg_shape p x y)) **
    ((poly_store FET_int (Z.add p (Z.mul i (@sizeof_front_end_type FET_int))) v))
    |--
    (
    TT &&
    emp **
    ((IntArray.seg_shape p i y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array_shape_strategy15 :=
  forall (y : Z) (v : Z) (p : Z) (z : Z),
    TT &&
    emp **
    ((IntArray.seg_shape p y z)) **
    ((poly_store FET_int (Z.add p (Z.mul z (@sizeof_front_end_type FET_int))) v))
    |--
    (
    TT &&
    emp **
    ((IntArray.seg_shape p y (Z.add z 1)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type array_shape_Strategy_Correct.

  Axiom array_shape_strategy1_correctness : array_shape_strategy1.
  Axiom array_shape_strategy3_correctness : array_shape_strategy3.
  Axiom array_shape_strategy6_correctness : array_shape_strategy6.
  Axiom array_shape_strategy7_correctness : array_shape_strategy7.
  Axiom array_shape_strategy8_correctness : array_shape_strategy8.
  Axiom array_shape_strategy9_correctness : array_shape_strategy9.
  Axiom array_shape_strategy10_correctness : array_shape_strategy10.
  Axiom array_shape_strategy11_correctness : array_shape_strategy11.
  Axiom array_shape_strategy13_correctness : array_shape_strategy13.
  Axiom array_shape_strategy16_correctness : array_shape_strategy16.
  Axiom array_shape_strategy17_correctness : array_shape_strategy17.
  Axiom array_shape_strategy18_correctness : array_shape_strategy18.
  Axiom array_shape_strategy19_correctness : array_shape_strategy19.
  Axiom array_shape_strategy20_correctness : array_shape_strategy20.
  Axiom array_shape_strategy2_correctness : array_shape_strategy2.
  Axiom array_shape_strategy4_correctness : array_shape_strategy4.
  Axiom array_shape_strategy5_correctness : array_shape_strategy5.
  Axiom array_shape_strategy12_correctness : array_shape_strategy12.
  Axiom array_shape_strategy14_correctness : array_shape_strategy14.
  Axiom array_shape_strategy15_correctness : array_shape_strategy15.

End array_shape_Strategy_Correct.
