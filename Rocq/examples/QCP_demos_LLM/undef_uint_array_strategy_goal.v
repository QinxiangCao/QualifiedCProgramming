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

Definition undef_uint_array_strategy3 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (Z.lt x y) ”) &&
    emp **
    ((UIntArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((UIntArray.undef_seg p (Z.add x 1) y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_uint (Z.add p (Z.mul x (@sizeof_front_end_type FET_uint)))))
    ).

Definition undef_uint_array_strategy4 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z),
    TT &&
    (“ (Z.le y z) ”) &&
    (“ (Z.le x y) ”) &&
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

Definition undef_uint_array_strategy5 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z),
    TT &&
    (“ (Z.le y z) ”) &&
    (“ (Z.le x y) ”) &&
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

Definition undef_uint_array_strategy6 :=
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

Definition undef_uint_array_strategy7 :=
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

Definition undef_uint_array_strategy8 :=
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

Definition undef_uint_array_strategy9 :=
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

Definition undef_uint_array_strategy10 :=
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

Definition undef_uint_array_strategy13 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (Z.lt x y) ”) &&
    emp **
    ((IntArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((IntArray.undef_seg p (Z.add x 1) y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int (Z.add p (Z.mul x (@sizeof_front_end_type FET_int)))))
    ).

Definition undef_uint_array_strategy14 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z),
    TT &&
    (“ (Z.le y z) ”) &&
    (“ (Z.le x y) ”) &&
    emp **
    ((IntArray.undef_seg p x y)) **
    ((IntArray.undef_seg p y z))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray.undef_seg p x z))
    ).

Definition undef_uint_array_strategy15 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z),
    TT &&
    (“ (Z.le y z) ”) &&
    (“ (Z.le x y) ”) &&
    emp **
    ((IntArray.undef_seg p x z))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray.undef_seg p x y)) **
    ((IntArray.undef_seg p y z))
    ).

Definition undef_uint_array_strategy16 :=
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
    ((IntArray.undef_seg p x x))
    ).

Definition undef_uint_array_strategy17 :=
  forall (p : Z) (n : Z),
    TT &&
    emp **
    ((IntArray.undef_full p n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray.undef_seg p 0 n))
    ).

Definition undef_uint_array_strategy18 :=
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
      ((IntArray.undef_full p n))
      ).

Definition undef_uint_array_strategy19 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((IntArray.undef_seg p x y))
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

Definition undef_uint_array_strategy20 :=
  forall (x1 : Z) (x : Z) (y : Z) (y1 : Z) (p : Z),
    TT &&
    (“ (y1 = y) ”) &&
    (“ (x1 = x) ”) &&
    emp **
    ((IntArray.undef_seg p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray.undef_seg p x1 y1))
    ).

Definition undef_uint_array_strategy21 :=
  forall (n : Z) (p : Z),
    TT &&
    (“ (Z.lt 0 n) ”) &&
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
    ((poly_undef_store FET_uint (Z.add p (Z.mul 0 (@sizeof_front_end_type FET_uint)))))
    ).

Definition undef_uint_array_strategy22 :=
  forall (n : Z) (p : Z),
    TT &&
    (“ (Z.lt 0 n) ”) &&
    emp **
    ((IntArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((IntArray.undef_seg p 1 n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int (Z.add p (Z.mul 0 (@sizeof_front_end_type FET_int)))))
    ).

Definition undef_uint_array_strategy2 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((UIntArray.undef_missing_i p i 0 n)) **
    ((poly_undef_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint)))))
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

Definition undef_uint_array_strategy12 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((IntArray.undef_missing_i p i 0 n)) **
    ((poly_undef_store FET_int (Z.add p (Z.mul i (@sizeof_front_end_type FET_int)))))
    |--
    (
    TT &&
    emp **
    ((IntArray.undef_full p n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition undef_uint_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
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
    ((poly_undef_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint)))))
    ).

Definition undef_uint_array_strategy11 :=
  forall (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((IntArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((IntArray.undef_missing_i p i 0 n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int (Z.add p (Z.mul i (@sizeof_front_end_type FET_int)))))
    ).

Module Type undef_uint_array_Strategy_Correct.

  Axiom undef_uint_array_strategy3_correctness : undef_uint_array_strategy3.
  Axiom undef_uint_array_strategy4_correctness : undef_uint_array_strategy4.
  Axiom undef_uint_array_strategy5_correctness : undef_uint_array_strategy5.
  Axiom undef_uint_array_strategy6_correctness : undef_uint_array_strategy6.
  Axiom undef_uint_array_strategy7_correctness : undef_uint_array_strategy7.
  Axiom undef_uint_array_strategy8_correctness : undef_uint_array_strategy8.
  Axiom undef_uint_array_strategy9_correctness : undef_uint_array_strategy9.
  Axiom undef_uint_array_strategy10_correctness : undef_uint_array_strategy10.
  Axiom undef_uint_array_strategy13_correctness : undef_uint_array_strategy13.
  Axiom undef_uint_array_strategy14_correctness : undef_uint_array_strategy14.
  Axiom undef_uint_array_strategy15_correctness : undef_uint_array_strategy15.
  Axiom undef_uint_array_strategy16_correctness : undef_uint_array_strategy16.
  Axiom undef_uint_array_strategy17_correctness : undef_uint_array_strategy17.
  Axiom undef_uint_array_strategy18_correctness : undef_uint_array_strategy18.
  Axiom undef_uint_array_strategy19_correctness : undef_uint_array_strategy19.
  Axiom undef_uint_array_strategy20_correctness : undef_uint_array_strategy20.
  Axiom undef_uint_array_strategy21_correctness : undef_uint_array_strategy21.
  Axiom undef_uint_array_strategy22_correctness : undef_uint_array_strategy22.
  Axiom undef_uint_array_strategy2_correctness : undef_uint_array_strategy2.
  Axiom undef_uint_array_strategy12_correctness : undef_uint_array_strategy12.
  Axiom undef_uint_array_strategy1_correctness : undef_uint_array_strategy1.
  Axiom undef_uint_array_strategy11_correctness : undef_uint_array_strategy11.

End undef_uint_array_Strategy_Correct.
