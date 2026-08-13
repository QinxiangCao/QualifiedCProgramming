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

Definition uint_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((UIntArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((UIntArray.missing_i p i 0 n l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth i l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) v))
      ).

Definition uint_array_strategy4 :=
  forall (p : Z) (l1 : (@list Z)) (n : Z),
    TT &&
    emp **
    ((UIntArray.full p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((UIntArray.full p n l2))
      ).

Definition uint_array_strategy5 :=
  forall (p : Z) (v : Z) (l : (@list Z)) (n : Z) (i : Z),
    TT &&
    emp **
    ((UIntArray.missing_i p i v n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.missing_i p i v n l))
    ).

Definition uint_array_strategy6 :=
  forall (p : Z) (y : Z) (l1 : (@list Z)) (x : Z),
    TT &&
    emp **
    ((UIntArray.seg p x y l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((UIntArray.seg p x y l2))
      ).

Definition uint_array_strategy7 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((UIntArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((UIntArray.missing_i p i x y l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (Z.sub i x) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) v))
      ).

Definition uint_array_strategy8 :=
  forall (x : Z) (y : Z) (z : Z) (l1 : (@list Z)) (p : Z) (l2 : (@list Z)),
    TT &&
    (“ (Z.le y z) ”) &&
    (“ (Z.le x y) ”) &&
    emp **
    ((UIntArray.seg p x y l1)) **
    ((UIntArray.seg p y z l2))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l3 : (@list Z)),
      TT &&
      (“ (l3 = (@app Z l1 l2)) ”) &&
      emp -*
      TT &&
      emp **
      ((UIntArray.seg p x z l3))
      ).

Definition uint_array_strategy9 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z) (l3 : (@list Z)),
    TT &&
    (“ (Z.le y z) ”) &&
    (“ (Z.le x y) ”) &&
    emp **
    ((UIntArray.seg p x z l3))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)) (l2 : (@list Z)),
      TT &&
      (“ (l3 = (@app Z l1 l2)) ”) &&
      (“ ((@Zlength Z l1) = (Z.sub y x)) ”) &&
      emp -*
      TT &&
      emp **
      ((UIntArray.seg p x y l1)) **
      ((UIntArray.seg p y z l2))
      ).

Definition uint_array_strategy10 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (p : Z) (x : Z),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((UIntArray.seg p x x l))
    ).

Definition uint_array_strategy13 :=
  forall (n : Z),
    TT &&
    (“ (n = 0) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (l = (@nil Z)) ”) &&
      emp -*
      TT &&
      emp **
      ((UIntArray.full p n l))
      ).

Definition uint_array_strategy14 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (l1 : (@list Z)) (a : Z) (p : Z) (n : Z),
    TT &&
    (“ (l = (@app Z l1 (@cons Z a (@nil Z)))) ”) &&
    emp **
    ((poly_store FET_uint (Z.add p (Z.mul n (@sizeof_front_end_type FET_uint))) a)) **
    ((UIntArray.full p n l1)) -*
    TT &&
    emp **
    ((UIntArray.full p (Z.add n 1) l))
    ).

Definition uint_array_strategy2 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((UIntArray.missing_i p i 0 n l)) **
    ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) (Znth i l  0)))
    |--
    (
    TT &&
    emp **
    ((UIntArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_strategy11 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((UIntArray.missing_i p i x y l)) **
    ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) (Znth (Z.sub i x) l  0)))
    |--
    (
    TT &&
    emp **
    ((UIntArray.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_strategy3 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((UIntArray.missing_i p i 0 n l)) **
    ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) v))
    |--
    (
    TT &&
    emp **
    ((UIntArray.full p n (@replace_Znth Z i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_strategy12 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((UIntArray.missing_i p i x y l)) **
    ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) v))
    |--
    (
    TT &&
    emp **
    ((UIntArray.seg p x y (@replace_Znth Z (Z.sub i x) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type uint_array_Strategy_Correct.

  Axiom uint_array_strategy1_correctness : uint_array_strategy1.
  Axiom uint_array_strategy4_correctness : uint_array_strategy4.
  Axiom uint_array_strategy5_correctness : uint_array_strategy5.
  Axiom uint_array_strategy6_correctness : uint_array_strategy6.
  Axiom uint_array_strategy7_correctness : uint_array_strategy7.
  Axiom uint_array_strategy8_correctness : uint_array_strategy8.
  Axiom uint_array_strategy9_correctness : uint_array_strategy9.
  Axiom uint_array_strategy10_correctness : uint_array_strategy10.
  Axiom uint_array_strategy13_correctness : uint_array_strategy13.
  Axiom uint_array_strategy14_correctness : uint_array_strategy14.
  Axiom uint_array_strategy2_correctness : uint_array_strategy2.
  Axiom uint_array_strategy11_correctness : uint_array_strategy11.
  Axiom uint_array_strategy3_correctness : uint_array_strategy3.
  Axiom uint_array_strategy12_correctness : uint_array_strategy12.

End uint_array_Strategy_Correct.
