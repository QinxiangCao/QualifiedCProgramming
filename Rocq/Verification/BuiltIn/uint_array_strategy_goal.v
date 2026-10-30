From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition uint_array_strategy101 :=
  forall (l : (@list Z)) (n : Z) (p : Z),
    TT &&
    emp **
    ((UIntArray.full p n l))
    |--
    (
    TT &&
    (“ ((@Zlength Z l) = n) ”) &&
    emp **
    ((UIntArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_strategy102 :=
  forall (l : (@list Z)) (x : Z) (y : Z) (p : Z),
    TT &&
    emp **
    ((UIntArray.seg p x y l))
    |--
    (
    TT &&
    (“ ((@Zlength Z l) = (y - x)) ”) &&
    emp **
    ((UIntArray.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_strategy103 :=
  forall (l : (@list Z)) (x : Z) (y : Z) (p : Z) (i : Z),
    TT &&
    emp **
    ((UIntArray.missing_i p i x y l))
    |--
    (
    TT &&
    (“ ((@Zlength Z l) = (y - x)) ”) &&
    emp **
    ((UIntArray.missing_i p i x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
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
      ((poly_store FET_uint (p + (i * sizeof(UINT))) v))
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

Definition uint_array_strategy17 :=
  forall (i : Z) (n : Z) (p : Z) (l1 : (@list Z)),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((UIntArray.seg p 0 i l1))
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

Definition uint_array_strategy7 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
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
      (“ (v = (Znth (i - x) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint (p + (i * sizeof(UINT))) v))
      ).

Definition uint_array_strategy8 :=
  forall (x : Z) (y : Z) (z : Z) (l1 : (@list Z)) (p : Z) (l2 : (@list Z)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
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
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
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
      (“ ((@Zlength Z l1) = (y - x)) ”) &&
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

Definition uint_array_strategy2 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UIntArray.missing_i p i 0 n l)) **
    ((poly_store FET_uint (p + (i * sizeof(UINT))) (Znth i l  0)))
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
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UIntArray.missing_i p i x y l)) **
    ((poly_store FET_uint (p + (i * sizeof(UINT))) (Znth (i - x) l  0)))
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

Definition uint_array_strategy31 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UIntArray.missing_i p i 0 n l)) **
    ((poly_store FET_uint (p + (i * sizeof(UINT))) (@Znth Z i l 0)))
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

Definition uint_array_strategy3 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UIntArray.missing_i p i 0 n l)) **
    ((poly_store FET_uint (p + (i * sizeof(UINT))) v))
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
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UIntArray.missing_i p i x y l)) **
    ((poly_store FET_uint (p + (i * sizeof(UINT))) v))
    |--
    (
    TT &&
    emp **
    ((UIntArray.seg p x y (@replace_Znth Z (i - x) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_strategy14 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((UIntArray.full p n l)) **
    ((poly_store FET_uint (p + (i * sizeof(UINT))) v))
    |--
    (
    TT &&
    emp **
    ((UIntArray.full p (n + 1) (@app Z l (@cons Z v (@nil Z)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_strategy15 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (i = y) ”) &&
    emp **
    ((UIntArray.seg p x y l)) **
    ((poly_store FET_uint (p + (i * sizeof(UINT))) v))
    |--
    (
    TT &&
    emp **
    ((UIntArray.seg p x (y + 1) (@app Z l (@cons Z v (@nil Z)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint_array_strategy16 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (0 < i) ”) &&
    emp **
    ((UIntArray.full (p + (i * sizeof(UINT))) n l)) **
    ((poly_store FET_uint (p + ((i - 1) * sizeof(UINT))) v))
    |--
    (
    TT &&
    emp **
    ((UIntArray.full (p + ((i - 1) * sizeof(UINT))) (n + 1) (@cons Z v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type uint_array_Strategy_Correct.

  Axiom uint_array_strategy101_correctness : uint_array_strategy101.
  Axiom uint_array_strategy102_correctness : uint_array_strategy102.
  Axiom uint_array_strategy103_correctness : uint_array_strategy103.
  Axiom uint_array_strategy1_correctness : uint_array_strategy1.
  Axiom uint_array_strategy4_correctness : uint_array_strategy4.
  Axiom uint_array_strategy5_correctness : uint_array_strategy5.
  Axiom uint_array_strategy6_correctness : uint_array_strategy6.
  Axiom uint_array_strategy17_correctness : uint_array_strategy17.
  Axiom uint_array_strategy7_correctness : uint_array_strategy7.
  Axiom uint_array_strategy8_correctness : uint_array_strategy8.
  Axiom uint_array_strategy9_correctness : uint_array_strategy9.
  Axiom uint_array_strategy10_correctness : uint_array_strategy10.
  Axiom uint_array_strategy13_correctness : uint_array_strategy13.
  Axiom uint_array_strategy2_correctness : uint_array_strategy2.
  Axiom uint_array_strategy11_correctness : uint_array_strategy11.
  Axiom uint_array_strategy31_correctness : uint_array_strategy31.
  Axiom uint_array_strategy3_correctness : uint_array_strategy3.
  Axiom uint_array_strategy12_correctness : uint_array_strategy12.
  Axiom uint_array_strategy14_correctness : uint_array_strategy14.
  Axiom uint_array_strategy15_correctness : uint_array_strategy15.
  Axiom uint_array_strategy16_correctness : uint_array_strategy16.

End uint_array_Strategy_Correct.
