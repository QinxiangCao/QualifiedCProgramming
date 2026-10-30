From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition uint64_array_strategy101 :=
  forall (l : (@list Z)) (n : Z) (p : Z),
    TT &&
    emp **
    ((UInt64Array.full p n l))
    |--
    (
    TT &&
    (“ ((@Zlength Z l) = n) ”) &&
    emp **
    ((UInt64Array.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_strategy102 :=
  forall (l : (@list Z)) (x : Z) (y : Z) (p : Z),
    TT &&
    emp **
    ((UInt64Array.seg p x y l))
    |--
    (
    TT &&
    (“ ((@Zlength Z l) = (y - x)) ”) &&
    emp **
    ((UInt64Array.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_strategy103 :=
  forall (l : (@list Z)) (x : Z) (y : Z) (p : Z) (i : Z),
    TT &&
    emp **
    ((UInt64Array.missing_i p i x y l))
    |--
    (
    TT &&
    (“ ((@Zlength Z l) = (y - x)) ”) &&
    emp **
    ((UInt64Array.missing_i p i x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UInt64Array.full p n l))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.missing_i p i 0 n l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth i l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) v))
      ).

Definition uint64_array_strategy4 :=
  forall (p : Z) (l1 : (@list Z)) (n : Z),
    TT &&
    emp **
    ((UInt64Array.full p n l1))
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
      ((UInt64Array.full p n l2))
      ).

Definition uint64_array_strategy5 :=
  forall (p : Z) (v : Z) (l : (@list Z)) (n : Z) (i : Z),
    TT &&
    emp **
    ((UInt64Array.missing_i p i v n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.missing_i p i v n l))
    ).

Definition uint64_array_strategy6 :=
  forall (p : Z) (y : Z) (l1 : (@list Z)) (x : Z),
    TT &&
    emp **
    ((UInt64Array.seg p x y l1))
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
      ((UInt64Array.seg p x y l2))
      ).

Definition uint64_array_strategy17 :=
  forall (i : Z) (n : Z) (p : Z) (l1 : (@list Z)),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((UInt64Array.seg p 0 i l1))
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
      ((UInt64Array.full p n l2))
      ).

Definition uint64_array_strategy7 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UInt64Array.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.missing_i p i x y l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (i - x) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) v))
      ).

Definition uint64_array_strategy8 :=
  forall (x : Z) (y : Z) (z : Z) (l1 : (@list Z)) (p : Z) (l2 : (@list Z)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((UInt64Array.seg p x y l1)) **
    ((UInt64Array.seg p y z l2))
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
      ((UInt64Array.seg p x z l3))
      ).

Definition uint64_array_strategy9 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z) (l3 : (@list Z)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((UInt64Array.seg p x z l3))
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
      ((UInt64Array.seg p x y l1)) **
      ((UInt64Array.seg p y z l2))
      ).

Definition uint64_array_strategy10 :=
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
    ((UInt64Array.seg p x x l))
    ).

Definition uint64_array_strategy13 :=
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
      ((UInt64Array.full p n l))
      ).

Definition uint64_array_strategy2 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UInt64Array.missing_i p i 0 n l)) **
    ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) (Znth i l  0)))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_strategy11 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UInt64Array.missing_i p i x y l)) **
    ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) (Znth (i - x) l  0)))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_strategy31 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UInt64Array.missing_i p i 0 n l)) **
    ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) (@Znth Z i l 0)))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_strategy3 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UInt64Array.missing_i p i 0 n l)) **
    ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) v))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.full p n (@replace_Znth Z i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_strategy12 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UInt64Array.missing_i p i x y l)) **
    ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) v))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.seg p x y (@replace_Znth Z (i - x) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_strategy14 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((UInt64Array.full p n l)) **
    ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) v))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.full p (n + 1) (@app Z l (@cons Z v (@nil Z)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_strategy15 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (i = y) ”) &&
    emp **
    ((UInt64Array.seg p x y l)) **
    ((poly_store FET_uint64 (p + (i * sizeof(UINT64))) v))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.seg p x (y + 1) (@app Z l (@cons Z v (@nil Z)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition uint64_array_strategy16 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (0 < i) ”) &&
    emp **
    ((UInt64Array.full (p + (i * sizeof(UINT64))) n l)) **
    ((poly_store FET_uint64 (p + ((i - 1) * sizeof(UINT64))) v))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.full (p + ((i - 1) * sizeof(UINT64))) (n + 1) (@cons Z v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type uint64_array_Strategy_Correct.

  Axiom uint64_array_strategy101_correctness : uint64_array_strategy101.
  Axiom uint64_array_strategy102_correctness : uint64_array_strategy102.
  Axiom uint64_array_strategy103_correctness : uint64_array_strategy103.
  Axiom uint64_array_strategy1_correctness : uint64_array_strategy1.
  Axiom uint64_array_strategy4_correctness : uint64_array_strategy4.
  Axiom uint64_array_strategy5_correctness : uint64_array_strategy5.
  Axiom uint64_array_strategy6_correctness : uint64_array_strategy6.
  Axiom uint64_array_strategy17_correctness : uint64_array_strategy17.
  Axiom uint64_array_strategy7_correctness : uint64_array_strategy7.
  Axiom uint64_array_strategy8_correctness : uint64_array_strategy8.
  Axiom uint64_array_strategy9_correctness : uint64_array_strategy9.
  Axiom uint64_array_strategy10_correctness : uint64_array_strategy10.
  Axiom uint64_array_strategy13_correctness : uint64_array_strategy13.
  Axiom uint64_array_strategy2_correctness : uint64_array_strategy2.
  Axiom uint64_array_strategy11_correctness : uint64_array_strategy11.
  Axiom uint64_array_strategy31_correctness : uint64_array_strategy31.
  Axiom uint64_array_strategy3_correctness : uint64_array_strategy3.
  Axiom uint64_array_strategy12_correctness : uint64_array_strategy12.
  Axiom uint64_array_strategy14_correctness : uint64_array_strategy14.
  Axiom uint64_array_strategy15_correctness : uint64_array_strategy15.
  Axiom uint64_array_strategy16_correctness : uint64_array_strategy16.

End uint64_array_Strategy_Correct.
