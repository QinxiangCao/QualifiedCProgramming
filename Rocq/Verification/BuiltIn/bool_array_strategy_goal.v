From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition bool_array_strategy101 :=
  forall (l : (@list Z)) (n : Z) (p : Z),
    TT &&
    emp **
    ((BoolArray.full p n l))
    |--
    (
    TT &&
    (“ ((@Zlength Z l) = n) ”) &&
    emp **
    ((BoolArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition bool_array_strategy102 :=
  forall (l : (@list Z)) (x : Z) (y : Z) (p : Z),
    TT &&
    emp **
    ((BoolArray.seg p x y l))
    |--
    (
    TT &&
    (“ ((@Zlength Z l) = (y - x)) ”) &&
    emp **
    ((BoolArray.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition bool_array_strategy103 :=
  forall (l : (@list Z)) (x : Z) (y : Z) (p : Z) (i : Z),
    TT &&
    emp **
    ((BoolArray.missing_i p i x y l))
    |--
    (
    TT &&
    (“ ((@Zlength Z l) = (y - x)) ”) &&
    emp **
    ((BoolArray.missing_i p i x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition bool_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((BoolArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((BoolArray.missing_i p i 0 n l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth i l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_bool (p + (i * sizeof(BOOL))) v))
      ).

Definition bool_array_strategy4 :=
  forall (p : Z) (l1 : (@list Z)) (n : Z),
    TT &&
    emp **
    ((BoolArray.full p n l1))
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
      ((BoolArray.full p n l2))
      ).

Definition bool_array_strategy5 :=
  forall (p : Z) (v : Z) (l : (@list Z)) (n : Z) (i : Z),
    TT &&
    emp **
    ((BoolArray.missing_i p i v n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((BoolArray.missing_i p i v n l))
    ).

Definition bool_array_strategy6 :=
  forall (p : Z) (y : Z) (l1 : (@list Z)) (x : Z),
    TT &&
    emp **
    ((BoolArray.seg p x y l1))
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
      ((BoolArray.seg p x y l2))
      ).

Definition bool_array_strategy17 :=
  forall (i : Z) (n : Z) (p : Z) (l1 : (@list Z)),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((BoolArray.seg p 0 i l1))
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
      ((BoolArray.full p n l2))
      ).

Definition bool_array_strategy7 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((BoolArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((BoolArray.missing_i p i x y l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (i - x) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_bool (p + (i * sizeof(BOOL))) v))
      ).

Definition bool_array_strategy8 :=
  forall (x : Z) (y : Z) (z : Z) (l1 : (@list Z)) (p : Z) (l2 : (@list Z)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((BoolArray.seg p x y l1)) **
    ((BoolArray.seg p y z l2))
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
      ((BoolArray.seg p x z l3))
      ).

Definition bool_array_strategy9 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z) (l3 : (@list Z)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((BoolArray.seg p x z l3))
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
      ((BoolArray.seg p x y l1)) **
      ((BoolArray.seg p y z l2))
      ).

Definition bool_array_strategy10 :=
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
    ((BoolArray.seg p x x l))
    ).

Definition bool_array_strategy13 :=
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
      ((BoolArray.full p n l))
      ).

Definition bool_array_strategy2 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((BoolArray.missing_i p i 0 n l)) **
    ((poly_store FET_bool (p + (i * sizeof(BOOL))) (Znth i l  0)))
    |--
    (
    TT &&
    emp **
    ((BoolArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition bool_array_strategy11 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((BoolArray.missing_i p i x y l)) **
    ((poly_store FET_bool (p + (i * sizeof(BOOL))) (Znth (i - x) l  0)))
    |--
    (
    TT &&
    emp **
    ((BoolArray.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition bool_array_strategy31 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((BoolArray.missing_i p i 0 n l)) **
    ((poly_store FET_bool (p + (i * sizeof(BOOL))) (@Znth Z i l 0)))
    |--
    (
    TT &&
    emp **
    ((BoolArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition bool_array_strategy3 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((BoolArray.missing_i p i 0 n l)) **
    ((poly_store FET_bool (p + (i * sizeof(BOOL))) v))
    |--
    (
    TT &&
    emp **
    ((BoolArray.full p n (@replace_Znth Z i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition bool_array_strategy12 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((BoolArray.missing_i p i x y l)) **
    ((poly_store FET_bool (p + (i * sizeof(BOOL))) v))
    |--
    (
    TT &&
    emp **
    ((BoolArray.seg p x y (@replace_Znth Z (i - x) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition bool_array_strategy14 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((BoolArray.full p n l)) **
    ((poly_store FET_bool (p + (i * sizeof(BOOL))) v))
    |--
    (
    TT &&
    emp **
    ((BoolArray.full p (n + 1) (@app Z l (@cons Z v (@nil Z)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition bool_array_strategy15 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (i = y) ”) &&
    emp **
    ((BoolArray.seg p x y l)) **
    ((poly_store FET_bool (p + (i * sizeof(BOOL))) v))
    |--
    (
    TT &&
    emp **
    ((BoolArray.seg p x (y + 1) (@app Z l (@cons Z v (@nil Z)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition bool_array_strategy16 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (0 < i) ”) &&
    emp **
    ((BoolArray.full (p + (i * sizeof(BOOL))) n l)) **
    ((poly_store FET_bool (p + ((i - 1) * sizeof(BOOL))) v))
    |--
    (
    TT &&
    emp **
    ((BoolArray.full (p + ((i - 1) * sizeof(BOOL))) (n + 1) (@cons Z v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type bool_array_Strategy_Correct.

  Axiom bool_array_strategy101_correctness : bool_array_strategy101.
  Axiom bool_array_strategy102_correctness : bool_array_strategy102.
  Axiom bool_array_strategy103_correctness : bool_array_strategy103.
  Axiom bool_array_strategy1_correctness : bool_array_strategy1.
  Axiom bool_array_strategy4_correctness : bool_array_strategy4.
  Axiom bool_array_strategy5_correctness : bool_array_strategy5.
  Axiom bool_array_strategy6_correctness : bool_array_strategy6.
  Axiom bool_array_strategy17_correctness : bool_array_strategy17.
  Axiom bool_array_strategy7_correctness : bool_array_strategy7.
  Axiom bool_array_strategy8_correctness : bool_array_strategy8.
  Axiom bool_array_strategy9_correctness : bool_array_strategy9.
  Axiom bool_array_strategy10_correctness : bool_array_strategy10.
  Axiom bool_array_strategy13_correctness : bool_array_strategy13.
  Axiom bool_array_strategy2_correctness : bool_array_strategy2.
  Axiom bool_array_strategy11_correctness : bool_array_strategy11.
  Axiom bool_array_strategy31_correctness : bool_array_strategy31.
  Axiom bool_array_strategy3_correctness : bool_array_strategy3.
  Axiom bool_array_strategy12_correctness : bool_array_strategy12.
  Axiom bool_array_strategy14_correctness : bool_array_strategy14.
  Axiom bool_array_strategy15_correctness : bool_array_strategy15.
  Axiom bool_array_strategy16_correctness : bool_array_strategy16.

End bool_array_Strategy_Correct.
