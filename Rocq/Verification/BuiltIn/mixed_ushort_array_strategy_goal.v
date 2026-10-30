From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition mixed_ushort_array_strategy101 :=
  forall (l : (@list (@option Z))) (n : Z) (p : Z),
    TT &&
    emp **
    ((UShortArray.mixed_full p n l))
    |--
    (
    TT &&
    (“ ((@Zlength (@option Z) l) = n) ”) &&
    emp **
    ((UShortArray.mixed_full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition mixed_ushort_array_strategy102 :=
  forall (l : (@list (@option Z))) (x : Z) (y : Z) (p : Z),
    TT &&
    emp **
    ((UShortArray.mixed_seg p x y l))
    |--
    (
    TT &&
    (“ ((@Zlength (@option Z) l) = (y - x)) ”) &&
    emp **
    ((UShortArray.mixed_seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition mixed_ushort_array_strategy103 :=
  forall (l : (@list (@option Z))) (x : Z) (y : Z) (p : Z) (i : Z),
    TT &&
    emp **
    ((UShortArray.mixed_missing_i p i x y l))
    |--
    (
    TT &&
    (“ ((@Zlength (@option Z) l) = (y - x)) ”) &&
    emp **
    ((UShortArray.mixed_missing_i p i x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition mixed_ushort_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list (@option Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UShortArray.mixed_full p n l))
    |--
    (
    TT &&
    emp **
    ((UShortArray.mixed_missing_i p i 0 n l))
    ) ** (
    ALL (v : Z) (v1 : Z) (__default_app1_Z : (@option Z)),
      TT &&
      (“ ((Znth i l __default_app1_Z) = (@Some Z v1)) ”) &&
      (“ (v = v1) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ushort (p + (i * sizeof(USHORT))) v))
      ).

Definition mixed_ushort_array_strategy4 :=
  forall (p : Z) (l1 : (@list (@option Z))) (n : Z),
    TT &&
    emp **
    ((UShortArray.mixed_full p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list (@option Z))),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((UShortArray.mixed_full p n l2))
      ).

Definition mixed_ushort_array_strategy5 :=
  forall (p : Z) (v : Z) (l : (@list (@option Z))) (n : Z) (i : Z),
    TT &&
    emp **
    ((UShortArray.mixed_missing_i p i v n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UShortArray.mixed_missing_i p i v n l))
    ).

Definition mixed_ushort_array_strategy6 :=
  forall (p : Z) (y : Z) (l1 : (@list (@option Z))) (x : Z),
    TT &&
    emp **
    ((UShortArray.mixed_seg p x y l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list (@option Z))),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((UShortArray.mixed_seg p x y l2))
      ).

Definition mixed_ushort_array_strategy7 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : (@list (@option Z))),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UShortArray.mixed_seg p x y l))
    |--
    (
    TT &&
    emp **
    ((UShortArray.mixed_missing_i p i x y l))
    ) ** (
    ALL (v : Z) (v1 : Z) (__default_app1_Z : (@option Z)),
      TT &&
      (“ ((@Some Z v1) = (Znth (i - x) l __default_app1_Z)) ”) &&
      (“ (v = v1) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ushort (p + (i * sizeof(USHORT))) v))
      ).

Definition mixed_ushort_array_strategy8 :=
  forall (x : Z) (y : Z) (z : Z) (l1 : (@list (@option Z))) (p : Z) (l2 : (@list (@option Z))),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((UShortArray.mixed_seg p x y l1)) **
    ((UShortArray.mixed_seg p y z l2))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l3 : (@list (@option Z))),
      TT &&
      (“ (l3 = (@app (@option Z) l1 l2)) ”) &&
      emp -*
      TT &&
      emp **
      ((UShortArray.mixed_seg p x z l3))
      ).

Definition mixed_ushort_array_strategy9 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z) (l3 : (@list (@option Z))),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((UShortArray.mixed_seg p x z l3))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@option Z))) (l2 : (@list (@option Z))),
      TT &&
      (“ (l3 = (@app (@option Z) l1 l2)) ”) &&
      (“ ((@Zlength (@option Z) l1) = (y - x)) ”) &&
      emp -*
      TT &&
      emp **
      ((UShortArray.mixed_seg p x y l1)) **
      ((UShortArray.mixed_seg p y z l2))
      ).

Definition mixed_ushort_array_strategy10 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list (@option Z))) (p : Z) (x : Z),
    TT &&
    (“ (l = (@nil (@option Z))) ”) &&
    emp -*
    TT &&
    emp **
    ((UShortArray.mixed_seg p x x l))
    ).

Definition mixed_ushort_array_strategy13 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list (@option Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UShortArray.mixed_full p n l))
    |--
    (
    TT &&
    emp **
    ((UShortArray.mixed_missing_i p i 0 n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_ushort (p + (i * sizeof(USHORT)))))
    ).

Definition mixed_ushort_array_strategy2 :=
  forall (v : Z) (l : (@list (@option Z))) (i : Z) (__default_app1_Z : (@option Z)) (n : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ ((@Some Z v) = (Znth i l __default_app1_Z)) ”) &&
    emp **
    ((UShortArray.mixed_missing_i p i 0 n l)) **
    ((poly_store FET_ushort (p + (i * sizeof(USHORT))) v))
    |--
    (
    TT &&
    emp **
    ((UShortArray.mixed_full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition mixed_ushort_array_strategy11 :=
  forall (v : Z) (l : (@list (@option Z))) (x : Z) (i : Z) (__default_app1_Z : (@option Z)) (y : Z) (p : Z),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    (“ ((@Some Z v) = (Znth (i - x) l __default_app1_Z)) ”) &&
    emp **
    ((UShortArray.mixed_missing_i p i x y l)) **
    ((poly_store FET_ushort (p + (i * sizeof(USHORT))) v))
    |--
    (
    TT &&
    emp **
    ((UShortArray.mixed_seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition mixed_ushort_array_strategy3 :=
  forall (i : Z) (n : Z) (l : (@list (@option Z))) (v : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UShortArray.mixed_missing_i p i 0 n l)) **
    ((poly_store FET_ushort (p + (i * sizeof(USHORT))) v))
    |--
    (
    TT &&
    emp **
    ((UShortArray.mixed_full p n (@replace_Znth (@option Z) i (@Some Z v) l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition mixed_ushort_array_strategy14 :=
  forall (i : Z) (n : Z) (l : (@list (@option Z))) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UShortArray.mixed_missing_i p i 0 n l)) **
    ((poly_undef_store FET_ushort (p + (i * sizeof(USHORT)))))
    |--
    (
    TT &&
    emp **
    ((UShortArray.mixed_full p n (@replace_Znth (@option Z) i (@None Z) l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition mixed_ushort_array_strategy12 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list (@option Z))) (v : Z) (p : Z),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UShortArray.mixed_missing_i p i x y l)) **
    ((poly_store FET_ushort (p + (i * sizeof(USHORT))) v))
    |--
    (
    TT &&
    emp **
    ((UShortArray.mixed_seg p x y (@replace_Znth (@option Z) (i - x) (@Some Z v) l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition mixed_ushort_array_strategy15 :=
  forall (i : Z) (n : Z) (v : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((UShortArray.undef_missing_i p i 0 n)) **
    ((poly_store FET_ushort (p + (i * sizeof(USHORT))) v))
    |--
    (
    TT &&
    emp **
    ((UShortArray.mixed_full p n (@replace_Znth (@option Z) i (@Some Z v) (@repeat_Z (@option Z) (@None Z) n))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition mixed_ushort_array_strategy16 :=
  forall (i : Z) (y : Z) (x : Z) (v : Z) (p : Z),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((UShortArray.undef_missing_i p i x y)) **
    ((poly_store FET_ushort (p + (i * sizeof(USHORT))) v))
    |--
    (
    TT &&
    emp **
    ((UShortArray.mixed_seg p x y (@replace_Znth (@option Z) (i - x) (@Some Z v) (@repeat_Z (@option Z) (@None Z) (y - x)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type mixed_ushort_array_Strategy_Correct.

  Axiom mixed_ushort_array_strategy101_correctness : mixed_ushort_array_strategy101.
  Axiom mixed_ushort_array_strategy102_correctness : mixed_ushort_array_strategy102.
  Axiom mixed_ushort_array_strategy103_correctness : mixed_ushort_array_strategy103.
  Axiom mixed_ushort_array_strategy1_correctness : mixed_ushort_array_strategy1.
  Axiom mixed_ushort_array_strategy4_correctness : mixed_ushort_array_strategy4.
  Axiom mixed_ushort_array_strategy5_correctness : mixed_ushort_array_strategy5.
  Axiom mixed_ushort_array_strategy6_correctness : mixed_ushort_array_strategy6.
  Axiom mixed_ushort_array_strategy7_correctness : mixed_ushort_array_strategy7.
  Axiom mixed_ushort_array_strategy8_correctness : mixed_ushort_array_strategy8.
  Axiom mixed_ushort_array_strategy9_correctness : mixed_ushort_array_strategy9.
  Axiom mixed_ushort_array_strategy10_correctness : mixed_ushort_array_strategy10.
  Axiom mixed_ushort_array_strategy13_correctness : mixed_ushort_array_strategy13.
  Axiom mixed_ushort_array_strategy2_correctness : mixed_ushort_array_strategy2.
  Axiom mixed_ushort_array_strategy11_correctness : mixed_ushort_array_strategy11.
  Axiom mixed_ushort_array_strategy3_correctness : mixed_ushort_array_strategy3.
  Axiom mixed_ushort_array_strategy14_correctness : mixed_ushort_array_strategy14.
  Axiom mixed_ushort_array_strategy12_correctness : mixed_ushort_array_strategy12.
  Axiom mixed_ushort_array_strategy15_correctness : mixed_ushort_array_strategy15.
  Axiom mixed_ushort_array_strategy16_correctness : mixed_ushort_array_strategy16.

End mixed_ushort_array_Strategy_Correct.
