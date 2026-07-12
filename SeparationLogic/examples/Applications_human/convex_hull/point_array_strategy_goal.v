Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.convex_hull.convex_hull_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition point_array_strategy20 :=
  forall (i : Z) (p : Z) (a : Point),
    TT &&
    emp **
    ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) a))
    |--
    (
    TT &&
    emp **
    ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) a))
    ) ** (
    ALL (vx : Z) (vy : Z),
      TT &&
      emp **
      ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) ( point_mk vx vy))) -*
      TT &&
      emp **
      ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "x") vx)) **
      ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "y") vy))
      ).

Definition point_array_strategy25 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list Point)) (__default_Point : Point),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((PointArray.missing_i p i 0 n l)) **
    ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) ( point_mk ( point_x (Znth i l __default_Point)) ( point_y (Znth i l __default_Point)))))
    |--
    (
    TT &&
    emp **
    ((PointArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy26 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : (@list Point)) (__default_Point : Point),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((PointArray.missing_i p i x y l)) **
    ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) ( point_mk ( point_x (Znth (Z.sub i x) l __default_Point)) ( point_y (Znth (Z.sub i x) l __default_Point)))))
    |--
    (
    TT &&
    emp **
    ((PointArray.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy19 :=
  forall (vx : Z) (vy : Z) (p : Z) (i : Z),
    TT &&
    emp **
    ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "x") vx)) **
    ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "y") vy))
    |--
    (
    TT &&
    emp **
    ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) ( point_mk vx vy)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list Point)),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((PointArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((PointArray.missing_i p i 0 n l))
    ) ** (
    ALL (v : Point) (__default_Point : Point),
      TT &&
      (“ (v = (Znth i l __default_Point)) ”) &&
      emp -*
      TT &&
      emp **
      ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) v))
      ).

Definition point_array_strategy4 :=
  forall (p : Z) (l1 : (@list Point)) (n : Z),
    TT &&
    emp **
    ((PointArray.full p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Point)),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((PointArray.full p n l2))
      ).

Definition point_array_strategy5 :=
  forall (p : Z) (v : Z) (l : (@list Point)) (n : Z) (i : Z),
    TT &&
    emp **
    ((PointArray.missing_i p i v n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PointArray.missing_i p i v n l))
    ).

Definition point_array_strategy6 :=
  forall (p : Z) (y : Z) (l1 : (@list Point)) (x : Z),
    TT &&
    emp **
    ((PointArray.seg p x y l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Point)),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((PointArray.seg p x y l2))
      ).

Definition point_array_strategy7 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : (@list Point)),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((PointArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((PointArray.missing_i p i x y l))
    ) ** (
    ALL (v : Point) (__default_Point : Point),
      TT &&
      (“ (v = (Znth (Z.sub i x) l __default_Point)) ”) &&
      emp -*
      TT &&
      emp **
      ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) v))
      ).

Definition point_array_strategy8 :=
  forall (x : Z) (y : Z) (z : Z) (l1 : (@list Point)) (p : Z) (l2 : (@list Point)),
    TT &&
    (“ (Z.le y z) ”) &&
    (“ (Z.le x y) ”) &&
    emp **
    ((PointArray.seg p x y l1)) **
    ((PointArray.seg p y z l2))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l3 : (@list Point)),
      TT &&
      (“ (l3 = (@app Point l1 l2)) ”) &&
      emp -*
      TT &&
      emp **
      ((PointArray.seg p x z l3))
      ).

Definition point_array_strategy9 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z) (l3 : (@list Point)),
    TT &&
    (“ (Z.le y z) ”) &&
    (“ (Z.le x y) ”) &&
    emp **
    ((PointArray.seg p x z l3))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Point)) (l2 : (@list Point)),
      TT &&
      (“ (l3 = (@app Point l1 l2)) ”) &&
      (“ ((@Zlength Point l1) = (Z.sub y x)) ”) &&
      emp -*
      TT &&
      emp **
      ((PointArray.seg p x y l1)) **
      ((PointArray.seg p y z l2))
      ).

Definition point_array_strategy10 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Point)) (p : Z) (x : Z),
    TT &&
    (“ (l = (@nil Point)) ”) &&
    emp -*
    TT &&
    emp **
    ((PointArray.seg p x x l))
    ).

Definition point_array_strategy13 :=
  forall (n : Z) (p : Z),
    TT &&
    (“ (Z.lt 0 n) ”) &&
    emp **
    ((PointArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((PointArray.undef_seg p 1 n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( (((Z.add p (Z.mul 0 (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "x"))) **
    ((poly_undef_store FET_int &( (((Z.add p (Z.mul 0 (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "y")))
    ).

Definition point_array_strategy15 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (Z.lt x y) ”) &&
    emp **
    ((PointArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((PointArray.undef_seg p (Z.add x 1) y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( (((Z.add p (Z.mul x (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "x"))) **
    ((poly_undef_store FET_int &( (((Z.add p (Z.mul x (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "y")))
    ).

Definition point_array_strategy29 :=
  forall (p : Z) (a : Point),
    TT &&
    emp **
    ((store_point p a))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (b : Point),
      TT &&
      (“ (a = b) ”) &&
      emp -*
      TT &&
      emp **
      ((store_point p b))
      ).

Definition point_array_strategy27 :=
  forall (p : Z) (a : Point),
    TT &&
    emp **
    ((store_point p a))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "Point" ->ₛ "x") ( point_x a))) **
    ((poly_store FET_int &( ((p)) # "Point" ->ₛ "y") ( point_y a)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy28 :=
  forall (n : Z) (m : Z) (p : Z),
    TT &&
    (“ (n = m) ”) &&
    emp **
    ((PointArray.undef_full p n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PointArray.undef_full p m))
    ).

Definition point_array_strategy2 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list Point)) (__default_Point : Point),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((PointArray.missing_i p i 0 n l)) **
    ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) (Znth i l __default_Point)))
    |--
    (
    TT &&
    emp **
    ((PointArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy11 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : (@list Point)) (__default_Point : Point),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((PointArray.missing_i p i x y l)) **
    ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) (Znth (Z.sub i x) l __default_Point)))
    |--
    (
    TT &&
    emp **
    ((PointArray.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy17 :=
  forall (x : Z) (z : Z) (y : Z) (a : Point) (p : Z),
    TT &&
    (“ (y = (Z.add x 1)) ”) &&
    (“ (Z.lt x z) ”) &&
    emp **
    ((store_point (Z.add p (Z.mul x (@sizeof_front_end_type (FET_alias ("Point"))))) a)) **
    ((PointArray.undef_seg p y z))
    |--
    (
    TT &&
    emp **
    ((PointArray.undef_seg p x z))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy18 :=
  forall (x : Z) (y : Z) (l : (@list Point)) (p : Z) (a : Point),
    TT &&
    (“ (Z.le x y) ”) &&
    emp **
    ((PointArray.seg p x y l)) **
    ((store_point (Z.add p (Z.mul y (@sizeof_front_end_type (FET_alias ("Point"))))) a))
    |--
    (
    TT &&
    emp **
    ((PointArray.seg p x (Z.add y 1) (@app Point l (@cons Point a (@nil Point)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy14 :=
  forall (n : Z) (p : Z),
    TT &&
    (“ (Z.lt 0 n) ”) &&
    emp **
    ((PointArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((poly_undef_store FET_int &( (((Z.add p (Z.mul 0 (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "y"))) **
    ((PointArray.undef_seg p 1 n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( (((Z.add p (Z.mul 0 (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "x")))
    ).

Definition point_array_strategy16 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (Z.lt x y) ”) &&
    emp **
    ((PointArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((poly_undef_store FET_int &( (((Z.add p (Z.mul x (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "y"))) **
    ((PointArray.undef_seg p (Z.add x 1) y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( (((Z.add p (Z.mul x (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "x")))
    ).

Definition point_array_strategy21 :=
  forall (i : Z) (n : Z) (__default_Point : Point) (p : Z) (l : (@list Point)),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((PointArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "y") ( point_y (Znth i l __default_Point)))) **
    ((PointArray.missing_i p i 0 n l))
    ) ** (
    ALL (vx : Z),
      TT &&
      (“ (vx = ( point_x (Znth i l __default_Point))) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "x") vx))
      ).

Definition point_array_strategy22 :=
  forall (i : Z) (n : Z) (__default_Point : Point) (p : Z) (l : (@list Point)),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((PointArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "x") ( point_x (Znth i l __default_Point)))) **
    ((PointArray.missing_i p i 0 n l))
    ) ** (
    ALL (vy : Z),
      TT &&
      (“ (vy = ( point_y (Znth i l __default_Point))) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "y") vy))
      ).

Definition point_array_strategy23 :=
  forall (i : Z) (y : Z) (x : Z) (__default_Point : Point) (p : Z) (l : (@list Point)),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((PointArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "y") ( point_y (Znth (Z.sub i x) l __default_Point)))) **
    ((PointArray.missing_i p i x y l))
    ) ** (
    ALL (vx : Z),
      TT &&
      (“ (vx = ( point_x (Znth (Z.sub i x) l __default_Point))) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "x") vx))
      ).

Definition point_array_strategy24 :=
  forall (i : Z) (y : Z) (x : Z) (__default_Point : Point) (p : Z) (l : (@list Point)),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((PointArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "x") ( point_x (Znth (Z.sub i x) l __default_Point)))) **
    ((PointArray.missing_i p i x y l))
    ) ** (
    ALL (vy : Z),
      TT &&
      (“ (vy = ( point_y (Znth (Z.sub i x) l __default_Point))) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( (((Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))))) # "Point" ->ₛ "y") vy))
      ).

Definition point_array_strategy3 :=
  forall (i : Z) (n : Z) (l : (@list Point)) (p : Z) (v : Point),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((PointArray.missing_i p i 0 n l)) **
    ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) v))
    |--
    (
    TT &&
    emp **
    ((PointArray.full p n (@replace_Znth Point i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy12 :=
  forall (i : Z) (y : Z) (x : Z) (l : (@list Point)) (p : Z) (v : Point),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((PointArray.missing_i p i x y l)) **
    ((store_point (Z.add p (Z.mul i (@sizeof_front_end_type (FET_alias ("Point"))))) v))
    |--
    (
    TT &&
    emp **
    ((PointArray.seg p x y (@replace_Znth Point (Z.sub i x) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type point_array_Strategy_Correct.

  Axiom point_array_strategy20_correctness : point_array_strategy20.
  Axiom point_array_strategy25_correctness : point_array_strategy25.
  Axiom point_array_strategy26_correctness : point_array_strategy26.
  Axiom point_array_strategy19_correctness : point_array_strategy19.
  Axiom point_array_strategy1_correctness : point_array_strategy1.
  Axiom point_array_strategy4_correctness : point_array_strategy4.
  Axiom point_array_strategy5_correctness : point_array_strategy5.
  Axiom point_array_strategy6_correctness : point_array_strategy6.
  Axiom point_array_strategy7_correctness : point_array_strategy7.
  Axiom point_array_strategy8_correctness : point_array_strategy8.
  Axiom point_array_strategy9_correctness : point_array_strategy9.
  Axiom point_array_strategy10_correctness : point_array_strategy10.
  Axiom point_array_strategy13_correctness : point_array_strategy13.
  Axiom point_array_strategy15_correctness : point_array_strategy15.
  Axiom point_array_strategy29_correctness : point_array_strategy29.
  Axiom point_array_strategy27_correctness : point_array_strategy27.
  Axiom point_array_strategy28_correctness : point_array_strategy28.
  Axiom point_array_strategy2_correctness : point_array_strategy2.
  Axiom point_array_strategy11_correctness : point_array_strategy11.
  Axiom point_array_strategy17_correctness : point_array_strategy17.
  Axiom point_array_strategy18_correctness : point_array_strategy18.
  Axiom point_array_strategy14_correctness : point_array_strategy14.
  Axiom point_array_strategy16_correctness : point_array_strategy16.
  Axiom point_array_strategy21_correctness : point_array_strategy21.
  Axiom point_array_strategy22_correctness : point_array_strategy22.
  Axiom point_array_strategy23_correctness : point_array_strategy23.
  Axiom point_array_strategy24_correctness : point_array_strategy24.
  Axiom point_array_strategy3_correctness : point_array_strategy3.
  Axiom point_array_strategy12_correctness : point_array_strategy12.

End point_array_Strategy_Correct.
