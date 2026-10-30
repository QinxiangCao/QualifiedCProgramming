From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.convex_hull_float.convex_hull_float_lib.
Local Open Scope sac.

Definition pointf_array_strategy20 :=
  forall (i : Z) (p : Z) (a : PointF),
    TT &&
    emp **
    ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) a))
    |--
    (
    TT &&
    emp **
    ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) a))
    ) ** (
    ALL (vx : fp32) (vy : fp32),
      TT &&
      emp **
      ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) (pointf_mk vx vy))) -*
      TT &&
      emp **
      ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "x") vx)) **
      ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "y") vy))
      ).

Definition pointf_array_strategy25 :=
  forall (i : Z) (n : Z) (__default_PointF : PointF) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) (pointf_mk (pointf_get_x (Znth i l __default_PointF)) (pointf_get_y (Znth i l __default_PointF))))) **
    ((PointFArray.missing_i p i 0 n l))
    |--
    (
    TT &&
    emp **
    ((PointFArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pointf_array_strategy26 :=
  forall (i : Z) (y : Z) (x : Z) (__default_PointF : PointF) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) (pointf_mk (pointf_get_x (Znth (i - x) l __default_PointF)) (pointf_get_y (Znth (i - x) l __default_PointF))))) **
    ((PointFArray.missing_i p i x y l))
    |--
    (
    TT &&
    emp **
    ((PointFArray.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pointf_array_strategy34 :=
  forall (vx : fp32) (vy : fp32) (p : Z),
    TT &&
    emp **
    ((poly_store FET_float &( ((p)) # "PointF" ->ₛ "x") vx)) **
    ((poly_store FET_float &( ((p)) # "PointF" ->ₛ "y") vy))
    |--
    (
    TT &&
    emp **
    ((store_pointf p (pointf_mk vx vy)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pointf_array_strategy35 :=
  forall (vy : fp32) (vx : fp32) (p : Z),
    TT &&
    emp **
    ((poly_store FET_float &( ((p)) # "PointF" ->ₛ "y") vy)) **
    ((poly_store FET_float &( ((p)) # "PointF" ->ₛ "x") vx))
    |--
    (
    TT &&
    emp **
    ((store_pointf p (pointf_mk vx vy)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pointf_array_strategy19 :=
  forall (vx : fp32) (vy : fp32) (p : Z) (i : Z),
    TT &&
    emp **
    ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "x") vx)) **
    ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "y") vy))
    |--
    (
    TT &&
    emp **
    ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) (pointf_mk vx vy)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pointf_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((PointFArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((PointFArray.missing_i p i 0 n l))
    ) ** (
    ALL (v : PointF) (__default_PointF : PointF),
      TT &&
      (“ (v = (Znth i l __default_PointF)) ”) &&
      emp -*
      TT &&
      emp **
      ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) v))
      ).

Definition pointf_array_strategy4 :=
  forall (p : Z) (l1 : (@list PointF)) (n : Z),
    TT &&
    emp **
    ((PointFArray.full p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list PointF)),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((PointFArray.full p n l2))
      ).

Definition pointf_array_strategy5 :=
  forall (p : Z) (v : Z) (l : (@list PointF)) (n : Z) (i : Z),
    TT &&
    emp **
    ((PointFArray.missing_i p i v n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PointFArray.missing_i p i v n l))
    ).

Definition pointf_array_strategy6 :=
  forall (p : Z) (y : Z) (l1 : (@list PointF)) (x : Z),
    TT &&
    emp **
    ((PointFArray.seg p x y l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list PointF)),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((PointFArray.seg p x y l2))
      ).

Definition pointf_array_strategy7 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((PointFArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((PointFArray.missing_i p i x y l))
    ) ** (
    ALL (v : PointF) (__default_PointF : PointF),
      TT &&
      (“ (v = (Znth (i - x) l __default_PointF)) ”) &&
      emp -*
      TT &&
      emp **
      ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) v))
      ).

Definition pointf_array_strategy8 :=
  forall (x : Z) (y : Z) (z : Z) (l1 : (@list PointF)) (p : Z) (l2 : (@list PointF)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((PointFArray.seg p x y l1)) **
    ((PointFArray.seg p y z l2))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l3 : (@list PointF)),
      TT &&
      (“ (l3 = (@app PointF l1 l2)) ”) &&
      emp -*
      TT &&
      emp **
      ((PointFArray.seg p x z l3))
      ).

Definition pointf_array_strategy9 :=
  forall (x : Z) (y : Z) (z : Z) (p : Z) (l3 : (@list PointF)),
    TT &&
    (“ (y <= z) ”) &&
    (“ (x <= y) ”) &&
    emp **
    ((PointFArray.seg p x z l3))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list PointF)) (l2 : (@list PointF)),
      TT &&
      (“ (l3 = (@app PointF l1 l2)) ”) &&
      (“ ((@Zlength PointF l1) = (y - x)) ”) &&
      emp -*
      TT &&
      emp **
      ((PointFArray.seg p x y l1)) **
      ((PointFArray.seg p y z l2))
      ).

Definition pointf_array_strategy10 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list PointF)) (p : Z) (x : Z),
    TT &&
    (“ (l = (@nil PointF)) ”) &&
    emp -*
    TT &&
    emp **
    ((PointFArray.seg p x x l))
    ).

Definition pointf_array_strategy13 :=
  forall (n : Z) (p : Z),
    TT &&
    (“ (0 < n) ”) &&
    emp **
    ((PointFArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((PointFArray.undef_seg p 1 n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_float &( (((p + (0 * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "x"))) **
    ((poly_undef_store FET_float &( (((p + (0 * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "y")))
    ).

Definition pointf_array_strategy15 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x < y) ”) &&
    emp **
    ((PointFArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((PointFArray.undef_seg p (x + 1) y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_float &( (((p + (x * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "x"))) **
    ((poly_undef_store FET_float &( (((p + (x * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "y")))
    ).

Definition pointf_array_strategy29 :=
  forall (p : Z) (a : PointF),
    TT &&
    emp **
    ((store_pointf p a))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (b : PointF),
      TT &&
      (“ (a = b) ”) &&
      emp -*
      TT &&
      emp **
      ((store_pointf p b))
      ).

Definition pointf_array_strategy28 :=
  forall (n : Z) (m : Z) (p : Z),
    TT &&
    (“ (n = m) ”) &&
    emp **
    ((PointFArray.undef_full p n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PointFArray.undef_full p m))
    ).

Definition pointf_array_strategy2 :=
  forall (i : Z) (n : Z) (__default_PointF : PointF) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) (Znth i l __default_PointF))) **
    ((PointFArray.missing_i p i 0 n l))
    |--
    (
    TT &&
    emp **
    ((PointFArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pointf_array_strategy11 :=
  forall (i : Z) (y : Z) (x : Z) (__default_PointF : PointF) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) (Znth (i - x) l __default_PointF))) **
    ((PointFArray.missing_i p i x y l))
    |--
    (
    TT &&
    emp **
    ((PointFArray.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pointf_array_strategy17 :=
  forall (x : Z) (z : Z) (y : Z) (a : PointF) (p : Z),
    TT &&
    (“ (y = (x + 1)) ”) &&
    (“ (x < z) ”) &&
    emp **
    ((store_pointf (p + (x * (sizeof_front_end_type (FET_alias ("PointF"))))) a)) **
    ((PointFArray.undef_seg p y z))
    |--
    (
    TT &&
    emp **
    ((PointFArray.undef_seg p x z))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pointf_array_strategy18 :=
  forall (x : Z) (y : Z) (l : (@list PointF)) (p : Z) (a : PointF),
    TT &&
    (“ (x <= y) ”) &&
    emp **
    ((PointFArray.seg p x y l)) **
    ((store_pointf (p + (y * (sizeof_front_end_type (FET_alias ("PointF"))))) a))
    |--
    (
    TT &&
    emp **
    ((PointFArray.seg p x (y + 1) (@app PointF l (@cons PointF a (@nil PointF)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pointf_array_strategy14 :=
  forall (n : Z) (p : Z),
    TT &&
    (“ (0 < n) ”) &&
    emp **
    ((PointFArray.undef_full p n))
    |--
    (
    TT &&
    emp **
    ((poly_undef_store FET_float &( (((p + (0 * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "y"))) **
    ((PointFArray.undef_seg p 1 n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_float &( (((p + (0 * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "x")))
    ).

Definition pointf_array_strategy16 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (x < y) ”) &&
    emp **
    ((PointFArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((poly_undef_store FET_float &( (((p + (x * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "y"))) **
    ((PointFArray.undef_seg p (x + 1) y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_float &( (((p + (x * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "x")))
    ).

Definition pointf_array_strategy30 :=
  forall (p : Z) (a : PointF),
    TT &&
    emp **
    ((store_pointf p a))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_float &( ((p)) # "PointF" ->ₛ "y") (pointf_get_y a)))
    ) ** (
    ALL (vx : fp32),
      TT &&
      (“ (vx = (pointf_get_x a)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_float &( ((p)) # "PointF" ->ₛ "x") vx))
      ).

Definition pointf_array_strategy31 :=
  forall (p : Z) (a : PointF),
    TT &&
    emp **
    ((store_pointf p a))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_float &( ((p)) # "PointF" ->ₛ "x") (pointf_get_x a)))
    ) ** (
    ALL (vy : fp32),
      TT &&
      (“ (vy = (pointf_get_y a)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_float &( ((p)) # "PointF" ->ₛ "y") vy))
      ).

Definition pointf_array_strategy21 :=
  forall (i : Z) (n : Z) (__default_PointF : PointF) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((PointFArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "y") (pointf_get_y (Znth i l __default_PointF)))) **
    ((PointFArray.missing_i p i 0 n l))
    ) ** (
    ALL (vx : fp32),
      TT &&
      (“ (vx = (pointf_get_x (Znth i l __default_PointF))) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "x") vx))
      ).

Definition pointf_array_strategy22 :=
  forall (i : Z) (n : Z) (__default_PointF : PointF) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((PointFArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "x") (pointf_get_x (Znth i l __default_PointF)))) **
    ((PointFArray.missing_i p i 0 n l))
    ) ** (
    ALL (vy : fp32),
      TT &&
      (“ (vy = (pointf_get_y (Znth i l __default_PointF))) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "y") vy))
      ).

Definition pointf_array_strategy23 :=
  forall (i : Z) (y : Z) (x : Z) (__default_PointF : PointF) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((PointFArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "y") (pointf_get_y (Znth (i - x) l __default_PointF)))) **
    ((PointFArray.missing_i p i x y l))
    ) ** (
    ALL (vx : fp32),
      TT &&
      (“ (vx = (pointf_get_x (Znth (i - x) l __default_PointF))) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "x") vx))
      ).

Definition pointf_array_strategy24 :=
  forall (i : Z) (y : Z) (x : Z) (__default_PointF : PointF) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((PointFArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "x") (pointf_get_x (Znth (i - x) l __default_PointF)))) **
    ((PointFArray.missing_i p i x y l))
    ) ** (
    ALL (vy : fp32),
      TT &&
      (“ (vy = (pointf_get_y (Znth (i - x) l __default_PointF))) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_float &( (((p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))))) # "PointF" ->ₛ "y") vy))
      ).

Definition pointf_array_strategy3 :=
  forall (i : Z) (n : Z) (v : PointF) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) v)) **
    ((PointFArray.missing_i p i 0 n l))
    |--
    (
    TT &&
    emp **
    ((PointFArray.full p n (@replace_Znth PointF i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pointf_array_strategy12 :=
  forall (i : Z) (y : Z) (x : Z) (v : PointF) (p : Z) (l : (@list PointF)),
    TT &&
    (“ (x <= i) ”) &&
    (“ (i < y) ”) &&
    emp **
    ((store_pointf (p + (i * (sizeof_front_end_type (FET_alias ("PointF"))))) v)) **
    ((PointFArray.missing_i p i x y l))
    |--
    (
    TT &&
    emp **
    ((PointFArray.seg p x y (@replace_Znth PointF (i - x) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type pointf_array_Strategy_Correct.

  Axiom pointf_array_strategy20_correctness : pointf_array_strategy20.
  Axiom pointf_array_strategy25_correctness : pointf_array_strategy25.
  Axiom pointf_array_strategy26_correctness : pointf_array_strategy26.
  Axiom pointf_array_strategy34_correctness : pointf_array_strategy34.
  Axiom pointf_array_strategy35_correctness : pointf_array_strategy35.
  Axiom pointf_array_strategy19_correctness : pointf_array_strategy19.
  Axiom pointf_array_strategy1_correctness : pointf_array_strategy1.
  Axiom pointf_array_strategy4_correctness : pointf_array_strategy4.
  Axiom pointf_array_strategy5_correctness : pointf_array_strategy5.
  Axiom pointf_array_strategy6_correctness : pointf_array_strategy6.
  Axiom pointf_array_strategy7_correctness : pointf_array_strategy7.
  Axiom pointf_array_strategy8_correctness : pointf_array_strategy8.
  Axiom pointf_array_strategy9_correctness : pointf_array_strategy9.
  Axiom pointf_array_strategy10_correctness : pointf_array_strategy10.
  Axiom pointf_array_strategy13_correctness : pointf_array_strategy13.
  Axiom pointf_array_strategy15_correctness : pointf_array_strategy15.
  Axiom pointf_array_strategy29_correctness : pointf_array_strategy29.
  Axiom pointf_array_strategy28_correctness : pointf_array_strategy28.
  Axiom pointf_array_strategy2_correctness : pointf_array_strategy2.
  Axiom pointf_array_strategy11_correctness : pointf_array_strategy11.
  Axiom pointf_array_strategy17_correctness : pointf_array_strategy17.
  Axiom pointf_array_strategy18_correctness : pointf_array_strategy18.
  Axiom pointf_array_strategy14_correctness : pointf_array_strategy14.
  Axiom pointf_array_strategy16_correctness : pointf_array_strategy16.
  Axiom pointf_array_strategy30_correctness : pointf_array_strategy30.
  Axiom pointf_array_strategy31_correctness : pointf_array_strategy31.
  Axiom pointf_array_strategy21_correctness : pointf_array_strategy21.
  Axiom pointf_array_strategy22_correctness : pointf_array_strategy22.
  Axiom pointf_array_strategy23_correctness : pointf_array_strategy23.
  Axiom pointf_array_strategy24_correctness : pointf_array_strategy24.
  Axiom pointf_array_strategy3_correctness : pointf_array_strategy3.
  Axiom pointf_array_strategy12_correctness : pointf_array_strategy12.

End pointf_array_Strategy_Correct.
