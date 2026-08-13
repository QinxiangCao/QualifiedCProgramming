Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.mergeablelist.sll_project_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition sll_project_strategy3 :=
  forall (p : Z),
    TT &&
    emp **
    ((sll p (@nil Z)))
    |--
    (
    TT &&
    (“ (p = 0) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_project_strategy4 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z),
    TT &&
    (“ (p = 0) ”) &&
    emp -*
    TT &&
    emp **
    ((sll p (@nil Z)))
    ).

Definition sll_project_strategy5 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((sll 0 l))
    ).

Definition sll_project_strategy6 :=
  forall (l : (@list Z)),
    TT &&
    emp **
    ((sll 0 l))
    |--
    (
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_project_strategy14 :=
  TT &&
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
    ((sllseg p p l))
    ).

Definition sll_project_strategy31 :=
  forall (p : Z),
    TT &&
    emp **
    ((sllb p (@nil Z)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((sllb p (@nil Z)))
    ).

Definition sll_project_strategy20 :=
  TT &&
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
    ((sllbseg p p l))
    ).

Definition sll_project_strategy40 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (x : Z),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    (“ (( map_mult x (@nil Z)) = l) ”) &&
    emp
    ).

Definition sll_project_strategy41 :=
  forall (x : Z) (l : (@list Z)),
    TT &&
    (“ (( map_mult x (@nil Z)) = l) ”) &&
    emp
    |--
    (
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_project_strategy42 :=
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
    ((sllseg p p ( map_mult x l)))
    ).

Definition sll_project_strategy50 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (r : (@list Z)),
    TT &&
    (“ (l = r) ”) &&
    emp -*
    TT &&
    (“ ((@app Z (@nil Z) l) = r) ”) &&
    emp
    ).

Definition sll_project_strategy51 :=
  forall (l : (@list Z)) (r : (@list Z)),
    TT &&
    (“ ((@app Z (@nil Z) l) = r) ”) &&
    emp
    |--
    (
    TT &&
    (“ (l = r) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_project_strategy52 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (r : (@list Z)),
    TT &&
    (“ (l = r) ”) &&
    emp -*
    TT &&
    (“ (l = (@app Z (@nil Z) r)) ”) &&
    emp
    ).

Definition sll_project_strategy60 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l1 : (@list Z)) (l2 : (@list Z)) (x2 : Z) (x1 : Z),
    TT &&
    (“ (x1 = x2) ”) &&
    (“ (l1 = l2) ”) &&
    emp -*
    TT &&
    (“ ((@cons Z x1 l1) = (@cons Z x2 l2)) ”) &&
    emp
    ).

Definition sll_project_strategy61 :=
  forall (l1 : (@list Z)) (x1 : Z) (x2 : Z) (l2 : (@list Z)),
    TT &&
    (“ ((@cons Z x1 l1) = (@cons Z x2 l2)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (x1 = x2) ”) &&
    (“ (l1 = l2) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_project_strategy37 :=
  forall (p : Z) (h : Z) (l : (@list Z)),
    TT &&
    (“ (p <> 0) ”) &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "sllb" ->ₛ "head") h)) **
    ((poly_store FET_ptr &( ((p)) # "sllb" ->ₛ "ptail") 0)) **
    ((sll h l))
    |--
    (
    TT &&
    emp **
    ((sllb_sll p l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_project_strategy7 :=
  forall (p : Z) (l0 : (@list Z)),
    TT &&
    emp **
    ((sll p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((sll p l1))
      ).

Definition sll_project_strategy16 :=
  forall (p : Z) (l0 : (@list Z)) (q : Z),
    TT &&
    emp **
    ((sllseg p q l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((sllseg p q l1))
      ).

Definition sll_project_strategy30 :=
  forall (p : Z) (l0 : (@list Z)),
    TT &&
    emp **
    ((sllb p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((sllb p l1))
      ).

Definition sll_project_strategy22 :=
  forall (p : Z) (l0 : (@list Z)) (q : Z),
    TT &&
    emp **
    ((sllbseg p q l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((sllbseg p q l1))
      ).

Definition sll_project_strategy38 :=
  forall (p : Z) (l0 : (@list Z)),
    TT &&
    emp **
    ((sllb_sll p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((sllb_sll p l1))
      ).

Definition sll_project_strategy72 :=
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

Definition sll_project_strategy73 :=
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

Definition sll_project_strategy74 :=
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

Definition sll_project_strategy75 :=
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

Definition sll_project_strategy76 :=
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

Definition sll_project_strategy77 :=
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

Definition sll_project_strategy78 :=
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

Definition sll_project_strategy80 :=
  forall (n : Z) (m : Z) (p : Z),
    TT &&
    (“ (n = m) ”) &&
    emp **
    ((UIntArray.undef_seg p 0 n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.undef_seg p (@Zlength Z (@nil Z)) m))
    ).

Definition sll_project_strategy85 :=
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

Definition sll_project_strategy86 :=
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

Definition sll_project_strategy87 :=
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

Definition sll_project_strategy90 :=
  forall (p : Z),
    TT &&
    emp **
    ((UIntArray.seg_shape p 0 (@Zlength Z (@nil Z))))
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

Definition sll_project_strategy91 :=
  TT &&
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
    ((UIntArray.seg_shape p 0 (@Zlength Z (@nil Z))))
    ).

Definition sll_project_strategy92 :=
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

Definition sll_project_strategy93 :=
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

Definition sll_project_strategy71 :=
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

Definition sll_project_strategy32 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    emp **
    ((sllb p l))
    |--
    EX (h : Z) (pt : Z),
      (
      TT &&
      (“ (p <> 0) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "sllb" ->ₛ "head") h)) **
      ((poly_store FET_ptr &( ((p)) # "sllb" ->ₛ "ptail") pt)) **
      ((sll h l))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sll_project_strategy35 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    emp **
    ((sllb_sll p l))
    |--
    EX (h : Z),
      (
      TT &&
      (“ (p <> 0) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "sllb" ->ₛ "head") h)) **
      ((poly_store FET_ptr &( ((p)) # "sllb" ->ₛ "ptail") 0)) **
      ((sll h l))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sll_project_strategy36 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z) (h : Z) (l : (@list Z)),
    TT &&
    (“ (p <> 0) ”) &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "sllb" ->ₛ "head") h)) **
    ((poly_store FET_ptr &( ((p)) # "sllb" ->ₛ "ptail") 0)) **
    ((sll h l)) -*
    TT &&
    emp **
    ((sllb_sll p l))
    ).

Definition sll_project_strategy70 :=
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

Module Type sll_project_Strategy_Correct.

  Axiom sll_project_strategy3_correctness : sll_project_strategy3.
  Axiom sll_project_strategy4_correctness : sll_project_strategy4.
  Axiom sll_project_strategy5_correctness : sll_project_strategy5.
  Axiom sll_project_strategy6_correctness : sll_project_strategy6.
  Axiom sll_project_strategy14_correctness : sll_project_strategy14.
  Axiom sll_project_strategy31_correctness : sll_project_strategy31.
  Axiom sll_project_strategy20_correctness : sll_project_strategy20.
  Axiom sll_project_strategy40_correctness : sll_project_strategy40.
  Axiom sll_project_strategy41_correctness : sll_project_strategy41.
  Axiom sll_project_strategy42_correctness : sll_project_strategy42.
  Axiom sll_project_strategy50_correctness : sll_project_strategy50.
  Axiom sll_project_strategy51_correctness : sll_project_strategy51.
  Axiom sll_project_strategy52_correctness : sll_project_strategy52.
  Axiom sll_project_strategy60_correctness : sll_project_strategy60.
  Axiom sll_project_strategy61_correctness : sll_project_strategy61.
  Axiom sll_project_strategy37_correctness : sll_project_strategy37.
  Axiom sll_project_strategy7_correctness : sll_project_strategy7.
  Axiom sll_project_strategy16_correctness : sll_project_strategy16.
  Axiom sll_project_strategy30_correctness : sll_project_strategy30.
  Axiom sll_project_strategy22_correctness : sll_project_strategy22.
  Axiom sll_project_strategy38_correctness : sll_project_strategy38.
  Axiom sll_project_strategy72_correctness : sll_project_strategy72.
  Axiom sll_project_strategy73_correctness : sll_project_strategy73.
  Axiom sll_project_strategy74_correctness : sll_project_strategy74.
  Axiom sll_project_strategy75_correctness : sll_project_strategy75.
  Axiom sll_project_strategy76_correctness : sll_project_strategy76.
  Axiom sll_project_strategy77_correctness : sll_project_strategy77.
  Axiom sll_project_strategy78_correctness : sll_project_strategy78.
  Axiom sll_project_strategy80_correctness : sll_project_strategy80.
  Axiom sll_project_strategy85_correctness : sll_project_strategy85.
  Axiom sll_project_strategy86_correctness : sll_project_strategy86.
  Axiom sll_project_strategy87_correctness : sll_project_strategy87.
  Axiom sll_project_strategy90_correctness : sll_project_strategy90.
  Axiom sll_project_strategy91_correctness : sll_project_strategy91.
  Axiom sll_project_strategy92_correctness : sll_project_strategy92.
  Axiom sll_project_strategy93_correctness : sll_project_strategy93.
  Axiom sll_project_strategy71_correctness : sll_project_strategy71.
  Axiom sll_project_strategy32_correctness : sll_project_strategy32.
  Axiom sll_project_strategy35_correctness : sll_project_strategy35.
  Axiom sll_project_strategy36_correctness : sll_project_strategy36.
  Axiom sll_project_strategy70_correctness : sll_project_strategy70.

End sll_project_Strategy_Correct.
