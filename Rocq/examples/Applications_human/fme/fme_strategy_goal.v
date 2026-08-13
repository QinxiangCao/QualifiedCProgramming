Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme.fme_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition fme_strategy5 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Constraint)) (n : Z),
    TT &&
    (“ (l = (@nil Constraint)) ”) &&
    emp -*
    TT &&
    emp **
    ((InequList 0 n l))
    ).

Definition fme_strategy6 :=
  forall (p : Z) (l0 : (@list Constraint)) (x0 : Constraint) (n1 : Z),
    TT &&
    emp **
    ((InequList p n1 (@cons Constraint x0 l0)))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Constraint)) (n2 : Z) (x1 : Constraint),
      TT &&
      (“ (n1 = n2) ”) &&
      (“ (x0 = x1) ”) &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((InequList p n2 (@cons Constraint x1 l1)))
      ).

Definition fme_strategy18 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Constraint)) (p : Z) (l0 : (@list Constraint)) (n : Z),
    TT &&
    (“ (l = (@nil Constraint)) ”) &&
    emp **
    ((InequList p n l0)) -*
    TT &&
    emp **
    ((InequList_seg p p n l)) **
    ((InequList p n l0))
    ).

Definition fme_strategy19 :=
  forall (p : Z) (n1 : Z) (l1 : (@list Constraint)) (q : Z),
    TT &&
    emp **
    ((InequList_seg p q n1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Constraint)) (n2 : Z),
      TT &&
      (“ (n1 = n2) ”) &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((InequList_seg p q n2 l2))
      ).

Definition fme_strategy7 :=
  forall (p : Z) (l0 : (@list Constraint)) (n1 : Z),
    TT &&
    emp **
    ((InequList p n1 l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Constraint)) (n2 : Z),
      TT &&
      (“ (n1 = n2) ”) &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((InequList p n2 l1))
      ).

Definition fme_strategy13 :=
  forall (p : Z) (l1 : Constraint) (n1 : Z),
    TT &&
    emp **
    ((coef_array p n1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : Constraint) (n2 : Z),
      TT &&
      (“ (n1 = n2) ”) &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((coef_array p n2 l2))
      ).

Definition fme_strategy15 :=
  forall (p : Z) (n : Z) (i : Z) (l : Constraint),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (p <> 0) ”) &&
    emp **
    ((coef_array p n l))
    |--
    (
    TT &&
    emp **
    ((coef_array_missing_i_rec p i 0 n l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = ( coef_Znth i l 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int (Z.add p (Z.mul i (@sizeof_front_end_type FET_int))) v))
      ).

Definition fme_strategy16 :=
  forall (p : Z) (n : Z) (i : Z) (l : Constraint),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (p <> 0) ”) &&
    emp **
    ((coef_array_missing_i_rec p i 0 n l)) **
    ((poly_store FET_int (Z.add p (Z.mul i (@sizeof_front_end_type FET_int))) ( coef_Znth i l 0)))
    |--
    (
    TT &&
    emp **
    ((coef_array p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition fme_strategy8 :=
  forall (m : Z) (n : Z) (p : Z) (l0 : (@list Constraint)),
    TT &&
    (“ (n = m) ” || “ (m = n) ”) &&
    emp **
    ((InequList p n l0))
    |--
    (
    TT &&
    (“ (n = m) ” || “ (m = n) ”) &&
    emp
    ) ** (
    ALL (l1 : (@list Constraint)),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((InequList p m l1))
      ).

Definition fme_strategy14 :=
  forall (m : Z) (n : Z) (p : Z) (l1 : Constraint),
    TT &&
    (“ (n = m) ” || “ (m = n) ”) &&
    emp **
    ((coef_array p n l1))
    |--
    (
    TT &&
    (“ (n = m) ” || “ (m = n) ”) &&
    emp
    ) ** (
    ALL (l2 : Constraint),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((coef_array p m l2))
      ).

Definition fme_strategy11 :=
  forall (p : Z) (l : (@list Constraint)) (x : Constraint) (n : Z),
    TT &&
    emp **
    ((InequList p n (@cons Constraint x l)))
    |--
    EX (y : Z) (h : Z),
      (
      TT &&
      (“ (h <> 0) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "InequList" ->ₛ "coef") h)) **
      ((coef_array h n x)) **
      ((poly_store FET_ptr &( ((p)) # "InequList" ->ₛ "next") y)) **
      ((InequList y n l))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition fme_strategy12 :=
  forall (p : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp
    |--
    (
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp
    ) ** (
    ALL (h : Z) (x : Constraint) (y : Z) (l : (@list Constraint)) (n : Z),
      TT &&
      (“ (h <> 0) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "InequList" ->ₛ "coef") h)) **
      ((coef_array h n x)) **
      ((poly_store FET_ptr &( ((p)) # "InequList" ->ₛ "next") y)) **
      ((InequList y n l)) -*
      TT &&
      emp **
      ((InequList p n (@cons Constraint x l)))
      ).

Definition fme_strategy17 :=
  forall (p : Z) (n : Z) (i : Z) (l : Constraint) (v : Z),
    TT &&
    (“ (Z.le 1 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (p <> 0) ”) &&
    emp **
    ((coef_array_missing_i_rec p i 0 n l)) **
    ((poly_store FET_int (Z.add p (Z.mul i (@sizeof_front_end_type FET_int))) v))
    |--
    (
    TT &&
    emp **
    ((coef_array p n ( coef_replace_Znth i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition fme_strategy9 :=
  forall (p : Z) (l : (@list Constraint)) (n : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((InequList p n l))
    |--
    EX (x : Constraint) (l0 : (@list Constraint)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons Constraint x l0)) ”) &&
      emp **
      ((InequList p n (@cons Constraint x l0)))
      ) ** (
      ALL (q : Z),
        TT &&
        emp **
        ((poly_store FET_ptr &( ((p)) # "InequList" ->ₛ "coef") q) || (poly_store FET_ptr &( ((p)) # "InequList" ->ₛ "next") q)) -*
        TT &&
        emp **
        ((poly_store FET_ptr &( ((p)) # "InequList" ->ₛ "coef") q) || (poly_store FET_ptr &( ((p)) # "InequList" ->ₛ "next") q))
        ).

Definition fme_strategy10 :=
  forall (p : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp
    |--
    (
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp
    ) ** (
    ALL (l : (@list Constraint)) (x : Constraint) (l0 : (@list Constraint)) (n : Z),
      TT &&
      (“ (l = (@cons Constraint x l0)) ”) &&
      emp **
      ((InequList p n (@cons Constraint x l0))) -*
      TT &&
      emp **
      ((InequList p n l))
      ).

Module Type fme_Strategy_Correct.

  Axiom fme_strategy5_correctness : fme_strategy5.
  Axiom fme_strategy6_correctness : fme_strategy6.
  Axiom fme_strategy18_correctness : fme_strategy18.
  Axiom fme_strategy19_correctness : fme_strategy19.
  Axiom fme_strategy7_correctness : fme_strategy7.
  Axiom fme_strategy13_correctness : fme_strategy13.
  Axiom fme_strategy15_correctness : fme_strategy15.
  Axiom fme_strategy16_correctness : fme_strategy16.
  Axiom fme_strategy8_correctness : fme_strategy8.
  Axiom fme_strategy14_correctness : fme_strategy14.
  Axiom fme_strategy11_correctness : fme_strategy11.
  Axiom fme_strategy12_correctness : fme_strategy12.
  Axiom fme_strategy17_correctness : fme_strategy17.
  Axiom fme_strategy9_correctness : fme_strategy9.
  Axiom fme_strategy10_correctness : fme_strategy10.

End fme_Strategy_Correct.
