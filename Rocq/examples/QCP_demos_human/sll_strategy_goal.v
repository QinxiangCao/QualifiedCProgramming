Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition sll_strategy3 :=
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

Definition sll_strategy4 :=
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

Definition sll_strategy5 :=
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

Definition sll_strategy6 :=
  forall (p : Z) (x0 : Z) (l0 : (@list Z)),
    TT &&
    emp **
    ((sll p (@cons Z x0 l0)))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)) (x1 : Z),
      TT &&
      (“ (x0 = x1) ”) &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((sll p (@cons Z x1 l1)))
      ).

Definition sll_strategy21 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((sll p l))
    |--
    EX (d : Z) (q : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons Z d l0)) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") d)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q)) **
      ((sll q l0))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sll_strategy22 :=
  forall (p : Z) (l0 : (@list Z)) (d : Z) (q : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") d)) **
    ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q)) **
    ((sll q l0))
    |--
    EX (l : (@list Z)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons Z d l0)) ”) &&
      emp **
      ((sll p l))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sll_strategy14 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (p : Z) (l0 : (@list Z)),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp **
    ((sll p l0)) -*
    TT &&
    emp **
    ((sllseg p p l)) **
    ((sll p l0))
    ).

Definition sll_strategy15 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (h : Z) (p : Z),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp **
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") h)) -*
    TT &&
    emp **
    ((sllseg p p l)) **
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") h))
    ).

Definition sll_strategy16 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (q : Z) (p : Z),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp **
    ((poly_store FET_ptr p q)) -*
    TT &&
    emp **
    ((sllbseg p p l)) **
    ((poly_store FET_ptr p q))
    ).

Definition sll_strategy17 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL ty (l : (@list Z)) (p : Z),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp **
    ((poly_undef_store ty p)) -*
    TT &&
    emp **
    ((sllbseg p p l)) **
    ((poly_undef_store ty p))
    ).

Definition sll_strategy18 :=
  forall (l1 : (@list Z)) (p : Z) (v1 : Z) (q : Z),
    TT &&
    emp **
    ((sllbseg p q l1)) **
    ((poly_store FET_ptr q v1))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr q v1))
    ) ** (
    ALL (l2 : (@list Z)) (v2 : Z),
      TT &&
      (“ (l1 = l2) ”) &&
      emp **
      ((poly_store FET_ptr q v2)) -*
      TT &&
      emp **
      ((sllbseg p q l2)) **
      ((poly_store FET_ptr q v2))
      ).

Definition sll_strategy19 :=
  forall ty (l1 : (@list Z)) (p : Z) (q : Z),
    TT &&
    emp **
    ((sllbseg p q l1)) **
    ((poly_undef_store ty q))
    |--
    (
    TT &&
    emp **
    ((poly_undef_store ty q))
    ) ** (
    ALL (l2 : (@list Z)) (r : Z),
      TT &&
      (“ (q = r) ”) &&
      (“ (l1 = l2) ”) &&
      emp **
      ((poly_undef_store ty r)) -*
      TT &&
      emp **
      ((sllbseg p r l2)) **
      ((poly_undef_store ty r))
      ).

Definition sll_strategy20 :=
  forall (p : Z),
    TT &&
    (“ (p = 0) ” || “ (0 = p) ”) &&
    emp
    |--
    (
    TT &&
    (“ (p = 0) ” || “ (0 = p) ”) &&
    emp
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      (“ (l = (@nil Z)) ”) &&
      emp -*
      TT &&
      emp **
      ((sll p l))
      ).

Definition sll_strategy7 :=
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

Definition sll_strategy10 :=
  forall (p : Z) (x : Z) (l : (@list Z)),
    TT &&
    emp **
    ((sll p (@cons Z x l)))
    |--
    EX (y : Z),
      (
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((sll y l))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sll_strategy11 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z) (x : Z) (y : Z) (l : (@list Z)),
    TT &&
    (“ (p <> 0) ”) &&
    emp **
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
    ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
    ((sll y l)) -*
    TT &&
    emp **
    ((sll p (@cons Z x l)))
    ).

Definition sll_strategy8 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((sll p l))
    |--
    EX (x : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((sll p (@cons Z x l0)))
      ) ** (
      ALL (q : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q))
        ).

Definition sll_strategy9 :=
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
    ALL (l : (@list Z)) (x : Z) (l0 : (@list Z)),
      TT &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((sll p (@cons Z x l0))) -*
      TT &&
      emp **
      ((sll p l))
      ).

Module Type sll_Strategy_Correct.

  Axiom sll_strategy3_correctness : sll_strategy3.
  Axiom sll_strategy4_correctness : sll_strategy4.
  Axiom sll_strategy5_correctness : sll_strategy5.
  Axiom sll_strategy6_correctness : sll_strategy6.
  Axiom sll_strategy21_correctness : sll_strategy21.
  Axiom sll_strategy22_correctness : sll_strategy22.
  Axiom sll_strategy14_correctness : sll_strategy14.
  Axiom sll_strategy15_correctness : sll_strategy15.
  Axiom sll_strategy16_correctness : sll_strategy16.
  Axiom sll_strategy17_correctness : sll_strategy17.
  Axiom sll_strategy18_correctness : sll_strategy18.
  Axiom sll_strategy19_correctness : sll_strategy19.
  Axiom sll_strategy20_correctness : sll_strategy20.
  Axiom sll_strategy7_correctness : sll_strategy7.
  Axiom sll_strategy10_correctness : sll_strategy10.
  Axiom sll_strategy11_correctness : sll_strategy11.
  Axiom sll_strategy8_correctness : sll_strategy8.
  Axiom sll_strategy9_correctness : sll_strategy9.

End sll_Strategy_Correct.
