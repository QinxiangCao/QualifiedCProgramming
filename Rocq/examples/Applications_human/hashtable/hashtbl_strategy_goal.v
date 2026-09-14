Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.hashtable.hashtbl_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition hashtbl_strategy0 :=
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

Definition hashtbl_strategy1 :=
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

Definition hashtbl_strategy2 :=
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

Definition hashtbl_strategy3 :=
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

Definition hashtbl_strategy9 :=
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

Definition hashtbl_strategy10 :=
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
    ((poly_store FET_int &( ((p)) # "blist" ->ₛ "val") h)) -*
    TT &&
    emp **
    ((sllseg p p l)) **
    ((poly_store FET_int &( ((p)) # "blist" ->ₛ "val") h))
    ).

Definition hashtbl_strategy11 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (p : Z) (q : Z),
    TT &&
    (“ (p <> 0) ”) &&
    (“ (l = (@nil Z)) ”) &&
    emp **
    ((poly_store FET_ptr p q)) -*
    TT &&
    emp **
    ((sllbseg p p l)) **
    ((poly_store FET_ptr p q))
    ).

Definition hashtbl_strategy12 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL ty (l : (@list Z)) (p : Z),
    TT &&
    (“ (p <> 0) ”) &&
    (“ (l = (@nil Z)) ”) &&
    emp **
    ((poly_undef_store ty p)) -*
    TT &&
    emp **
    ((sllbseg p p l)) **
    ((poly_undef_store ty p))
    ).

Definition hashtbl_strategy13 :=
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

Definition hashtbl_strategy14 :=
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

Definition hashtbl_strategy15 :=
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

Definition hashtbl_strategy22 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (y_up : Z) (x_up : Z) (x : Z),
    TT &&
    (“ (x_up = y_up) ”) &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((dllseg x x x_up y_up l))
    ).

Definition hashtbl_strategy26 :=
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

Definition hashtbl_strategy27 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    (“ (p = 0) ”) &&
    emp **
    ((sll p l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    emp
    ).

Definition hashtbl_strategy16 :=
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
      (“ (p = d) ”) &&
      (“ (l = (@cons Z d l0)) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "blist" ->ₛ "next") q)) **
      ((sll q l0))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition hashtbl_strategy17 :=
  forall (p : Z) (q : Z) (l0 : (@list Z)),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    (“ (&( ((p)) # "blist" ->ₛ "next") <> 0) ”) &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "blist" ->ₛ "next") q)) **
    ((sll q l0))
    |--
    (
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    (“ (&( ((p)) # "blist" ->ₛ "next") <> 0) ”) &&
    emp **
    ((sll p (@cons Z p l0)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition hashtbl_strategy20 :=
  forall (p : Z) (l : (@list Z)) (up : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((dll p up l))
    |--
    EX (down : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons Z p l0)) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "blist" ->ₛ "down") down)) **
      ((poly_store FET_ptr &( ((p)) # "blist" ->ₛ "up") up)) **
      ((dll down p l0))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition hashtbl_strategy21 :=
  forall (p : Z) (l0 : (@list Z)) (up : Z) (down : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "blist" ->ₛ "down") down)) **
    ((poly_store FET_ptr &( ((p)) # "blist" ->ₛ "up") up)) **
    ((dll down p l0))
    |--
    EX (l : (@list Z)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons Z p l0)) ”) &&
      emp **
      ((dll p up l))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition hashtbl_strategy4 :=
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

Definition hashtbl_strategy24 :=
  forall (p : Z) (u1 : Z) (l0 : (@list Z)) (u2 : Z) (q : Z),
    TT &&
    emp **
    ((dllseg p q u1 u2 l0))
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
      ((dllseg p q u1 u2 l1))
      ).

Definition hashtbl_strategy25 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z) (l : (@list Z)),
    TT &&
    emp **
    ((sll p l)) -*
    TT &&
    emp **
    ((sllseg p 0 l))
    ).

Definition hashtbl_strategy18 :=
  forall (p : Z) (q : Z) (l0 : (@list Z)) (r : Z),
    TT &&
    emp **
    ((dllseg p 0 q r l0))
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
      ((dllseg p 0 q r l1))
      ).

Definition hashtbl_strategy7 :=
  forall (p : Z) (x : Z) (l : (@list Z)),
    TT &&
    emp **
    ((sll p (@cons Z x l)))
    |--
    EX (y : Z),
      (
      TT &&
      (“ (p = x) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "blist" ->ₛ "next") y)) **
      ((sll y l))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition hashtbl_strategy8 :=
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
    (“ (p = x) ”) &&
    (“ (&( ((p)) # "blist" ->ₛ "next") <> 0) ”) &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "blist" ->ₛ "next") y)) **
    ((sll y l)) -*
    TT &&
    emp **
    ((sll p (@cons Z x l)))
    ).

Definition hashtbl_strategy23 :=
  forall (x : Z) (y : Z) (l : (@list Z)) (x_up : Z) (y_up : Z),
    TT &&
    (“ (x <> y) ”) &&
    emp **
    ((dllseg x y x_up y_up l))
    |--
    EX (z : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (x <> y) ”) &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((poly_store FET_ptr &( ((x)) # "blist" ->ₛ "down") z)) **
      ((poly_store FET_ptr &( ((x)) # "blist" ->ₛ "up") x_up)) **
      ((dllseg z y x y_up l0))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition hashtbl_strategy5 :=
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
      (“ (p = x) ”) &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((sll p (@cons Z x l0)))
      ) ** (
      ALL (q : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "blist" ->ₛ "val") q) || (poly_store FET_ptr &( ((p)) # "blist" ->ₛ "next") q)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "blist" ->ₛ "val") q) || (poly_store FET_ptr &( ((p)) # "blist" ->ₛ "next") q))
        ).

Definition hashtbl_strategy6 :=
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
    ALL (l : (@list Z)) (l0 : (@list Z)),
      TT &&
      (“ (l = (@cons Z p l0)) ”) &&
      emp **
      ((sll p l)) -*
      TT &&
      emp **
      ((sll p l))
      ).

Module Type hashtbl_Strategy_Correct.

  Axiom hashtbl_strategy0_correctness : hashtbl_strategy0.
  Axiom hashtbl_strategy1_correctness : hashtbl_strategy1.
  Axiom hashtbl_strategy2_correctness : hashtbl_strategy2.
  Axiom hashtbl_strategy3_correctness : hashtbl_strategy3.
  Axiom hashtbl_strategy9_correctness : hashtbl_strategy9.
  Axiom hashtbl_strategy10_correctness : hashtbl_strategy10.
  Axiom hashtbl_strategy11_correctness : hashtbl_strategy11.
  Axiom hashtbl_strategy12_correctness : hashtbl_strategy12.
  Axiom hashtbl_strategy13_correctness : hashtbl_strategy13.
  Axiom hashtbl_strategy14_correctness : hashtbl_strategy14.
  Axiom hashtbl_strategy15_correctness : hashtbl_strategy15.
  Axiom hashtbl_strategy22_correctness : hashtbl_strategy22.
  Axiom hashtbl_strategy26_correctness : hashtbl_strategy26.
  Axiom hashtbl_strategy27_correctness : hashtbl_strategy27.
  Axiom hashtbl_strategy16_correctness : hashtbl_strategy16.
  Axiom hashtbl_strategy17_correctness : hashtbl_strategy17.
  Axiom hashtbl_strategy20_correctness : hashtbl_strategy20.
  Axiom hashtbl_strategy21_correctness : hashtbl_strategy21.
  Axiom hashtbl_strategy4_correctness : hashtbl_strategy4.
  Axiom hashtbl_strategy24_correctness : hashtbl_strategy24.
  Axiom hashtbl_strategy25_correctness : hashtbl_strategy25.
  Axiom hashtbl_strategy18_correctness : hashtbl_strategy18.
  Axiom hashtbl_strategy7_correctness : hashtbl_strategy7.
  Axiom hashtbl_strategy8_correctness : hashtbl_strategy8.
  Axiom hashtbl_strategy23_correctness : hashtbl_strategy23.
  Axiom hashtbl_strategy5_correctness : hashtbl_strategy5.
  Axiom hashtbl_strategy6_correctness : hashtbl_strategy6.

End hashtbl_Strategy_Correct.
