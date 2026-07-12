Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition sll_data_strategy3 :=
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

Definition sll_data_strategy4 :=
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

Definition sll_data_strategy5 :=
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

Definition sll_data_strategy14 :=
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

Definition sll_data_strategy15 :=
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
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q)) -*
    TT &&
    emp **
    ((sllseg p p l)) **
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q))
    ).

Definition sll_data_strategy25 :=
  forall (p : Z) (q : Z) (l2 : (@list Z)) (l1 : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((sllseg p q l1)) **
    ((sll q l2))
    |--
    EX (l3 : (@list Z)),
      (
      TT &&
      (“ (l3 = (@app Z l1 l2)) ”) &&
      emp **
      ((sll q l3))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sll_data_strategy23 :=
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

Definition sll_data_strategy6 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    (“ (p = 0) ” || “ (0 = p) ”) &&
    emp **
    ((sll p l))
    |--
    (
    TT &&
    (“ (p = 0) ” || “ (0 = p) ”) &&
    (“ (l = (@nil Z)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_data_strategy10 :=
  forall (p : Z) (l1 : (@list Z)) (q : Z),
    TT &&
    emp **
    ((sllseg p q l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (l3 : (@list Z)),
      TT &&
      (“ (l2 = (@app Z l1 l3)) ”) &&
      emp **
      ((sll q l3)) -*
      TT &&
      emp **
      ((sll p l2))
      ).

Definition sll_data_strategy16 :=
  forall (q : Z) (l1 : (@list Z)) (p : Z) (z : Z),
    TT &&
    (“ (q <> 0) ” || “ (0 <> q) ”) &&
    emp **
    ((sllseg p q l1)) **
    ((poly_store FET_ptr &( ((q)) # "list" ->ₛ "next") z))
    |--
    (
    TT &&
    (“ (q <> 0) ” || “ (0 <> q) ”) &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (h : Z),
      TT &&
      (“ (l2 = (@app Z l1 (@cons Z h (@nil Z)))) ”) &&
      emp **
      ((poly_store FET_int &( ((q)) # "list" ->ₛ "data") h)) -*
      TT &&
      emp **
      ((sllseg p z l2))
      ).

Definition sll_data_strategy21 :=
  forall (q : Z) (p : Z) (l1 : (@list Z)),
    TT &&
    (“ (q = 0) ”) &&
    emp **
    ((sll p l1))
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
      ((sllseg p q l2))
      ).

Definition sll_data_strategy11 :=
  forall (p : Z) (q : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q))
    |--
    (
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q))
    ) ** (
    ALL (l : (@list Z)) (x : Z) (l0 : (@list Z)) (y : Z),
      TT &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((sll y l0)) -*
      TT &&
      emp **
      ((sll p l))
      ).

Definition sll_data_strategy17 :=
  forall (p : Z) (q : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q))
    |--
    (
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q))
    ) ** (
    ALL (l : (@list Z)) (x : Z) (l0 : (@list Z)) (y : Z) (z : Z),
      TT &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((sllseg y z l0)) -*
      TT &&
      emp **
      ((sllseg p z l))
      ).

Definition sll_data_strategy18 :=
  forall (p : Z) (l1 : (@list Z)) (q : Z),
    TT &&
    emp **
    ((sllseg p q l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (l3 : (@list Z)) (z : Z),
      TT &&
      (“ (l2 = (@app Z l1 l3)) ”) &&
      emp **
      ((sllseg q z l3)) -*
      TT &&
      emp **
      ((sllseg p z l2))
      ).

Definition sll_data_strategy19 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (p : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((sllseg p p l))
    ).

Definition sll_data_strategy20 :=
  forall (q : Z) (p : Z),
    TT &&
    (“ (p = 0) ”) &&
    (“ (q = 0) ”) &&
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
      ((sllseg p q l))
      ).

Definition sll_data_strategy24 :=
  forall (p : Z) (q : Z) (l : (@list Z)),
    TT &&
    (“ (p = 0) ”) &&
    emp **
    ((sllseg p q l))
    |--
    (
    TT &&
    (“ (q = 0) ”) &&
    (“ (l = (@nil Z)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_data_strategy7 :=
  forall (p : Z) (l1 : (@list Z)),
    TT &&
    emp **
    ((sll p l1))
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
      ((sll p l2))
      ).

Definition sll_data_strategy8 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((sll p l))
    |--
    EX (x : Z) (y : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((sll y l0))
      ) ** (
      ALL (q : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q))
        ).

Definition sll_data_strategy9 :=
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
    ALL (l : (@list Z)) (x : Z) (l0 : (@list Z)) (y : Z),
      TT &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((sll y l0)) -*
      TT &&
      emp **
      ((sll p l))
      ).

Definition sll_data_strategy22 :=
  forall (p : Z) (l : (@list Z)) (q : Z),
    TT &&
    (“ (p <> q) ” || “ (q <> p) ”) &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((sllseg p q l))
    |--
    EX (x : Z) (y : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (p <> q) ” || “ (q <> p) ”) &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((sllseg y q l0))
      ) ** (
      ALL (v : Z) (n : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") v) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") n)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") v) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") n))
        ).

Module Type sll_data_Strategy_Correct.

  Axiom sll_data_strategy3_correctness : sll_data_strategy3.
  Axiom sll_data_strategy4_correctness : sll_data_strategy4.
  Axiom sll_data_strategy5_correctness : sll_data_strategy5.
  Axiom sll_data_strategy14_correctness : sll_data_strategy14.
  Axiom sll_data_strategy15_correctness : sll_data_strategy15.
  Axiom sll_data_strategy25_correctness : sll_data_strategy25.
  Axiom sll_data_strategy23_correctness : sll_data_strategy23.
  Axiom sll_data_strategy6_correctness : sll_data_strategy6.
  Axiom sll_data_strategy10_correctness : sll_data_strategy10.
  Axiom sll_data_strategy16_correctness : sll_data_strategy16.
  Axiom sll_data_strategy21_correctness : sll_data_strategy21.
  Axiom sll_data_strategy11_correctness : sll_data_strategy11.
  Axiom sll_data_strategy17_correctness : sll_data_strategy17.
  Axiom sll_data_strategy18_correctness : sll_data_strategy18.
  Axiom sll_data_strategy19_correctness : sll_data_strategy19.
  Axiom sll_data_strategy20_correctness : sll_data_strategy20.
  Axiom sll_data_strategy24_correctness : sll_data_strategy24.
  Axiom sll_data_strategy7_correctness : sll_data_strategy7.
  Axiom sll_data_strategy8_correctness : sll_data_strategy8.
  Axiom sll_data_strategy9_correctness : sll_data_strategy9.
  Axiom sll_data_strategy22_correctness : sll_data_strategy22.

End sll_data_Strategy_Correct.
