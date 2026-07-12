Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_shape_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition sll_shape_strategy3 :=
  TT &&
  emp **
  ((listrep 0))
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

Definition sll_shape_strategy4 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((listrep 0))
  ).

Definition sll_shape_strategy5 :=
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
    TT &&
    emp -*
    TT &&
    emp **
    ((listrep p))
    ).

Definition sll_shape_strategy14 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z),
    TT &&
    emp **
    ((listrep p)) -*
    TT &&
    emp **
    ((lseg p p)) **
    ((listrep p))
    ).

Definition sll_shape_strategy15 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (q : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q)) -*
    TT &&
    emp **
    ((lseg p p)) **
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q))
    ).

Definition sll_shape_strategy23 :=
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
    ((lseg p p))
    ).

Definition sll_shape_strategy25 :=
  forall (p : Z) (q : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((lseg p q)) **
    ((listrep q))
    |--
    (
    TT &&
    emp **
    ((listrep q))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_shape_strategy6 :=
  forall (p : Z),
    TT &&
    (“ (p = 0) ” || “ (0 = p) ”) &&
    emp **
    ((listrep p))
    |--
    (
    TT &&
    (“ (p = 0) ” || “ (0 = p) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_shape_strategy10 :=
  forall (p : Z) (q : Z),
    TT &&
    emp **
    ((lseg p q))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp **
    ((listrep q)) -*
    TT &&
    emp **
    ((listrep p))
    ).

Definition sll_shape_strategy16 :=
  forall (q : Z) (p : Z) (z : Z),
    TT &&
    (“ (q <> 0) ” || “ (0 <> q) ”) &&
    emp **
    ((lseg p q)) **
    ((poly_store FET_ptr &( ((q)) # "list" ->ₛ "next") z))
    |--
    (
    TT &&
    (“ (q <> 0) ” || “ (0 <> q) ”) &&
    emp
    ) ** (
    ALL (h : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((q)) # "list" ->ₛ "data") h)) -*
      TT &&
      emp **
      ((lseg p z))
      ).

Definition sll_shape_strategy21 :=
  forall (q : Z) (p : Z),
    TT &&
    (“ (q = 0) ”) &&
    emp **
    ((listrep p))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((lseg p q))
    ).

Definition sll_shape_strategy11 :=
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
    ALL (x : Z) (y : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((listrep y)) -*
      TT &&
      emp **
      ((listrep p))
      ).

Definition sll_shape_strategy17 :=
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
    ALL (x : Z) (y : Z) (z : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((lseg y z)) -*
      TT &&
      emp **
      ((lseg p z))
      ).

Definition sll_shape_strategy18 :=
  forall (p : Z) (q : Z),
    TT &&
    emp **
    ((lseg p q))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (z : Z),
      TT &&
      emp **
      ((lseg q z)) -*
      TT &&
      emp **
      ((lseg p z))
      ).

Definition sll_shape_strategy19 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp -*
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((lseg p p))
    ).

Definition sll_shape_strategy20 :=
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
    TT &&
    emp -*
    TT &&
    emp **
    ((lseg p q))
    ).

Definition sll_shape_strategy24 :=
  forall (p : Z) (q : Z),
    TT &&
    (“ (p = 0) ”) &&
    emp **
    ((lseg p q))
    |--
    (
    TT &&
    (“ (q = 0) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_shape_strategy7 :=
  forall (p : Z),
    TT &&
    emp **
    ((listrep p))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((listrep p))
    ).

Definition sll_shape_strategy8 :=
  forall (p : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((listrep p))
    |--
    EX (x : Z) (y : Z),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((listrep y))
      ) ** (
      ALL (q : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q))
        ).

Definition sll_shape_strategy9 :=
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
    ALL (x : Z) (y : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((listrep y)) -*
      TT &&
      emp **
      ((listrep p))
      ).

Definition sll_shape_strategy22 :=
  forall (p : Z) (q : Z),
    TT &&
    (“ (p <> q) ” || “ (q <> p) ”) &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((lseg p q))
    |--
    EX (x : Z) (y : Z),
      (
      TT &&
      (“ (p <> q) ” || “ (q <> p) ”) &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((lseg y q))
      ) ** (
      ALL (v : Z) (n : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") v) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") n)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") v) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") n))
        ).

Module Type sll_shape_Strategy_Correct.

  Axiom sll_shape_strategy3_correctness : sll_shape_strategy3.
  Axiom sll_shape_strategy4_correctness : sll_shape_strategy4.
  Axiom sll_shape_strategy5_correctness : sll_shape_strategy5.
  Axiom sll_shape_strategy14_correctness : sll_shape_strategy14.
  Axiom sll_shape_strategy15_correctness : sll_shape_strategy15.
  Axiom sll_shape_strategy23_correctness : sll_shape_strategy23.
  Axiom sll_shape_strategy25_correctness : sll_shape_strategy25.
  Axiom sll_shape_strategy6_correctness : sll_shape_strategy6.
  Axiom sll_shape_strategy10_correctness : sll_shape_strategy10.
  Axiom sll_shape_strategy16_correctness : sll_shape_strategy16.
  Axiom sll_shape_strategy21_correctness : sll_shape_strategy21.
  Axiom sll_shape_strategy11_correctness : sll_shape_strategy11.
  Axiom sll_shape_strategy17_correctness : sll_shape_strategy17.
  Axiom sll_shape_strategy18_correctness : sll_shape_strategy18.
  Axiom sll_shape_strategy19_correctness : sll_shape_strategy19.
  Axiom sll_shape_strategy20_correctness : sll_shape_strategy20.
  Axiom sll_shape_strategy24_correctness : sll_shape_strategy24.
  Axiom sll_shape_strategy7_correctness : sll_shape_strategy7.
  Axiom sll_shape_strategy8_correctness : sll_shape_strategy8.
  Axiom sll_shape_strategy9_correctness : sll_shape_strategy9.
  Axiom sll_shape_strategy22_correctness : sll_shape_strategy22.

End sll_shape_Strategy_Correct.
