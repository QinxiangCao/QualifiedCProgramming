Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.poly_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition poly_sll_strategy1 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l : (@list A)) (x : Z),
    TT &&
    emp **
    ((sll storeA x l))
    |--
    (
    TT &&
    (“ (sll_para storeA) ”) &&
    emp **
    ((sll storeA x l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition poly_sll_strategy2 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (y : Z) (l : (@list A)) (x : Z),
    TT &&
    emp **
    ((sllseg storeA x y l))
    |--
    (
    TT &&
    (“ (sll_para storeA) ”) &&
    emp **
    ((sllseg storeA x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition poly_sll_strategy4 :=
  forall (A : Type) (l : (@list A)) (storeA : (Z -> (A -> Assertion))),
    TT &&
    emp **
    ((sll storeA 0 l))
    |--
    (
    TT &&
    (“ (l = (@nil A)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition poly_sll_strategy5 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (l : (@list A)) (storeA : (Z -> (A -> Assertion))),
    TT &&
    (“ (l = (@nil A)) ”) &&
    emp -*
    TT &&
    emp **
    ((sll storeA 0 l))
    ).

Definition poly_sll_strategy16 :=
  forall (A : Type) (p : Z) (x : A) (storeA : (Z -> (A -> Assertion))),
    TT &&
    emp **
    ((storeA p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : A),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((storeA p y))
      ).

Definition poly_sll_strategy17 :=
  forall (A : Type) (l : (@list A)) (storeA : (Z -> (A -> Assertion))) (l0 : (@list A)) (p : Z),
    TT &&
    emp **
    ((sllseg storeA p p l)) **
    ((sll storeA p l0))
    |--
    (
    TT &&
    (“ (l = (@nil A)) ”) &&
    emp **
    ((sll storeA p l0))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition poly_sll_strategy18 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (l : (@list A)) (storeA : (Z -> (A -> Assertion))) (l0 : (@list A)) (p : Z),
    TT &&
    (“ (l = (@nil A)) ”) &&
    emp **
    ((sll storeA p l0)) -*
    TT &&
    emp **
    ((sllseg storeA p p l)) **
    ((sll storeA p l0))
    ).

Definition poly_sll_strategy19 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))),
    TT &&
    (“ (sll_para storeA) ”) &&
    emp
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

Definition poly_sll_strategy7 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l0 : (@list A)) (p : Z),
    TT &&
    emp **
    ((sll storeA p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list A)),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((sll storeA p l1))
      ).

Definition poly_sll_strategy10 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l : (@list A)) (x : A) (p : Z),
    TT &&
    emp **
    ((sll storeA p (@cons A x l)))
    |--
    EX (y : Z) (h : Z),
      (
      TT &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "data") h)) **
      ((storeA h x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((sll storeA y l))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition poly_sll_strategy11 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (p : Z) (h : Z) (x : A) (storeA : (Z -> (A -> Assertion))) (l : (@list A)) (y : Z),
    TT &&
    (“ (p <> 0) ”) &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "data") h)) **
    ((storeA h x)) **
    ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
    ((sll storeA y l)) -*
    TT &&
    emp **
    ((sll storeA p (@cons A x l)))
    ).

Definition poly_sll_strategy12 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (q : Z) (l0 : (@list A)) (p : Z),
    TT &&
    emp **
    ((sllseg storeA p q l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list A)) (l2 : (@list A)),
      TT &&
      (“ (l1 = (@app A l0 l2)) ”) &&
      emp **
      ((sll storeA q l2)) -*
      TT &&
      emp **
      ((sll storeA p l1))
      ).

Definition poly_sll_strategy8 :=
  forall (A : Type) (p : Z) (l : (@list A)) (storeA : (Z -> (A -> Assertion))),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((sll storeA p l))
    |--
    EX (x : A) (l0 : (@list A)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons A x l0)) ”) &&
      emp **
      ((sll storeA p (@cons A x l0)))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition poly_sll_strategy9 :=
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
    ALL (A : Type) (l : (@list A)) (x : A) (l0 : (@list A)) (storeA : (Z -> (A -> Assertion))),
      TT &&
      (“ (l = (@cons A x l0)) ”) &&
      emp **
      ((sll storeA p (@cons A x l0))) -*
      TT &&
      emp **
      ((sll storeA p l))
      ).

Module Type poly_sll_Strategy_Correct.

  Axiom poly_sll_strategy1_correctness : poly_sll_strategy1.
  Axiom poly_sll_strategy2_correctness : poly_sll_strategy2.
  Axiom poly_sll_strategy4_correctness : poly_sll_strategy4.
  Axiom poly_sll_strategy5_correctness : poly_sll_strategy5.
  Axiom poly_sll_strategy16_correctness : poly_sll_strategy16.
  Axiom poly_sll_strategy17_correctness : poly_sll_strategy17.
  Axiom poly_sll_strategy18_correctness : poly_sll_strategy18.
  Axiom poly_sll_strategy19_correctness : poly_sll_strategy19.
  Axiom poly_sll_strategy7_correctness : poly_sll_strategy7.
  Axiom poly_sll_strategy10_correctness : poly_sll_strategy10.
  Axiom poly_sll_strategy11_correctness : poly_sll_strategy11.
  Axiom poly_sll_strategy12_correctness : poly_sll_strategy12.
  Axiom poly_sll_strategy8_correctness : poly_sll_strategy8.
  Axiom poly_sll_strategy9_correctness : poly_sll_strategy9.

End poly_sll_Strategy_Correct.
