Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.dll_shape_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition dll_data_strategy1 :=
  forall (l : (@list Z)) (prev : Z),
    TT &&
    emp **
    ((dlistrep 0 prev l))
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

Definition dll_data_strategy2 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (prev : Z),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((dlistrep 0 prev l))
    ).

Definition dll_data_strategy3 :=
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
    ALL (l : (@list Z)) (prev : Z),
      TT &&
      (“ (l = (@nil Z)) ”) &&
      emp -*
      TT &&
      emp **
      ((dlistrep p prev l))
      ).

Definition dll_data_strategy4 :=
  forall (p : Z) (l : (@list Z)) (prev : Z),
    TT &&
    (“ (p = 0) ” || “ (0 = p) ”) &&
    emp **
    ((dlistrep p prev l))
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

Definition dll_data_strategy12 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l1 : (@list Z)) (r : Z) (q : Z) (x : Z) (p : Z) (l2 : (@list Z)),
    TT &&
    (“ (q = r) ”) &&
    (“ (x = q) ”) &&
    (“ (l1 = (@nil Z)) ”) &&
    emp **
    ((dlistrep p x l2)) -*
    TT &&
    emp **
    ((dllseg p p q r l1)) **
    ((dlistrep p x l2))
    ).

Definition dll_data_strategy7 :=
  forall (q : Z) (x : Z) (p : Z) (l1 : (@list Z)) (r : Z) (s : Z),
    TT &&
    (“ (q = x) ”) &&
    emp **
    ((dllseg p s q r l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (l3 : (@list Z)),
      TT &&
      (“ (l2 = (@app Z l1 l3)) ”) &&
      emp **
      ((dlistrep s r l3)) -*
      TT &&
      emp **
      ((dlistrep p x l2))
      ).

Definition dll_data_strategy13 :=
  forall (s : Z) (n : Z) (m : Z),
    TT &&
    (“ (m = n) ”) &&
    (“ (s <> 0) ”) &&
    emp **
    ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") n))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") n))
    ) ** (
    ALL (l : (@list Z)) (l0 : (@list Z)) (x : Z) (p : Z) (q : Z) (y : Z),
      TT &&
      (“ (l = (@app Z l0 (@cons Z x (@nil Z)))) ”) &&
      emp **
      ((poly_store FET_int &( ((s)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") m)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "prev") y)) **
      ((dllseg p s q y l0)) -*
      TT &&
      emp **
      ((dllseg p m q s l))
      ).

Definition dll_data_strategy14 :=
  forall (m : Z) (p : Z) (l : (@list Z)) (s : Z) (q : Z),
    TT &&
    (“ (m <> p) ”) &&
    emp **
    ((dllseg p m q s l))
    |--
    EX (x : Z) (y : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (l = (@app Z l0 (@cons Z x (@nil Z)))) ”) &&
      (“ (s <> 0) ”) &&
      emp **
      ((poly_store FET_int &( ((s)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") m)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "prev") y)) **
      ((dllseg p s q y l0))
      ) ** (
      ALL (n : Z),
        TT &&
        emp **
        ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "prev") n)) -*
        TT &&
        emp **
        ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "prev") n))
        ).

Definition dll_data_strategy15 :=
  forall (q : Z) (x : Z) (t : Z) (p : Z) (l1 : (@list Z)) (r : Z) (s : Z),
    TT &&
    (“ (p = t) ”) &&
    (“ (q = x) ”) &&
    emp **
    ((dllseg p s q r l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (l3 : (@list Z)),
      TT &&
      (“ (l2 = (@app Z l1 l3)) ”) &&
      emp **
      ((dlistrep s r l3)) -*
      TT &&
      emp **
      ((dlistrep t x l2))
      ).

Definition dll_data_strategy16 :=
  forall (s : Z) (q : Z) (l : (@list Z)) (p : Z) (m : Z),
    TT &&
    (“ (s <> q) ”) &&
    emp **
    ((dllseg p m q s l))
    |--
    EX (x : Z) (y : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (l = (@app Z l0 (@cons Z x (@nil Z)))) ”) &&
      emp **
      ((poly_store FET_int &( ((s)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") m)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "prev") y)) **
      ((dllseg p s q y l0))
      ) ** (
      ALL (n : Z),
        TT &&
        emp **
        ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") n)) -*
        TT &&
        emp **
        ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") n))
        ).

Definition dll_data_strategy8 :=
  forall (p : Z) (l1 : (@list Z)) (x : Z),
    TT &&
    emp **
    ((dlistrep p x l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (y : Z),
      TT &&
      (“ (x = y) ”) &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((dlistrep p y l2))
      ).

Definition dll_data_strategy11 :=
  forall (p : Z) (s : Z) (r : Z) (q : Z),
    TT &&
    (“ (q = r) ”) &&
    (“ (p = s) ”) &&
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
      ((dllseg p s q r l))
      ).

Definition dll_data_strategy5 :=
  forall (p : Z) (l : (@list Z)) (prev : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((dlistrep p prev l))
    |--
    EX (x : Z) (y : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "prev") prev)) **
      ((dlistrep y p l0))
      ) ** (
      ALL (q : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "prev") q)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "prev") q))
        ).

Definition dll_data_strategy6 :=
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
    ALL (l : (@list Z)) (x : Z) (l0 : (@list Z)) (prev : Z) (y : Z),
      TT &&
      (“ (l = (@cons Z x l0)) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "prev") prev)) **
      ((dlistrep y p l0)) -*
      TT &&
      emp **
      ((dlistrep p prev l))
      ).

Module Type dll_data_Strategy_Correct.

  Axiom dll_data_strategy1_correctness : dll_data_strategy1.
  Axiom dll_data_strategy2_correctness : dll_data_strategy2.
  Axiom dll_data_strategy3_correctness : dll_data_strategy3.
  Axiom dll_data_strategy4_correctness : dll_data_strategy4.
  Axiom dll_data_strategy12_correctness : dll_data_strategy12.
  Axiom dll_data_strategy7_correctness : dll_data_strategy7.
  Axiom dll_data_strategy13_correctness : dll_data_strategy13.
  Axiom dll_data_strategy14_correctness : dll_data_strategy14.
  Axiom dll_data_strategy15_correctness : dll_data_strategy15.
  Axiom dll_data_strategy16_correctness : dll_data_strategy16.
  Axiom dll_data_strategy8_correctness : dll_data_strategy8.
  Axiom dll_data_strategy11_correctness : dll_data_strategy11.
  Axiom dll_data_strategy5_correctness : dll_data_strategy5.
  Axiom dll_data_strategy6_correctness : dll_data_strategy6.

End dll_data_Strategy_Correct.
