Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.dll_shape_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition dll_shape_strategy1 :=
  forall (x : Z),
    TT &&
    emp **
    ((dlistrep_shape 0 x))
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

Definition dll_shape_strategy2 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (x : Z),
    TT &&
    emp -*
    TT &&
    emp **
    ((dlistrep_shape 0 x))
    ).

Definition dll_shape_strategy3 :=
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
    ALL (x : Z),
      TT &&
      emp -*
      TT &&
      emp **
      ((dlistrep_shape p x))
      ).

Definition dll_shape_strategy4 :=
  forall (p : Z) (x : Z),
    TT &&
    (“ (p = 0) ” || “ (0 = p) ”) &&
    emp **
    ((dlistrep_shape p x))
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

Definition dll_shape_strategy12 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (x : Z) (q : Z) (r : Z) (p : Z),
    TT &&
    (“ (q = r) ”) &&
    (“ (x = q) ”) &&
    emp **
    ((dlistrep_shape p x)) -*
    TT &&
    emp **
    ((dllseg_shape p q r p)) **
    ((dlistrep_shape p x))
    ).

Definition dll_shape_strategy7 :=
  forall (q : Z) (x : Z) (p : Z) (r : Z) (s : Z),
    TT &&
    (“ (q = x) ”) &&
    emp **
    ((dllseg_shape p q r s))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp **
    ((dlistrep_shape s r)) -*
    TT &&
    emp **
    ((dlistrep_shape p x))
    ).

Definition dll_shape_strategy13 :=
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
    ALL (x : Z) (p : Z) (y : Z) (q : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") m)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "prev") y)) **
      ((dllseg_shape p q y s)) -*
      TT &&
      emp **
      ((dllseg_shape p q s m))
      ).

Definition dll_shape_strategy14 :=
  forall (m : Z) (p : Z) (s : Z) (q : Z),
    TT &&
    (“ (m <> p) ”) &&
    emp **
    ((dllseg_shape p q s m))
    |--
    EX (x : Z) (y : Z),
      (
      TT &&
      (“ (s <> 0) ”) &&
      emp **
      ((poly_store FET_int &( ((s)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") m)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "prev") y)) **
      ((dllseg_shape p q y s))
      ) ** (
      ALL (n : Z),
        TT &&
        emp **
        ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "prev") n)) -*
        TT &&
        emp **
        ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "prev") n))
        ).

Definition dll_shape_strategy15 :=
  forall (q : Z) (x : Z) (t : Z) (p : Z) (r : Z) (s : Z),
    TT &&
    (“ (p = t) ”) &&
    (“ (q = x) ”) &&
    emp **
    ((dllseg_shape p q r s))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp **
    ((dlistrep_shape s r)) -*
    TT &&
    emp **
    ((dlistrep_shape t x))
    ).

Definition dll_shape_strategy16 :=
  forall (s : Z) (q : Z) (p : Z) (m : Z),
    TT &&
    (“ (s <> q) ”) &&
    emp **
    ((dllseg_shape p q s m))
    |--
    EX (x : Z) (y : Z),
      (
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") m)) **
      ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "prev") y)) **
      ((dllseg_shape p q y s))
      ) ** (
      ALL (n : Z),
        TT &&
        emp **
        ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") n)) -*
        TT &&
        emp **
        ((poly_store FET_ptr &( ((s)) # "list" ->ₛ "next") n))
        ).

Definition dll_shape_strategy8 :=
  forall (p : Z) (x : Z),
    TT &&
    emp **
    ((dlistrep_shape p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : Z),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((dlistrep_shape p y))
      ).

Definition dll_shape_strategy11 :=
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
    TT &&
    emp -*
    TT &&
    emp **
    ((dllseg_shape p q r s))
    ).

Definition dll_shape_strategy5 :=
  forall (p : Z) (prev : Z),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((dlistrep_shape p prev))
    |--
    EX (x : Z) (y : Z),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "prev") prev)) **
      ((dlistrep_shape y p))
      ) ** (
      ALL (q : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "prev") q)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "prev") q))
        ).

Definition dll_shape_strategy6 :=
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
    ALL (prev : Z) (x : Z) (y : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "prev") prev)) **
      ((dlistrep_shape y p)) -*
      TT &&
      emp **
      ((dlistrep_shape p prev))
      ).

Module Type dll_shape_Strategy_Correct.

  Axiom dll_shape_strategy1_correctness : dll_shape_strategy1.
  Axiom dll_shape_strategy2_correctness : dll_shape_strategy2.
  Axiom dll_shape_strategy3_correctness : dll_shape_strategy3.
  Axiom dll_shape_strategy4_correctness : dll_shape_strategy4.
  Axiom dll_shape_strategy12_correctness : dll_shape_strategy12.
  Axiom dll_shape_strategy7_correctness : dll_shape_strategy7.
  Axiom dll_shape_strategy13_correctness : dll_shape_strategy13.
  Axiom dll_shape_strategy14_correctness : dll_shape_strategy14.
  Axiom dll_shape_strategy15_correctness : dll_shape_strategy15.
  Axiom dll_shape_strategy16_correctness : dll_shape_strategy16.
  Axiom dll_shape_strategy8_correctness : dll_shape_strategy8.
  Axiom dll_shape_strategy11_correctness : dll_shape_strategy11.
  Axiom dll_shape_strategy5_correctness : dll_shape_strategy5.
  Axiom dll_shape_strategy6_correctness : dll_shape_strategy6.

End dll_shape_Strategy_Correct.
