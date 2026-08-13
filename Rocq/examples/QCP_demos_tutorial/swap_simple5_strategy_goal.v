Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.int_pair_additional_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition swap_simple5_strategy0 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((store_int_pair_y_only p y))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = x) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") v))
      ).

Definition swap_simple5_strategy1 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((store_int_pair_x_only p x))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = y) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") v))
      ).

Definition swap_simple5_strategy2 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((store_int_pair_y_only p y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "int_pair" ->ₛ "a")))
    ).

Definition swap_simple5_strategy3 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((store_int_pair_x_only p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "int_pair" ->ₛ "b")))
    ).

Definition swap_simple5_strategy4 :=
  forall (x : Z) (p : Z) (y : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") x)) **
    ((store_int_pair_y_only p y))
    |--
    (
    TT &&
    emp **
    ((store_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition swap_simple5_strategy5 :=
  forall (y : Z) (p : Z) (x : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") y)) **
    ((store_int_pair_x_only p x))
    |--
    (
    TT &&
    emp **
    ((store_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition swap_simple5_strategy6 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") x)) **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition swap_simple5_strategy7 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") x)) **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") y))
    |--
    (
    TT &&
    emp **
    ((store_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type swap_simple5_Strategy_Correct.

  Axiom swap_simple5_strategy0_correctness : swap_simple5_strategy0.
  Axiom swap_simple5_strategy1_correctness : swap_simple5_strategy1.
  Axiom swap_simple5_strategy2_correctness : swap_simple5_strategy2.
  Axiom swap_simple5_strategy3_correctness : swap_simple5_strategy3.
  Axiom swap_simple5_strategy4_correctness : swap_simple5_strategy4.
  Axiom swap_simple5_strategy5_correctness : swap_simple5_strategy5.
  Axiom swap_simple5_strategy6_correctness : swap_simple5_strategy6.
  Axiom swap_simple5_strategy7_correctness : swap_simple5_strategy7.

End swap_simple5_Strategy_Correct.
