Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.pos_int_pair_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition pos_int_pair_strategy0 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((store_pos_int_pair_y_only p x y))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = x) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") v))
      ).

Definition pos_int_pair_strategy1 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((store_pos_int_pair_x_only p x y))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = y) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") v))
      ).

Definition pos_int_pair_strategy2 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((store_pos_int_pair_y_only p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "int_pair" ->ₛ "a")))
    ).

Definition pos_int_pair_strategy3 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((store_pos_int_pair_x_only p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "int_pair" ->ₛ "b")))
    ).

Definition pos_int_pair_strategy4 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") x)) **
    ((store_pos_int_pair_y_only p x y))
    |--
    (
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pos_int_pair_strategy6 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") y)) **
    ((store_pos_int_pair_x_only p x y))
    |--
    (
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pos_int_pair_strategy8 :=
  forall (y : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    |--
    (
    TT &&
    (“ (Z.ge x 0) ”) &&
    (“ (Z.ge y 0) ”) &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") x)) **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pos_int_pair_strategy9 :=
  forall (y : Z) (x : Z) (p : Z),
    TT &&
    (“ (Z.ge x 0) ”) &&
    (“ (Z.ge y 0) ”) &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") x)) **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") y))
    |--
    (
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pos_int_pair_strategy10 :=
  forall (x : Z) (p : Z) (y : Z),
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    |--
    (
    TT &&
    (“ (Z.ge x 0) ”) &&
    emp **
    ((store_pos_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pos_int_pair_strategy11 :=
  forall (y : Z) (p : Z) (x : Z),
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    |--
    (
    TT &&
    (“ (Z.ge y 0) ”) &&
    emp **
    ((store_pos_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pos_int_pair_strategy12 :=
  forall (x : Z) (p : Z) (y : Z),
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    |--
    (
    TT &&
    (“ (Z.le x ( INT_MAX)) ”) &&
    emp **
    ((store_pos_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pos_int_pair_strategy13 :=
  forall (y : Z) (p : Z) (x : Z),
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    |--
    (
    TT &&
    (“ (Z.le y ( INT_MAX)) ”) &&
    emp **
    ((store_pos_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pos_int_pair_strategy5 :=
  forall (x : Z) (p : Z) (y : Z) (x0 : Z),
    TT &&
    (“ (Z.ge x 0) ”) &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") x)) **
    ((store_pos_int_pair_y_only p x0 y))
    |--
    (
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition pos_int_pair_strategy7 :=
  forall (y : Z) (p : Z) (y0 : Z) (x : Z),
    TT &&
    (“ (Z.ge y 0) ”) &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") y)) **
    ((store_pos_int_pair_x_only p x y0))
    |--
    (
    TT &&
    emp **
    ((store_pos_int_pair p x y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type pos_int_pair_Strategy_Correct.

  Axiom pos_int_pair_strategy0_correctness : pos_int_pair_strategy0.
  Axiom pos_int_pair_strategy1_correctness : pos_int_pair_strategy1.
  Axiom pos_int_pair_strategy2_correctness : pos_int_pair_strategy2.
  Axiom pos_int_pair_strategy3_correctness : pos_int_pair_strategy3.
  Axiom pos_int_pair_strategy4_correctness : pos_int_pair_strategy4.
  Axiom pos_int_pair_strategy6_correctness : pos_int_pair_strategy6.
  Axiom pos_int_pair_strategy8_correctness : pos_int_pair_strategy8.
  Axiom pos_int_pair_strategy9_correctness : pos_int_pair_strategy9.
  Axiom pos_int_pair_strategy10_correctness : pos_int_pair_strategy10.
  Axiom pos_int_pair_strategy11_correctness : pos_int_pair_strategy11.
  Axiom pos_int_pair_strategy12_correctness : pos_int_pair_strategy12.
  Axiom pos_int_pair_strategy13_correctness : pos_int_pair_strategy13.
  Axiom pos_int_pair_strategy5_correctness : pos_int_pair_strategy5.
  Axiom pos_int_pair_strategy7_correctness : pos_int_pair_strategy7.

End pos_int_pair_Strategy_Correct.
