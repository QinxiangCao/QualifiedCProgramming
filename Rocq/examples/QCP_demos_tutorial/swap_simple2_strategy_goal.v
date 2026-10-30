From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope sac.

Definition swap_simple2_strategy0 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") y))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = x) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") v))
      ).

Definition swap_simple2_strategy1 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") x))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = y) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") v))
      ).

Definition swap_simple2_strategy2 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "b") y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "int_pair" ->ₛ "a")))
    ).

Definition swap_simple2_strategy3 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_int_pair p x y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((p)) # "int_pair" ->ₛ "a") x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((p)) # "int_pair" ->ₛ "b")))
    ).

Module Type swap_simple2_Strategy_Correct.

  Axiom swap_simple2_strategy0_correctness : swap_simple2_strategy0.
  Axiom swap_simple2_strategy1_correctness : swap_simple2_strategy1.
  Axiom swap_simple2_strategy2_correctness : swap_simple2_strategy2.
  Axiom swap_simple2_strategy3_correctness : swap_simple2_strategy3.

End swap_simple2_Strategy_Correct.
