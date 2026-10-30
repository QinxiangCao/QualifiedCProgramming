From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope sac.

Definition swap_simple4_strategy0 :=
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

Definition swap_simple4_strategy1 :=
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

Module Type swap_simple4_Strategy_Correct.

  Axiom swap_simple4_strategy0_correctness : swap_simple4_strategy0.
  Axiom swap_simple4_strategy1_correctness : swap_simple4_strategy1.

End swap_simple4_Strategy_Correct.
