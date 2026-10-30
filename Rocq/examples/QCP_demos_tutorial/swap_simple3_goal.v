From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple3_strategy_goal.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple3_strategy_proof.

(*----- Function swap_int_pair -----*)

Definition swap_int_pair_return_wit_1 :=
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre y x )
|--
  (store_int_pair p_pre y x )
.

Definition swap_int_pair_partial_solve_wit_1 :=
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
.

Definition swap_int_pair_partial_solve_wit_2 :=
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
  **  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
.

Definition swap_int_pair_partial_solve_wit_3 :=
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |->_)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
.

Definition swap_int_pair_partial_solve_wit_4 :=
forall (y: Z) (p_pre: Z),
  (store_int_pair p_pre y y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |->_)
  **  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> y)
.

Module Type VC_Correct.

Include swap_simple3_Strategy_Correct.

Axiom proof_of_swap_int_pair_return_wit_1 : swap_int_pair_return_wit_1.
Axiom proof_of_swap_int_pair_partial_solve_wit_1 : swap_int_pair_partial_solve_wit_1.
Axiom proof_of_swap_int_pair_partial_solve_wit_2 : swap_int_pair_partial_solve_wit_2.
Axiom proof_of_swap_int_pair_partial_solve_wit_3 : swap_int_pair_partial_solve_wit_3.
Axiom proof_of_swap_int_pair_partial_solve_wit_4 : swap_int_pair_partial_solve_wit_4.

End VC_Correct.
