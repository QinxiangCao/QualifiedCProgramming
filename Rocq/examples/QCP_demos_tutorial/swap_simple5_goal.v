From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.int_pair_additional_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple5_strategy_goal.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple5_strategy_proof.

(*----- Function swap_int_pair -----*)

Definition swap_int_pair_entail_wit_1 :=
forall (y: Z) (x: Z) (p_pre: Z),
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
  **  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
.

Definition swap_int_pair_entail_wit_2 :=
forall (y: Z) (x: Z) (p_pre: Z),
  ((( &( "temp" ) )) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> y)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  (store_int_pair p_pre y x )
  **  ((( &( "temp" ) )) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
.

Definition swap_int_pair_return_wit_1 :=
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre y x )
|--
  (store_int_pair p_pre y x )
.

(*----- Function swap_int_pair2 -----*)

Definition swap_int_pair2_return_wit_1 :=
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre y x )
|--
  (store_int_pair p_pre y x )
.

Definition swap_int_pair2_partial_solve_wit_1 :=
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  (store_int_pair_y_only p_pre y )
.

Definition swap_int_pair2_partial_solve_wit_2 :=
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
  **  (store_int_pair_x_only p_pre x )
.

Definition swap_int_pair2_partial_solve_wit_3 :=
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |->_)
  **  (store_int_pair_y_only p_pre y )
.

Definition swap_int_pair2_partial_solve_wit_4 :=
forall (y: Z) (p_pre: Z),
  (store_int_pair p_pre y y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |->_)
  **  (store_int_pair_x_only p_pre y )
.

Module Type VC_Correct.

Include swap_simple5_Strategy_Correct.

Axiom proof_of_swap_int_pair_entail_wit_1 : swap_int_pair_entail_wit_1.
Axiom proof_of_swap_int_pair_entail_wit_2 : swap_int_pair_entail_wit_2.
Axiom proof_of_swap_int_pair_return_wit_1 : swap_int_pair_return_wit_1.
Axiom proof_of_swap_int_pair2_return_wit_1 : swap_int_pair2_return_wit_1.
Axiom proof_of_swap_int_pair2_partial_solve_wit_1 : swap_int_pair2_partial_solve_wit_1.
Axiom proof_of_swap_int_pair2_partial_solve_wit_2 : swap_int_pair2_partial_solve_wit_2.
Axiom proof_of_swap_int_pair2_partial_solve_wit_3 : swap_int_pair2_partial_solve_wit_3.
Axiom proof_of_swap_int_pair2_partial_solve_wit_4 : swap_int_pair2_partial_solve_wit_4.

End VC_Correct.
