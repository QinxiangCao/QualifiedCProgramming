From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple4_strategy_goal.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple4_strategy_proof.

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

Module Type VC_Correct.

Include swap_simple4_Strategy_Correct.

Axiom proof_of_swap_int_pair_entail_wit_1 : swap_int_pair_entail_wit_1.
Axiom proof_of_swap_int_pair_entail_wit_2 : swap_int_pair_entail_wit_2.
Axiom proof_of_swap_int_pair_return_wit_1 : swap_int_pair_return_wit_1.

End VC_Correct.
