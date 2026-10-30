From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope sac.

(*----- Function swap_int_pair -----*)

Definition swap_int_pair_entail_wit_1 :=
(
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
) \/
(
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
).

Definition swap_int_pair_entail_wit_1_split_goal_spatial :=
forall (y: Z) (x: Z) (p_pre: Z),
  (store_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
.

Definition swap_int_pair_return_wit_1 :=
(
forall (y: Z) (x: Z) (p_pre: Z),
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> y)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> x)
|--
  (store_int_pair p_pre y x )
) \/
(
forall (y: Z) (x: Z) (p_pre: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (y <= INT_MAX)) (PreH3 : (x >= INT_MIN)) (PreH4 : (y >= INT_MIN)),
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> y)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> x)
|--
  (store_int_pair p_pre y x )
).

Definition swap_int_pair_return_wit_1_split_goal_spatial :=
forall (y: Z) (x: Z) (p_pre: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (y <= INT_MAX)) (PreH3 : (x >= INT_MIN)) (PreH4 : (y >= INT_MIN)),
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> y)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> x)
|--
  (store_int_pair p_pre y x )
.

Module Type VC_Correct.


Axiom proof_of_swap_int_pair_entail_wit_1 : swap_int_pair_entail_wit_1.
Axiom proof_of_swap_int_pair_return_wit_1 : swap_int_pair_return_wit_1.

End VC_Correct.
