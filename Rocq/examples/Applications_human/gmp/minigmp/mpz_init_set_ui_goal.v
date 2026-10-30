From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_init_set_ui -----*)

Definition mpz_init_set_ui_return_wit_1 :=
forall (x0: Z) (r_pre: Z) (x_pre: Z) (PreH1 : (x_pre = x0)) (PreH2 : (0 <= x0)),
  (store_Z r_pre x0 )
|--
  (store_Z r_pre x0 )
.

Definition mpz_init_set_ui_partial_solve_wit_1 :=
forall (x0: Z) (r_pre: Z) (x_pre: Z) (PreH1 : (x_pre = x0)) (PreH2 : (0 <= x0)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ (x_pre = x0) ”
  &&  “ (0 <= x0) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
.

Definition mpz_init_set_ui_partial_solve_wit_2_pure :=
forall (x0: Z) (r_pre: Z) (x_pre: Z) (PreH1 : (x_pre = x0)) (PreH2 : (0 <= x0)),
  (store_Z r_pre 0 )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (x_pre = x0) ”
  &&  “ (0 <= x0) ”
.

Definition mpz_init_set_ui_partial_solve_wit_2_aux :=
forall (x0: Z) (r_pre: Z) (x_pre: Z) (PreH1 : (x_pre = x0)) (PreH2 : (0 <= x0)),
  (store_Z r_pre 0 )
|--
  “ (x_pre = x0) ”
  &&  “ (0 <= x0) ”
  &&  “ (x_pre = x0) ”
  &&  “ (0 <= x0) ”
  &&  (store_Z r_pre 0 )
.

Definition mpz_init_set_ui_partial_solve_wit_2 := mpz_init_set_ui_partial_solve_wit_2_pure -> mpz_init_set_ui_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_init_set_ui_return_wit_1 : mpz_init_set_ui_return_wit_1.
Axiom proof_of_mpz_init_set_ui_partial_solve_wit_1 : mpz_init_set_ui_partial_solve_wit_1.
Axiom proof_of_mpz_init_set_ui_partial_solve_wit_2_pure : mpz_init_set_ui_partial_solve_wit_2_pure.
Axiom proof_of_mpz_init_set_ui_partial_solve_wit_2 : mpz_init_set_ui_partial_solve_wit_2.

End VC_Correct.
