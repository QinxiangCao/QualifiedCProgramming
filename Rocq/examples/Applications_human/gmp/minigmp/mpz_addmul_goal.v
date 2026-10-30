From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_addmul -----*)

Definition mpz_addmul_return_wit_1 :=
forall (z2: Z) (z1: Z) (old: Z) (rop_pre: Z) (op1_pre: Z) (op2_pre: Z) (retval: Z) (PreH1 : (retval <> 0)),
  (store_Z rop_pre (old + (z1 * z2 ) ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
|--
  (store_Z rop_pre (old + (z1 * z2 ) ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
.

Definition mpz_addmul_partial_solve_wit_1 :=
forall (z2: Z) (z1: Z) (old: Z) (rop_pre: Z) (op1_pre: Z) (op2_pre: Z),
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
|--
  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
.

Definition mpz_addmul_partial_solve_wit_2 :=
forall (z2: Z) (z1: Z) (old: Z) (rop_pre: Z) (op1_pre: Z) (op2_pre: Z) (retval: Z) (PreH1 : (retval <> 0)),
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
|--
  “ (retval <> 0) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
.

Definition mpz_addmul_partial_solve_wit_3 :=
forall (z2: Z) (z1: Z) (old: Z) (rop_pre: Z) (op1_pre: Z) (op2_pre: Z) (retval: Z) (PreH1 : (retval <> 0)),
  (store_Z retval 0 )
  **  (store_Z rop_pre old )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
|--
  “ (retval <> 0) ”
  &&  (store_Z retval 0 )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z rop_pre old )
.

Definition mpz_addmul_partial_solve_wit_4_pure :=
forall (z2: Z) (z1: Z) (old: Z) (rop_pre: Z) (op1_pre: Z) (op2_pre: Z) (retval: Z) (PreH1 : (retval <> 0)),
  (store_Z retval (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  ((( &( "t" ) )) # Ptr  |-> retval)
  **  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op1" ) )) # Ptr  |-> op1_pre)
  **  ((( &( "op2" ) )) # Ptr  |-> op2_pre)
  **  (store_Z rop_pre old )
|--
  “ (rop_pre = rop_pre) ”
.

Definition mpz_addmul_partial_solve_wit_4_aux :=
forall (z2: Z) (z1: Z) (old: Z) (rop_pre: Z) (op1_pre: Z) (op2_pre: Z) (retval: Z) (PreH1 : (retval <> 0)),
  (store_Z retval (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
  **  (store_Z rop_pre old )
|--
  “ (rop_pre = rop_pre) ”
  &&  “ (retval <> 0) ”
  &&  (store_Z rop_pre old )
  **  (store_Z retval (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
.

Definition mpz_addmul_partial_solve_wit_4 := mpz_addmul_partial_solve_wit_4_pure -> mpz_addmul_partial_solve_wit_4_aux.

Definition mpz_addmul_partial_solve_wit_5 :=
forall (z2: Z) (z1: Z) (old: Z) (rop_pre: Z) (op1_pre: Z) (op2_pre: Z) (retval: Z) (PreH1 : (retval <> 0)),
  (store_Z rop_pre (old + (z1 * z2 ) ) )
  **  (store_Z retval (z1 * z2 ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
|--
  “ (retval <> 0) ”
  &&  (store_Z retval (z1 * z2 ) )
  **  (store_Z rop_pre (old + (z1 * z2 ) ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
.

Definition mpz_addmul_partial_solve_wit_6 :=
forall (z2: Z) (z1: Z) (old: Z) (rop_pre: Z) (op1_pre: Z) (op2_pre: Z) (retval: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (retval <> 0)),
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z rop_pre (old + (z1 * z2 ) ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
|--
  “ (retval <> 0) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z rop_pre (old + (z1 * z2 ) ) )
  **  (store_Z op1_pre z1 )
  **  (store_Z op2_pre z2 )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_addmul_return_wit_1 : mpz_addmul_return_wit_1.
Axiom proof_of_mpz_addmul_partial_solve_wit_1 : mpz_addmul_partial_solve_wit_1.
Axiom proof_of_mpz_addmul_partial_solve_wit_2 : mpz_addmul_partial_solve_wit_2.
Axiom proof_of_mpz_addmul_partial_solve_wit_3 : mpz_addmul_partial_solve_wit_3.
Axiom proof_of_mpz_addmul_partial_solve_wit_4_pure : mpz_addmul_partial_solve_wit_4_pure.
Axiom proof_of_mpz_addmul_partial_solve_wit_4 : mpz_addmul_partial_solve_wit_4.
Axiom proof_of_mpz_addmul_partial_solve_wit_5 : mpz_addmul_partial_solve_wit_5.
Axiom proof_of_mpz_addmul_partial_solve_wit_6 : mpz_addmul_partial_solve_wit_6.

End VC_Correct.
