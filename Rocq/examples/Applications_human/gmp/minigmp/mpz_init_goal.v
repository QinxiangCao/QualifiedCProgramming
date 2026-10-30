From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_init -----*)

Definition mpz_init_safety_wit_1 :=
forall (x_pre: Z),
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_init_safety_wit_2 :=
forall (x_pre: Z),
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_init_return_wit_1 :=
(
forall (x_pre: Z),
  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ( &( "mpz_dummy_limb" ) ))
|--
  (store_Z_dummy x_pre ( &( "mpz_dummy_limb" ) ) )
) \/
(
forall (x_pre: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)),
  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ( &( "mpz_dummy_limb" ) ))
|--
  (store_Z_dummy x_pre ( &( "mpz_dummy_limb" ) ) )
).

Definition mpz_init_return_wit_1_split_goal_spatial :=
forall (x_pre: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)),
  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ( &( "mpz_dummy_limb" ) ))
|--
  (store_Z_dummy x_pre ( &( "mpz_dummy_limb" ) ) )
.

(* Shallow FunAssertion specs for mpz_init. *)
Definition mpz_init_sig : FuncSig := ([ * struct "__mpz_struct"], void)%ctype.

Definition mpz_init_abs : Spec mpz_init_sig :=
  fun F =>
HoareFun ([ * struct "__mpz_struct"], void)%ctype
  (fun x_pre =>
  (((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)))
  (fun x_pre (_retval : unit) =>
  ((store_Z x_pre 0 )))
  F.

Definition mpz_init_dummy : Spec mpz_init_sig :=
  fun F =>
HoareFun ([ * struct "__mpz_struct"], void)%ctype
  (fun x_pre =>
  (((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)))
  (fun x_pre (_retval : unit) =>
  ((store_Z_dummy x_pre ( &( "mpz_dummy_limb" ) ) )))
  F.

Definition mpz_init_dummy_entail_abs :=
forall (x_pre: Z),
  (((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_))
|--
  (((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_))
  **
  (  ((store_Z_dummy x_pre ( &( "mpz_dummy_limb" ) ) ))
  -*
  ((store_Z x_pre 0 )))
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_init_safety_wit_1 : mpz_init_safety_wit_1.
Axiom proof_of_mpz_init_safety_wit_2 : mpz_init_safety_wit_2.
Axiom proof_of_mpz_init_return_wit_1 : mpz_init_return_wit_1.
Axiom proof_of_mpz_init_dummy_entail_abs : mpz_init_dummy_entail_abs.

End VC_Correct.
