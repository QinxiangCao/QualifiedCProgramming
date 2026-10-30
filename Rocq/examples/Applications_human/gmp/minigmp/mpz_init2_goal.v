From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_init2 -----*)

Definition mpz_init2_safety_wit_1 :=
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : (bits_pre = (alloc * 32 ))) (PreH2 : (alloc > 0)) (PreH3 : (alloc <= INT_MAX)),
  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_init2_safety_wit_2 :=
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : (bits_pre = 0)) (PreH2 : (bits_pre = (alloc * 32 ))) (PreH3 : (alloc > 0)) (PreH4 : (alloc <= INT_MAX)),
  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ False ”
.

Definition mpz_init2_safety_wit_3 :=
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : (bits_pre <> 0)) (PreH2 : (bits_pre = (alloc * 32 ))) (PreH3 : (alloc > 0)) (PreH4 : (alloc <= INT_MAX)),
  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> (bits_pre - 1 ))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ (32 <> 0) ”
.

Definition mpz_init2_safety_wit_4 :=
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : (bits_pre <> 0)) (PreH2 : (bits_pre = (alloc * 32 ))) (PreH3 : (alloc > 0)) (PreH4 : (alloc <= INT_MAX)),
  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> (bits_pre - 1 ))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_init2_safety_wit_5 :=
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : (bits_pre <> 0)) (PreH2 : (bits_pre = (alloc * 32 ))) (PreH3 : (alloc > 0)) (PreH4 : (alloc <= INT_MAX)),
  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> (bits_pre - 1 ))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_init2_safety_wit_6 :=
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : (bits_pre <> 0)) (PreH2 : (bits_pre = (alloc * 32 ))) (PreH3 : (alloc > 0)) (PreH4 : (alloc <= INT_MAX)),
  ((( &( "rn" ) )) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> (bits_pre - 1 ))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_init2_return_wit_1 :=
(
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (bits_pre <> 0)) (PreH3 : (bits_pre = (alloc * 32 ))) (PreH4 : (alloc > 0)) (PreH5 : (alloc <= INT_MAX)),
  (UIntArray.undef_full retval (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) )
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (x__mp_size: Z) (ptr: Z),
  “ (ptr <> 0) ”
  &&  “ (x__mp_size = 0) ”
  &&  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> alloc)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> x__mp_size)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_full ptr alloc )
) \/
(
forall (alloc: Z) (bits_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (bits_pre <> 0)) (PreH3 : (bits_pre = (alloc * 32 ))) (PreH4 : (alloc > 0)) (PreH5 : (alloc <= INT_MAX)),
  (UIntArray.undef_full retval (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) )
|--
  “ ((signed_last_nbits ((1 + (((alloc * 32 ) - 1 ) ÷ 32 ) )) (32)) = alloc) ”
  &&  (UIntArray.undef_full retval alloc )
).

Definition mpz_init2_return_wit_1_split_goal_1 :=
forall (alloc: Z) (bits_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (bits_pre <> 0)) (PreH3 : (bits_pre = (alloc * 32 ))) (PreH4 : (alloc > 0)) (PreH5 : (alloc <= INT_MAX)),
  (UIntArray.undef_full retval (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) )
|--
  “ ((signed_last_nbits ((1 + (((alloc * 32 ) - 1 ) ÷ 32 ) )) (32)) = alloc) ”
.

Definition mpz_init2_return_wit_1_split_goal_spatial :=
forall (alloc: Z) (bits_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (bits_pre <> 0)) (PreH3 : (bits_pre = (alloc * 32 ))) (PreH4 : (alloc > 0)) (PreH5 : (alloc <= INT_MAX)),
  (UIntArray.undef_full retval (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) )
|--
  (UIntArray.undef_full retval alloc )
.

Definition mpz_init2_partial_solve_wit_1_pure :=
(
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : (bits_pre <> 0)) (PreH2 : (bits_pre = (alloc * 32 ))) (PreH3 : (alloc > 0)) (PreH4 : (alloc <= INT_MAX)),
  ((( &( "rn" ) )) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> (bits_pre - 1 ))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ ((signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) > 0) ”
  &&  “ ((signed_last_nbits ((1 + (((alloc * 32 ) - 1 ) ÷ 32 ) )) (32)) > 0) ”
) \/
(
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : ((bits_pre - 1 ) <= UINT64_MAX)) (PreH2 : ((bits_pre - 1 ) >= 0)) (PreH3 : (0 <= INT_MAX)) (PreH4 : ((signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : ((signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) >= INT_MIN)) (PreH7 : (bits_pre <> 0)) (PreH8 : (bits_pre = (alloc * 32 ))) (PreH9 : (alloc > 0)) (PreH10 : (alloc <= INT_MAX)),
  ((( &( "rn" ) )) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> (bits_pre - 1 ))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ ((signed_last_nbits ((1 + (((alloc * 32 ) - 1 ) ÷ 32 ) )) (32)) > 0) ”
  &&  “ ((signed_last_nbits ((1 + (((alloc * 32 ) - 1 ) ÷ 32 ) )) (32)) > 0) ”
).

Definition mpz_init2_partial_solve_wit_1_pure_split_goal_1 :=
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : ((bits_pre - 1 ) <= UINT64_MAX)) (PreH2 : ((bits_pre - 1 ) >= 0)) (PreH3 : (0 <= INT_MAX)) (PreH4 : ((signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : ((signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) >= INT_MIN)) (PreH7 : (bits_pre <> 0)) (PreH8 : (bits_pre = (alloc * 32 ))) (PreH9 : (alloc > 0)) (PreH10 : (alloc <= INT_MAX)),
  ((( &( "rn" ) )) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> (bits_pre - 1 ))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ ((signed_last_nbits ((1 + (((alloc * 32 ) - 1 ) ÷ 32 ) )) (32)) > 0) ”
.

Definition mpz_init2_partial_solve_wit_1_pure_split_goal_2 :=
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : ((bits_pre - 1 ) <= UINT64_MAX)) (PreH2 : ((bits_pre - 1 ) >= 0)) (PreH3 : (0 <= INT_MAX)) (PreH4 : ((signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : ((signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) >= INT_MIN)) (PreH7 : (bits_pre <> 0)) (PreH8 : (bits_pre = (alloc * 32 ))) (PreH9 : (alloc > 0)) (PreH10 : (alloc <= INT_MAX)),
  ((( &( "rn" ) )) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> (bits_pre - 1 ))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ ((signed_last_nbits ((1 + (((alloc * 32 ) - 1 ) ÷ 32 ) )) (32)) > 0) ”
.

Definition mpz_init2_partial_solve_wit_1_aux :=
forall (alloc: Z) (x_pre: Z) (bits_pre: Z) (PreH1 : (bits_pre <> 0)) (PreH2 : (bits_pre = (alloc * 32 ))) (PreH3 : (alloc > 0)) (PreH4 : (alloc <= INT_MAX)),
  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
|--
  “ ((signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)) > 0) ”
  &&  “ ((signed_last_nbits ((1 + (((alloc * 32 ) - 1 ) ÷ 32 ) )) (32)) > 0) ”
  &&  “ (bits_pre <> 0) ”
  &&  “ (bits_pre = (alloc * 32 )) ”
  &&  “ (alloc > 0) ”
  &&  “ (alloc <= INT_MAX) ”
  &&  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (signed_last_nbits ((1 + ((bits_pre - 1 ) ÷ 32 ) )) (32)))
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
.

Definition mpz_init2_partial_solve_wit_1 := mpz_init2_partial_solve_wit_1_pure -> mpz_init2_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_init2_safety_wit_1 : mpz_init2_safety_wit_1.
Axiom proof_of_mpz_init2_safety_wit_2 : mpz_init2_safety_wit_2.
Axiom proof_of_mpz_init2_safety_wit_3 : mpz_init2_safety_wit_3.
Axiom proof_of_mpz_init2_safety_wit_4 : mpz_init2_safety_wit_4.
Axiom proof_of_mpz_init2_safety_wit_5 : mpz_init2_safety_wit_5.
Axiom proof_of_mpz_init2_safety_wit_6 : mpz_init2_safety_wit_6.
Axiom proof_of_mpz_init2_return_wit_1 : mpz_init2_return_wit_1.
Axiom proof_of_mpz_init2_partial_solve_wit_1_pure : mpz_init2_partial_solve_wit_1_pure.
Axiom proof_of_mpz_init2_partial_solve_wit_1 : mpz_init2_partial_solve_wit_1.

End VC_Correct.
