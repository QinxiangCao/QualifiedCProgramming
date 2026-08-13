Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_add_ui -----*)

Definition mpz_add_ui_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (b0_r_eq_a: Z) (za_r_eq_a: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (b_pre = b0_r_eq_a)) (PreH4 : (0 <= b0_r_eq_a)) ,
  (store_Z a_pre (za_r_eq_a + b0_r_eq_a ) )
|--
  (store_Z a_pre (za_r_eq_a + b0_r_eq_a ) )
.

Definition mpz_add_ui_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (b0_r_eq_a: Z) (za_r_eq_a: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (b_pre = b0_r_eq_a)) (PreH3 : (0 <= b0_r_eq_a)) ,
  (store_Z a_pre za_r_eq_a )
|--
  “ (r_pre = a_pre) ” 
  &&  “ (b_pre = b0_r_eq_a) ” 
  &&  “ (0 <= b0_r_eq_a) ”
  &&  (store_Z a_pre za_r_eq_a )
.

Definition mpz_add_ui_partial_solve_wit_2_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (b0_r_eq_a: Z) (za_r_eq_a: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (b_pre = b0_r_eq_a)) (PreH4 : (0 <= b0_r_eq_a)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((( &( "bb" ) )) # Ptr  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  (store_Z a_pre za_r_eq_a )
|--
  “ (b_pre = b0_r_eq_a) ” 
  &&  “ (0 <= b0_r_eq_a) ”
.

Definition mpz_add_ui_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (b0_r_eq_a: Z) (za_r_eq_a: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (b_pre = b0_r_eq_a)) (PreH4 : (0 <= b0_r_eq_a)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z a_pre za_r_eq_a )
|--
  “ (b_pre = b0_r_eq_a) ” 
  &&  “ (0 <= b0_r_eq_a) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (b_pre = b0_r_eq_a) ” 
  &&  “ (0 <= b0_r_eq_a) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z a_pre za_r_eq_a )
.

Definition mpz_add_ui_partial_solve_wit_2 := mpz_add_ui_partial_solve_wit_2_pure -> mpz_add_ui_partial_solve_wit_2_aux.

Definition mpz_add_ui_partial_solve_wit_3_pure := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (b0_r_eq_a: Z) (za_r_eq_a: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (b_pre = b0_r_eq_a)) (PreH4 : (0 <= b0_r_eq_a)) ,
  (store_Z retval b0_r_eq_a )
  **  ((( &( "bb" ) )) # Ptr  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  (store_Z a_pre za_r_eq_a )
|--
  “ (r_pre = a_pre) ”
.

Definition mpz_add_ui_partial_solve_wit_3_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (b0_r_eq_a: Z) (za_r_eq_a: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (b_pre = b0_r_eq_a)) (PreH4 : (0 <= b0_r_eq_a)) ,
  (store_Z retval b0_r_eq_a )
  **  (store_Z a_pre za_r_eq_a )
|--
  “ (r_pre = a_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (b_pre = b0_r_eq_a) ” 
  &&  “ (0 <= b0_r_eq_a) ”
  &&  (store_Z a_pre za_r_eq_a )
  **  (store_Z retval b0_r_eq_a )
.

Definition mpz_add_ui_partial_solve_wit_3 := mpz_add_ui_partial_solve_wit_3_pure -> mpz_add_ui_partial_solve_wit_3_aux.

Definition mpz_add_ui_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (b0_r_eq_a: Z) (za_r_eq_a: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (b_pre = b0_r_eq_a)) (PreH4 : (0 <= b0_r_eq_a)) ,
  (store_Z a_pre (za_r_eq_a + b0_r_eq_a ) )
  **  (store_Z retval b0_r_eq_a )
|--
  “ (retval <> 0) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (b_pre = b0_r_eq_a) ” 
  &&  “ (0 <= b0_r_eq_a) ”
  &&  (store_Z retval b0_r_eq_a )
  **  (store_Z a_pre (za_r_eq_a + b0_r_eq_a ) )
.

Definition mpz_add_ui_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (b0_r_eq_a: Z) (za_r_eq_a: Z) (retval: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (retval <> 0)) (PreH2 : (r_pre = a_pre)) (PreH3 : (b_pre = b0_r_eq_a)) (PreH4 : (0 <= b0_r_eq_a)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z a_pre (za_r_eq_a + b0_r_eq_a ) )
|--
  “ (retval <> 0) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (b_pre = b0_r_eq_a) ” 
  &&  “ (0 <= b0_r_eq_a) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z a_pre (za_r_eq_a + b0_r_eq_a ) )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_add_ui_return_wit_1 : mpz_add_ui_return_wit_1.
Axiom proof_of_mpz_add_ui_partial_solve_wit_1 : mpz_add_ui_partial_solve_wit_1.
Axiom proof_of_mpz_add_ui_partial_solve_wit_2_pure : mpz_add_ui_partial_solve_wit_2_pure.
Axiom proof_of_mpz_add_ui_partial_solve_wit_2 : mpz_add_ui_partial_solve_wit_2.
Axiom proof_of_mpz_add_ui_partial_solve_wit_3_pure : mpz_add_ui_partial_solve_wit_3_pure.
Axiom proof_of_mpz_add_ui_partial_solve_wit_3 : mpz_add_ui_partial_solve_wit_3.
Axiom proof_of_mpz_add_ui_partial_solve_wit_4 : mpz_add_ui_partial_solve_wit_4.
Axiom proof_of_mpz_add_ui_partial_solve_wit_5 : mpz_add_ui_partial_solve_wit_5.

End VC_Correct.
