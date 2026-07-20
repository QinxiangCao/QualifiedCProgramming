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

(*----- Function mpz_init_set -----*)

Definition mpz_init_set_return_wit_1 := 
forall (x_pre: Z) (r_pre: Z) (z: Z) ,
  (store_Z r_pre z )
  **  (store_Z x_pre z )
|--
  (store_Z r_pre z )
  **  (store_Z x_pre z )
.

Definition mpz_init_set_partial_solve_wit_1 := 
forall (x_pre: Z) (r_pre: Z) (z: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z x_pre z )
|--
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z x_pre z )
.

Definition mpz_init_set_partial_solve_wit_2 := 
forall (x_pre: Z) (r_pre: Z) (z: Z) ,
  (store_Z r_pre 0 )
  **  (store_Z x_pre z )
|--
  (store_Z r_pre 0 )
  **  (store_Z x_pre z )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_init_set_return_wit_1 : mpz_init_set_return_wit_1.
Axiom proof_of_mpz_init_set_partial_solve_wit_1 : mpz_init_set_partial_solve_wit_1.
Axiom proof_of_mpz_init_set_partial_solve_wit_2 : mpz_init_set_partial_solve_wit_2.

End VC_Correct.
