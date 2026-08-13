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

(*----- Function mpz_tdiv_r -----*)

Definition mpz_tdiv_r_safety_wit_1 := 
forall (d_pre: Z) (n_pre: Z) (r_pre: Z) (zd_r_eq_n: Z) (zn_r_eq_n: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_tdiv_r_safety_wit_2 := 
forall (d_pre: Z) (n_pre: Z) (r_pre: Z) (zd_r_eq_n: Z) (zn_r_eq_n: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 0 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpz_tdiv_r_entail_wit_1 := 
(
forall (d_pre: Z) (n_pre: Z) (r_pre: Z) (zd_r_eq_n: Z) (zn_r_eq_n: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)) ,
  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
|--
  “ (r_pre = n_pre) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (zd_r_eq_n <> 0) ”
  &&  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 0 )
) \/
(
forall (d_pre: Z) (n_pre: Z) (r_pre: Z) (zd_r_eq_n: Z) (zn_r_eq_n: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)) ,
  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
|--
  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 0 )
).

Definition mpz_tdiv_r_entail_wit_1_split_goal_spatial := 
forall (d_pre: Z) (n_pre: Z) (r_pre: Z) (zd_r_eq_n: Z) (zn_r_eq_n: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)) ,
  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
|--
  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 0 )
.

Definition mpz_tdiv_r_entail_wit_2 := 
forall (d_pre: Z) (n_pre: Z) (r_pre: Z) (zd_r_eq_n: Z) (zn_r_eq_n: Z) (qv_2: Z) (rv_2: Z) (retval: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (mpz_div_qr_math 2 zn_r_eq_n zd_r_eq_n qv_2 rv_2 )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (mpz_div_qr_ret_ok retval rv_2 )) (PreH6 : (r_pre = n_pre)) (PreH7 : (n_pre <> 0)) (PreH8 : (zd_r_eq_n <> 0)) ,
  (store_Z n_pre rv_2 )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 qv_2 )
|--
  (EX (rv: Z)  (qv: Z) ,
  “ (r_pre = n_pre) ” 
  &&  “ (zd_r_eq_n <> 0) ” 
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ” 
  &&  “ (rv = 0) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 qv ))
  ||
  (EX (rv: Z)  (qv: Z) ,
  “ (r_pre = n_pre) ” 
  &&  “ (zd_r_eq_n <> 0) ” 
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ” 
  &&  “ (same_sign rv zn_r_eq_n ) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 qv ))
.

Definition mpz_tdiv_r_return_wit_1 := 
forall (d_pre: Z) (n_pre: Z) (r_pre: Z) (zd_r_eq_n: Z) (zn_r_eq_n: Z) (qv_2: Z) (rv_2: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (zd_r_eq_n <> 0)) (PreH3 : (zn_r_eq_n = ((qv_2 * zd_r_eq_n ) + rv_2 ))) (PreH4 : ((Zabs (rv_2)) < (Zabs (zd_r_eq_n)))) (PreH5 : (rv_2 = 0)) ,
  (store_Z n_pre rv_2 )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 qv_2 )
|--
  (EX (rv: Z)  (qv: Z) ,
  “ (r_pre = n_pre) ” 
  &&  “ (zd_r_eq_n <> 0) ” 
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ” 
  &&  “ (rv = 0) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n ))
  ||
  (EX (rv: Z)  (qv: Z) ,
  “ (r_pre = n_pre) ” 
  &&  “ (zd_r_eq_n <> 0) ” 
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ” 
  &&  “ (same_sign rv zn_r_eq_n ) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n ))
.

Definition mpz_tdiv_r_return_wit_2 := 
forall (d_pre: Z) (n_pre: Z) (r_pre: Z) (zd_r_eq_n: Z) (zn_r_eq_n: Z) (qv_2: Z) (rv_2: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (zd_r_eq_n <> 0)) (PreH3 : (zn_r_eq_n = ((qv_2 * zd_r_eq_n ) + rv_2 ))) (PreH4 : ((Zabs (rv_2)) < (Zabs (zd_r_eq_n)))) (PreH5 : (same_sign rv_2 zn_r_eq_n )) ,
  (store_Z n_pre rv_2 )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 qv_2 )
|--
  (EX (rv: Z)  (qv: Z) ,
  “ (r_pre = n_pre) ” 
  &&  “ (zd_r_eq_n <> 0) ” 
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ” 
  &&  “ (rv = 0) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n ))
  ||
  (EX (rv: Z)  (qv: Z) ,
  “ (r_pre = n_pre) ” 
  &&  “ (zd_r_eq_n <> 0) ” 
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ” 
  &&  “ (same_sign rv zn_r_eq_n ) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n ))
.

Definition mpz_tdiv_r_partial_solve_wit_1_pure := 
forall (d_pre: Z) (n_pre: Z) (r_pre: Z) (zd_r_eq_n: Z) (zn_r_eq_n: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 0 )
|--
  “ (0 = 0) ” 
  &&  “ (r_pre = r_pre) ” 
  &&  “ (n_pre = n_pre) ” 
  &&  “ (d_pre = d_pre) ” 
  &&  “ (2 = 2) ” 
  &&  “ (r_pre = n_pre) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (zd_r_eq_n <> 0) ” 
  &&  “ (2 = 2) ”
.

Definition mpz_tdiv_r_partial_solve_wit_1_aux := 
forall (d_pre: Z) (n_pre: Z) (r_pre: Z) (zd_r_eq_n: Z) (zn_r_eq_n: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)) ,
  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 0 )
|--
  “ (0 = 0) ” 
  &&  “ (r_pre = r_pre) ” 
  &&  “ (n_pre = n_pre) ” 
  &&  “ (d_pre = d_pre) ” 
  &&  “ (2 = 2) ” 
  &&  “ (r_pre = n_pre) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (zd_r_eq_n <> 0) ” 
  &&  “ (2 = 2) ” 
  &&  “ (r_pre = n_pre) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (zd_r_eq_n <> 0) ”
  &&  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 0 )
.

Definition mpz_tdiv_r_partial_solve_wit_1 := mpz_tdiv_r_partial_solve_wit_1_pure -> mpz_tdiv_r_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_tdiv_r_safety_wit_1 : mpz_tdiv_r_safety_wit_1.
Axiom proof_of_mpz_tdiv_r_safety_wit_2 : mpz_tdiv_r_safety_wit_2.
Axiom proof_of_mpz_tdiv_r_entail_wit_1 : mpz_tdiv_r_entail_wit_1.
Axiom proof_of_mpz_tdiv_r_entail_wit_2 : mpz_tdiv_r_entail_wit_2.
Axiom proof_of_mpz_tdiv_r_return_wit_1 : mpz_tdiv_r_return_wit_1.
Axiom proof_of_mpz_tdiv_r_return_wit_2 : mpz_tdiv_r_return_wit_2.
Axiom proof_of_mpz_tdiv_r_partial_solve_wit_1_pure : mpz_tdiv_r_partial_solve_wit_1_pure.
Axiom proof_of_mpz_tdiv_r_partial_solve_wit_1 : mpz_tdiv_r_partial_solve_wit_1.

End VC_Correct.
