From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_tdiv_r -----*)

Definition mpz_tdiv_r_safety_wit_1_r_eq_n :=
forall (zd_r_eq_n: Z) (zn_r_eq_n: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)),
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

Definition mpz_tdiv_r_safety_wit_2_r_eq_n :=
forall (zd_r_eq_n: Z) (zn_r_eq_n: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)),
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

Definition mpz_tdiv_r_safety_wit_3_r_eq_n_read0 :=
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zn_r_eq_n_read0 <> 0)) (PreH4 : (zd_r_eq_n_read0 <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 0 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_tdiv_r_safety_wit_4_r_eq_n_read0 :=
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zn_r_eq_n_read0 <> 0)) (PreH4 : (zd_r_eq_n_read0 <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 0 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpz_tdiv_r_entail_wit_1_r_eq_n :=
(
forall (zd_r_eq_n: Z) (zn_r_eq_n: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)),
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
forall (zd_r_eq_n: Z) (zn_r_eq_n: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)),
  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
|--
  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 0 )
).

Definition mpz_tdiv_r_entail_wit_1_r_eq_n_split_goal_spatial :=
forall (zd_r_eq_n: Z) (zn_r_eq_n: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)),
  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
|--
  (store_Z n_pre zn_r_eq_n )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 0 )
.

Definition mpz_tdiv_r_entail_wit_2_r_eq_n_read0 :=
(
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zn_r_eq_n_read0 <> 0)) (PreH4 : (zd_r_eq_n_read0 <> 0)),
  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
|--
  “ (r_pre = n_pre) ”
  &&  “ (n_pre <> 0) ”
  &&  “ (zn_r_eq_n_read0 <> 0) ”
  &&  “ (zd_r_eq_n_read0 <> 0) ”
  &&  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 0 )
) \/
(
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zn_r_eq_n_read0 <> 0)) (PreH4 : (zd_r_eq_n_read0 <> 0)),
  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
|--
  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 0 )
).

Definition mpz_tdiv_r_entail_wit_2_r_eq_n_read0_split_goal_spatial :=
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zn_r_eq_n_read0 <> 0)) (PreH4 : (zd_r_eq_n_read0 <> 0)),
  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
|--
  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 0 )
.

Definition mpz_tdiv_r_entail_wit_3_r_eq_n :=
forall (zd_r_eq_n: Z) (zn_r_eq_n: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (qv_2: Z) (rv_2: Z) (retval: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (mpz_div_qr_math 2 zn_r_eq_n zd_r_eq_n qv_2 rv_2 )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (mpz_div_qr_ret_ok retval rv_2 )) (PreH6 : (r_pre = n_pre)) (PreH7 : (n_pre <> 0)) (PreH8 : (zd_r_eq_n <> 0)),
  (store_Z n_pre rv_2 )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 qv_2 )
|--
  (EX (rv: Z) (qv: Z),
  “ (r_pre = n_pre) ”
  &&  “ (zd_r_eq_n <> 0) ”
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ”
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ”
  &&  “ (rv = 0) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 qv ))
  ||
  (EX (rv: Z) (qv: Z),
  “ (r_pre = n_pre) ”
  &&  “ (zd_r_eq_n <> 0) ”
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ”
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ”
  &&  “ (same_sign rv zn_r_eq_n ) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 qv ))
.

Definition mpz_tdiv_r_entail_wit_4_r_eq_n_read0 :=
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (qv_2: Z) (rv_2: Z) (retval: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (mpz_div_qr_math 2 zn_r_eq_n_read0 zd_r_eq_n_read0 qv_2 rv_2 )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (mpz_div_qr_ret_ok retval rv_2 )) (PreH6 : (r_pre = n_pre)) (PreH7 : (n_pre <> 0)) (PreH8 : (zn_r_eq_n_read0 <> 0)) (PreH9 : (zd_r_eq_n_read0 <> 0)),
  (store_Z_read0 n_pre rv_2 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 qv_2 )
|--
  EX (qv: Z) (rv: Z),
  “ (r_pre = n_pre) ”
  &&  “ (zn_r_eq_n_read0 <> 0) ”
  &&  “ (mpz_div_qr_math 2 zn_r_eq_n_read0 zd_r_eq_n_read0 qv rv ) ”
  &&  (store_Z_read0 n_pre rv )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 qv )
.

Definition mpz_tdiv_r_return_wit_1_r_eq_n :=
forall (zd_r_eq_n: Z) (zn_r_eq_n: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (qv_2: Z) (rv_2: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (zd_r_eq_n <> 0)) (PreH3 : (zn_r_eq_n = ((qv_2 * zd_r_eq_n ) + rv_2 ))) (PreH4 : ((Zabs (rv_2)) < (Zabs (zd_r_eq_n)))) (PreH5 : (rv_2 = 0)),
  (store_Z n_pre rv_2 )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 qv_2 )
|--
  (EX (rv: Z) (qv: Z),
  “ (r_pre = n_pre) ”
  &&  “ (zd_r_eq_n <> 0) ”
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ”
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ”
  &&  “ (rv = 0) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n ))
  ||
  (EX (rv: Z) (qv: Z),
  “ (r_pre = n_pre) ”
  &&  “ (zd_r_eq_n <> 0) ”
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ”
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ”
  &&  “ (same_sign rv zn_r_eq_n ) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n ))
.

Definition mpz_tdiv_r_return_wit_2_r_eq_n :=
forall (zd_r_eq_n: Z) (zn_r_eq_n: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (qv_2: Z) (rv_2: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (zd_r_eq_n <> 0)) (PreH3 : (zn_r_eq_n = ((qv_2 * zd_r_eq_n ) + rv_2 ))) (PreH4 : ((Zabs (rv_2)) < (Zabs (zd_r_eq_n)))) (PreH5 : (same_sign rv_2 zn_r_eq_n )),
  (store_Z n_pre rv_2 )
  **  (store_Z d_pre zd_r_eq_n )
  **  (optional_store_Z 0 qv_2 )
|--
  (EX (rv: Z) (qv: Z),
  “ (r_pre = n_pre) ”
  &&  “ (zd_r_eq_n <> 0) ”
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ”
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ”
  &&  “ (rv = 0) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n ))
  ||
  (EX (rv: Z) (qv: Z),
  “ (r_pre = n_pre) ”
  &&  “ (zd_r_eq_n <> 0) ”
  &&  “ (zn_r_eq_n = ((qv * zd_r_eq_n ) + rv )) ”
  &&  “ ((Zabs (rv)) < (Zabs (zd_r_eq_n))) ”
  &&  “ (same_sign rv zn_r_eq_n ) ”
  &&  (store_Z n_pre rv )
  **  (store_Z d_pre zd_r_eq_n ))
.

Definition mpz_tdiv_r_return_wit_3_r_eq_n_read0 :=
(
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (qv_2: Z) (rv_2: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (zn_r_eq_n_read0 <> 0)) (PreH3 : (mpz_div_qr_math 2 zn_r_eq_n_read0 zd_r_eq_n_read0 qv_2 rv_2 )),
  (store_Z_read0 n_pre rv_2 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 qv_2 )
|--
  EX (qv: Z) (rv: Z),
  “ (r_pre = n_pre) ”
  &&  “ (mpz_div_qr_math 2 zn_r_eq_n_read0 zd_r_eq_n_read0 qv rv ) ”
  &&  (store_Z_read0 n_pre rv )
  **  (store_Z d_pre zd_r_eq_n_read0 )
) \/
(
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (qv_2: Z) (rv_2: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (zn_r_eq_n_read0 <> 0)) (PreH3 : (mpz_div_qr_math 2 zn_r_eq_n_read0 zd_r_eq_n_read0 qv_2 rv_2 )),
  (optional_store_Z 0 qv_2 )
|--
  TT && emp 
).

Definition mpz_tdiv_r_return_wit_3_r_eq_n_read0_split_goal_spatial :=
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (qv_2: Z) (rv_2: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (zn_r_eq_n_read0 <> 0)) (PreH3 : (mpz_div_qr_math 2 zn_r_eq_n_read0 zd_r_eq_n_read0 qv_2 rv_2 )),
  (optional_store_Z 0 qv_2 )
|--
  TT && emp 
.

Definition mpz_tdiv_r_partial_solve_wit_1_r_eq_n_pure :=
forall (zd_r_eq_n: Z) (zn_r_eq_n: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)),
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

Definition mpz_tdiv_r_partial_solve_wit_1_r_eq_n_aux :=
forall (zd_r_eq_n: Z) (zn_r_eq_n: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zd_r_eq_n <> 0)),
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

Definition mpz_tdiv_r_partial_solve_wit_1_r_eq_n := mpz_tdiv_r_partial_solve_wit_1_r_eq_n_pure -> mpz_tdiv_r_partial_solve_wit_1_r_eq_n_aux.

Definition mpz_tdiv_r_partial_solve_wit_2_r_eq_n_read0_pure :=
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zn_r_eq_n_read0 <> 0)) (PreH4 : (zd_r_eq_n_read0 <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 0 )
|--
  “ (0 = 0) ”
  &&  “ (r_pre = r_pre) ”
  &&  “ (n_pre = n_pre) ”
  &&  “ (d_pre = d_pre) ”
  &&  “ (2 = 2) ”
  &&  “ (r_pre = n_pre) ”
  &&  “ (n_pre <> 0) ”
  &&  “ (zn_r_eq_n_read0 <> 0) ”
  &&  “ (zd_r_eq_n_read0 <> 0) ”
  &&  “ (2 = 2) ”
.

Definition mpz_tdiv_r_partial_solve_wit_2_r_eq_n_read0_aux :=
forall (zd_r_eq_n_read0: Z) (zn_r_eq_n_read0: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre = n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (zn_r_eq_n_read0 <> 0)) (PreH4 : (zd_r_eq_n_read0 <> 0)),
  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 0 )
|--
  “ (0 = 0) ”
  &&  “ (r_pre = r_pre) ”
  &&  “ (n_pre = n_pre) ”
  &&  “ (d_pre = d_pre) ”
  &&  “ (2 = 2) ”
  &&  “ (r_pre = n_pre) ”
  &&  “ (n_pre <> 0) ”
  &&  “ (zn_r_eq_n_read0 <> 0) ”
  &&  “ (zd_r_eq_n_read0 <> 0) ”
  &&  “ (2 = 2) ”
  &&  “ (r_pre = n_pre) ”
  &&  “ (n_pre <> 0) ”
  &&  “ (zn_r_eq_n_read0 <> 0) ”
  &&  “ (zd_r_eq_n_read0 <> 0) ”
  &&  (store_Z n_pre zn_r_eq_n_read0 )
  **  (store_Z d_pre zd_r_eq_n_read0 )
  **  (optional_store_Z 0 0 )
.

Definition mpz_tdiv_r_partial_solve_wit_2_r_eq_n_read0 := mpz_tdiv_r_partial_solve_wit_2_r_eq_n_read0_pure -> mpz_tdiv_r_partial_solve_wit_2_r_eq_n_read0_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_tdiv_r_safety_wit_1_r_eq_n : mpz_tdiv_r_safety_wit_1_r_eq_n.
Axiom proof_of_mpz_tdiv_r_safety_wit_2_r_eq_n : mpz_tdiv_r_safety_wit_2_r_eq_n.
Axiom proof_of_mpz_tdiv_r_safety_wit_3_r_eq_n_read0 : mpz_tdiv_r_safety_wit_3_r_eq_n_read0.
Axiom proof_of_mpz_tdiv_r_safety_wit_4_r_eq_n_read0 : mpz_tdiv_r_safety_wit_4_r_eq_n_read0.
Axiom proof_of_mpz_tdiv_r_entail_wit_1_r_eq_n : mpz_tdiv_r_entail_wit_1_r_eq_n.
Axiom proof_of_mpz_tdiv_r_entail_wit_2_r_eq_n_read0 : mpz_tdiv_r_entail_wit_2_r_eq_n_read0.
Axiom proof_of_mpz_tdiv_r_entail_wit_3_r_eq_n : mpz_tdiv_r_entail_wit_3_r_eq_n.
Axiom proof_of_mpz_tdiv_r_entail_wit_4_r_eq_n_read0 : mpz_tdiv_r_entail_wit_4_r_eq_n_read0.
Axiom proof_of_mpz_tdiv_r_return_wit_1_r_eq_n : mpz_tdiv_r_return_wit_1_r_eq_n.
Axiom proof_of_mpz_tdiv_r_return_wit_2_r_eq_n : mpz_tdiv_r_return_wit_2_r_eq_n.
Axiom proof_of_mpz_tdiv_r_return_wit_3_r_eq_n_read0 : mpz_tdiv_r_return_wit_3_r_eq_n_read0.
Axiom proof_of_mpz_tdiv_r_partial_solve_wit_1_r_eq_n_pure : mpz_tdiv_r_partial_solve_wit_1_r_eq_n_pure.
Axiom proof_of_mpz_tdiv_r_partial_solve_wit_1_r_eq_n : mpz_tdiv_r_partial_solve_wit_1_r_eq_n.
Axiom proof_of_mpz_tdiv_r_partial_solve_wit_2_r_eq_n_read0_pure : mpz_tdiv_r_partial_solve_wit_2_r_eq_n_read0_pure.
Axiom proof_of_mpz_tdiv_r_partial_solve_wit_2_r_eq_n_read0 : mpz_tdiv_r_partial_solve_wit_2_r_eq_n_read0.

End VC_Correct.
