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
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import ge_gmp_array_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import ge_gmp_array_strategy_proof.

(*----- Function matrix_inverse_gmp -----*)

Definition matrix_inverse_gmp_safety_wit_1 := 
forall (Bres: matrix) (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> exists (Bres: matrix) , ((rep_matrix linv2 n_pre n_pre Bres ) /\ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres )))) (PreH4 : (a_pre <> 0)) (PreH5 : (inv_pre <> 0)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (a_pre <> inv_pre)) (PreH10 : (a_pre <> aug_pre)) (PreH11 : (a_pre <> x_pre)) (PreH12 : (inv_pre <> aug_pre)) (PreH13 : (inv_pre <> x_pre)) (PreH14 : (aug_pre <> x_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 256)) (PreH17 : (2 <= zp_low_level_spec)) (PreH18 : (prime zp_low_level_spec )) (PreH19 : (0 <= (n_pre * n_pre ))) (PreH20 : ((n_pre * n_pre ) <= INT_MAX)) (PreH21 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH22 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH23 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH24 : ((Zlength (laug_low_level_spec)) = (n_pre * (n_pre + 1 ) ))) (PreH25 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH26 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrix_inverse_gmp_safety_wit_2 := 
forall (Bres: matrix) (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval = 1) -> exists (Bres: matrix) , ((rep_matrix linv2 n_pre n_pre Bres ) /\ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres )))) (PreH5 : (a_pre <> 0)) (PreH6 : (inv_pre <> 0)) (PreH7 : (aug_pre <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (a_pre <> inv_pre)) (PreH11 : (a_pre <> aug_pre)) (PreH12 : (a_pre <> x_pre)) (PreH13 : (inv_pre <> aug_pre)) (PreH14 : (inv_pre <> x_pre)) (PreH15 : (aug_pre <> x_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 256)) (PreH18 : (2 <= zp_low_level_spec)) (PreH19 : (prime zp_low_level_spec )) (PreH20 : (0 <= (n_pre * n_pre ))) (PreH21 : ((n_pre * n_pre ) <= INT_MAX)) (PreH22 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH23 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH24 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH25 : ((Zlength (laug_low_level_spec)) = (n_pre * (n_pre + 1 ) ))) (PreH26 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition matrix_inverse_gmp_safety_wit_3 := 
forall (Bres: matrix) (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval = 1) -> exists (Bres: matrix) , ((rep_matrix linv2 n_pre n_pre Bres ) /\ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres )))) (PreH5 : (a_pre <> 0)) (PreH6 : (inv_pre <> 0)) (PreH7 : (aug_pre <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (a_pre <> inv_pre)) (PreH11 : (a_pre <> aug_pre)) (PreH12 : (a_pre <> x_pre)) (PreH13 : (inv_pre <> aug_pre)) (PreH14 : (inv_pre <> x_pre)) (PreH15 : (aug_pre <> x_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 256)) (PreH18 : (2 <= zp_low_level_spec)) (PreH19 : (prime zp_low_level_spec )) (PreH20 : (0 <= (n_pre * n_pre ))) (PreH21 : ((n_pre * n_pre ) <= INT_MAX)) (PreH22 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH23 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH24 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH25 : ((Zlength (laug_low_level_spec)) = (n_pre * (n_pre + 1 ) ))) (PreH26 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrix_inverse_gmp_return_wit_1 := 
(
forall (Bres_2: matrix) (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (lx2_2: (@list Z)) (laug2_2: (@list Z)) (linv2_2: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval = 1) -> exists (Bres_2: matrix) , ((rep_matrix linv2_2 n_pre n_pre Bres_2 ) /\ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres_2 )))) (PreH5 : (a_pre <> 0)) (PreH6 : (inv_pre <> 0)) (PreH7 : (aug_pre <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (a_pre <> inv_pre)) (PreH11 : (a_pre <> aug_pre)) (PreH12 : (a_pre <> x_pre)) (PreH13 : (inv_pre <> aug_pre)) (PreH14 : (inv_pre <> x_pre)) (PreH15 : (aug_pre <> x_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 256)) (PreH18 : (2 <= zp_low_level_spec)) (PreH19 : (prime zp_low_level_spec )) (PreH20 : (0 <= (n_pre * n_pre ))) (PreH21 : ((n_pre * n_pre ) <= INT_MAX)) (PreH22 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH23 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH24 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH25 : ((Zlength (laug_low_level_spec)) = (n_pre * (n_pre + 1 ) ))) (PreH26 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2_2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2_2 )
  **  (mpz_array x_pre n_pre lx2_2 )
|--
  EX (Bres: matrix)  (lx2: (@list Z))  (laug2: (@list Z))  (linv2: (@list Z)) ,
  “ (1 = 1) ” 
  &&  “ (rep_matrix linv2 n_pre n_pre Bres ) ” 
  &&  “ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
) \/
(
forall (Bres_2: matrix) (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (linv2_2: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval = 1) -> exists (Bres_2: matrix) , ((rep_matrix linv2_2 n_pre n_pre Bres_2 ) /\ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres_2 )))) (PreH5 : (a_pre <> 0)) (PreH6 : (inv_pre <> 0)) (PreH7 : (aug_pre <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (a_pre <> inv_pre)) (PreH11 : (a_pre <> aug_pre)) (PreH12 : (a_pre <> x_pre)) (PreH13 : (inv_pre <> aug_pre)) (PreH14 : (inv_pre <> x_pre)) (PreH15 : (aug_pre <> x_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 256)) (PreH18 : (2 <= zp_low_level_spec)) (PreH19 : (prime zp_low_level_spec )) (PreH20 : (0 <= (n_pre * n_pre ))) (PreH21 : ((n_pre * n_pre ) <= INT_MAX)) (PreH22 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH23 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH24 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH25 : ((Zlength (laug_low_level_spec)) = (n_pre * (n_pre + 1 ) ))) (PreH26 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  TT && emp 
|--
  EX (Bres: matrix) ,
  “ (rep_matrix linv2_2 (Zlength (lx_low_level_spec)) (Zlength (lx_low_level_spec)) Bres ) ” 
  &&  “ (matrix_inverse_success zp_low_level_spec (Zlength (lx_low_level_spec)) A_low_level_spec Bres ) ”
  &&  emp
).

Definition matrix_inverse_gmp_return_wit_2 := 
forall (Bres_2: matrix) (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (lx2_2: (@list Z)) (laug2_2: (@list Z)) (linv2_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval = 1) -> exists (Bres_2: matrix) , ((rep_matrix linv2_2 n_pre n_pre Bres_2 ) /\ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres_2 )))) (PreH5 : (a_pre <> 0)) (PreH6 : (inv_pre <> 0)) (PreH7 : (aug_pre <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (a_pre <> inv_pre)) (PreH11 : (a_pre <> aug_pre)) (PreH12 : (a_pre <> x_pre)) (PreH13 : (inv_pre <> aug_pre)) (PreH14 : (inv_pre <> x_pre)) (PreH15 : (aug_pre <> x_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 256)) (PreH18 : (2 <= zp_low_level_spec)) (PreH19 : (prime zp_low_level_spec )) (PreH20 : (0 <= (n_pre * n_pre ))) (PreH21 : ((n_pre * n_pre ) <= INT_MAX)) (PreH22 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH23 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH24 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH25 : ((Zlength (laug_low_level_spec)) = (n_pre * (n_pre + 1 ) ))) (PreH26 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2_2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2_2 )
  **  (mpz_array x_pre n_pre lx2_2 )
|--
  EX (lx2: (@list Z))  (laug2: (@list Z))  (linv2: (@list Z)) ,
  “ (0 = 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
.

Definition matrix_inverse_gmp_partial_solve_wit_1_pure := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH21 : ((Zlength (laug_low_level_spec)) = (n_pre * (n_pre + 1 ) ))) (PreH22 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (a_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> inv_pre) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (a_pre <> x_pre) ” 
  &&  “ (inv_pre <> aug_pre) ” 
  &&  “ (inv_pre <> x_pre) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (linv_low_level_spec)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ”
.

Definition matrix_inverse_gmp_partial_solve_wit_1_aux := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH21 : ((Zlength (laug_low_level_spec)) = (n_pre * (n_pre + 1 ) ))) (PreH22 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (a_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> inv_pre) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (a_pre <> x_pre) ” 
  &&  “ (inv_pre <> aug_pre) ” 
  &&  “ (inv_pre <> x_pre) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (linv_low_level_spec)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> inv_pre) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (a_pre <> x_pre) ” 
  &&  “ (inv_pre <> aug_pre) ” 
  &&  “ (inv_pre <> x_pre) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (linv_low_level_spec)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (laug_low_level_spec)) = (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition matrix_inverse_gmp_partial_solve_wit_1 := matrix_inverse_gmp_partial_solve_wit_1_pure -> matrix_inverse_gmp_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_matrix_inverse_gmp_safety_wit_1 : matrix_inverse_gmp_safety_wit_1.
Axiom proof_of_matrix_inverse_gmp_safety_wit_2 : matrix_inverse_gmp_safety_wit_2.
Axiom proof_of_matrix_inverse_gmp_safety_wit_3 : matrix_inverse_gmp_safety_wit_3.
Axiom proof_of_matrix_inverse_gmp_return_wit_1 : matrix_inverse_gmp_return_wit_1.
Axiom proof_of_matrix_inverse_gmp_return_wit_2 : matrix_inverse_gmp_return_wit_2.
Axiom proof_of_matrix_inverse_gmp_partial_solve_wit_1_pure : matrix_inverse_gmp_partial_solve_wit_1_pure.
Axiom proof_of_matrix_inverse_gmp_partial_solve_wit_1 : matrix_inverse_gmp_partial_solve_wit_1.

End VC_Correct.
