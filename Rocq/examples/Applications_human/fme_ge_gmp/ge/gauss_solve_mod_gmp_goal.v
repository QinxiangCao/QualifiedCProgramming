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

(*----- Function gauss_solve_mod_gmp -----*)

Definition gauss_solve_mod_gmp_safety_wit_1 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH10 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH11 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) (PreH13 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_2 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH10 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH11 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) (PreH13 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gauss_solve_mod_gmp_safety_wit_3 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH10 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH11 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) (PreH13 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "cols" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_4 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k <= n_pre)) (PreH21 : (rep_matrix lcur n_pre cols M )) (PreH22 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  ((( &( "ps" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |-> k)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_5 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= ((pivot * cols ) + k ))) (PreH24 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH29 : (ps = 1)) (PreH30 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_6 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= ((pivot * cols ) + k ))) (PreH24 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH29 : (ps = (-1))) (PreH30 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_7 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (pivot >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH28 : (ps = 0)) (PreH29 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_8 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (pivot >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH28 : (ps = 1)) (PreH29 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_9 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (pivot >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH28 : (ps = 1)) (PreH29 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_10 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (pivot >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH28 : (ps = (-1))) (PreH29 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_11 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (pivot >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH28 : (ps = (-1))) (PreH29 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_12 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= ((pivot * cols ) + k ))) (PreH24 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH29 : (ps = (-1))) (PreH30 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_13 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= ((pivot * cols ) + k ))) (PreH24 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH29 : (ps = 1)) (PreH30 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_14 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= ((pivot * cols ) + k ))) (PreH24 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH29 : (ps = 0)) (PreH30 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_15 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (ps = 0)) (PreH2 : (pivot < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (0 <= ((pivot * cols ) + k ))) (PreH25 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH29 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH30 : (ps = (-1))) (PreH31 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_16 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (ps = 0)) (PreH2 : (pivot < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (0 <= ((pivot * cols ) + k ))) (PreH25 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH29 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH30 : (ps = 1)) (PreH31 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_17 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (ps <> 0)) (PreH2 : (pivot < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (0 <= ((pivot * cols ) + k ))) (PreH25 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH29 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH30 : (ps = 0)) (PreH31 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_18 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (ps = 0)) (PreH2 : (pivot < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (0 <= ((pivot * cols ) + k ))) (PreH25 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH29 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH30 : (ps = 0)) (PreH31 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "pidx" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (((pivot * cols ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((pivot * cols ) + k )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_19 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (ps = 0)) (PreH2 : (pivot < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (0 <= ((pivot * cols ) + k ))) (PreH25 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH29 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH30 : (ps = 0)) (PreH31 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "pidx" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ ((pivot * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot * cols )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_20 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) < 0)) (PreH2 : (retval = (-1))) (PreH3 : (ps = 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = 0)) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot * cols ) + k ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> retval)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_21 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) = 0)) (PreH2 : (retval = 0)) (PreH3 : (ps = 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = 0)) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot * cols ) + k ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> retval)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_22 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) > 0)) (PreH2 : (retval = 1)) (PreH3 : (ps = 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = 0)) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot * cols ) + k ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> retval)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_23 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (ps = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot <= n_pre)) (PreH27 : (0 <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH32 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH33 : (ps = 0)) (PreH34 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot * cols ) + k ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> retval)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_24 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (ps = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot <= n_pre)) (PreH27 : (0 <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH32 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH33 : (ps = 0)) (PreH34 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot * cols ) + k ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> retval)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_25 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (ps = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot <= n_pre)) (PreH27 : (0 <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH32 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH33 : (ps = 0)) (PreH34 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot * cols ) + k ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> retval)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_26 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (ps = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot <= n_pre)) (PreH27 : (0 <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH32 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH33 : (ps = 0)) (PreH34 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot * cols ) + k ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> retval)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ ((pivot + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot + 1 )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_27 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (ps = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot <= n_pre)) (PreH27 : (0 <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH32 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH33 : (ps = 0)) (PreH34 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot * cols ) + k ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> retval)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gauss_solve_mod_gmp_safety_wit_28 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot <> n_pre)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (pivot >= n_pre)) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH29 : (ps = 0)) (PreH30 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_29 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot <> n_pre)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (0 <= ((pivot * cols ) + k ))) (PreH25 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH29 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH30 : (ps = 0)) (PreH31 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_30 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot = n_pre)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (0 <= ((pivot * cols ) + k ))) (PreH25 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH29 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH30 : (ps = 0)) (PreH31 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_31 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot = n_pre)) (PreH2 : (ps <> 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot <= n_pre)) (PreH25 : (0 <= ((pivot * cols ) + k ))) (PreH26 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (pivot * cols ))) (PreH28 : ((pivot * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH30 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH31 : (ps = 1)) (PreH32 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH33 : (rep_matrix lcur n_pre cols M )) (PreH34 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH35 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_32 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot = n_pre)) (PreH2 : (ps <> 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot <= n_pre)) (PreH25 : (0 <= ((pivot * cols ) + k ))) (PreH26 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (pivot * cols ))) (PreH28 : ((pivot * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH30 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH31 : (ps = (-1))) (PreH32 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH33 : (rep_matrix lcur n_pre cols M )) (PreH34 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH35 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_33 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot = n_pre)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (pivot >= n_pre)) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH29 : (ps = 0)) (PreH30 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "ps" ) )) # Int  |-> ps)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_34 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (ps_addr_v: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= ((k * cols ) + k ))) (PreH26 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (k * cols ))) (PreH28 : ((k * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((k * cols ) + k ))) (PreH30 : (((k * cols ) + k ) <= INT_MAX)) (PreH31 : (rep_matrix l1 n_pre cols M1 )) (PreH32 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH34 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH35 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((( &( "factor" ) )) # Ptr  |-> retval_3)
  **  ((( &( "inv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "pv" ) )) # Ptr  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k * cols ) + k )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_35 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (ps_addr_v: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= ((k * cols ) + k ))) (PreH26 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (k * cols ))) (PreH28 : ((k * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((k * cols ) + k ))) (PreH30 : (((k * cols ) + k ) <= INT_MAX)) (PreH31 : (rep_matrix l1 n_pre cols M1 )) (PreH32 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH34 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH35 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((( &( "factor" ) )) # Ptr  |-> retval_3)
  **  ((( &( "inv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "pv" ) )) # Ptr  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * cols )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_36 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (ps_addr_v: Z) (zinv: Z) (M2: matrix) (l2: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= zinv)) (PreH26 : (zinv < zp_low_level_spec)) (PreH27 : (rep_matrix l2 n_pre cols M2 )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M2 )) (PreH29 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M2 )) (PreH30 : (pivot_column_prefix_ready zp_low_level_spec n_pre k 0 M2 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * cols ) l2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_37 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (ps_addr_v: Z) (zfactor: Z) (lcur2: (@list Z)) (Mcur: matrix) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot < n_pre)) (PreH26 : (0 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (i >= n_pre)) (PreH29 : (INT_MIN <= (i * cols ))) (PreH30 : ((i * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((i * cols ) + k ))) (PreH32 : (((i * cols ) + k ) <= INT_MAX)) (PreH33 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH36 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_38 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (ps_addr_v: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  ((( &( "fs" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ (((i * cols ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * cols ) + k )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_39 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (ps_addr_v: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  ((( &( "fs" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ ((i * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * cols )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_40 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (ps_addr_v: Z) (retval: Z) (PreH1 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) < 0)) (PreH2 : (retval = (-1))) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i < n_pre)) (PreH26 : (i <> k)) (PreH27 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH28 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH29 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH30 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH31 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH32 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
  **  ((( &( "fs" ) )) # Int  |->_)
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_41 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (ps_addr_v: Z) (retval: Z) (PreH1 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) = 0)) (PreH2 : (retval = 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i < n_pre)) (PreH26 : (i <> k)) (PreH27 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH28 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH29 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH30 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH31 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH32 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
  **  ((( &( "fs" ) )) # Int  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_42 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (ps_addr_v: Z) (retval: Z) (PreH1 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) > 0)) (PreH2 : (retval = 1)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i < n_pre)) (PreH26 : (i <> k)) (PreH27 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH28 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH29 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH30 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH31 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH32 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
  **  ((( &( "fs" ) )) # Int  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_43 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (ps_addr_v: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (pv <> 0)) (PreH9 : (inv <> 0)) (PreH10 : (factor <> 0)) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (i <> k)) (PreH28 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH29 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH30 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
  **  ((( &( "fs" ) )) # Int  |-> retval)
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_44 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (ps_addr_v: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (pv <> 0)) (PreH9 : (inv <> 0)) (PreH10 : (factor <> 0)) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (i <> k)) (PreH28 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH29 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH30 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
  **  ((( &( "fs" ) )) # Int  |-> retval)
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_45 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (ps_addr_v: Z) (retval: Z) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur) (k) (i) ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)))) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur) (k) (i) ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)))) )) (PreH3 : (retval <> 0)) (PreH4 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) > 0)) (PreH5 : (retval = 1)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (pv <> 0)) (PreH11 : (inv <> 0)) (PreH12 : (factor <> 0)) (PreH13 : (cols = (n_pre + 1 ))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 256)) (PreH16 : (2 <= zp_low_level_spec)) (PreH17 : (prime zp_low_level_spec )) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i < n_pre)) (PreH29 : (i <> k)) (PreH30 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH31 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH32 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH33 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH34 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH35 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_46 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (ps_addr_v: Z) (retval: Z) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur) (k) (i) ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)))) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur) (k) (i) ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)))) )) (PreH3 : (retval <> 0)) (PreH4 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) > 0)) (PreH5 : (retval = 1)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (pv <> 0)) (PreH11 : (inv <> 0)) (PreH12 : (factor <> 0)) (PreH13 : (cols = (n_pre + 1 ))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 256)) (PreH16 : (2 <= zp_low_level_spec)) (PreH17 : (prime zp_low_level_spec )) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i < n_pre)) (PreH29 : (i <> k)) (PreH30 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH31 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH32 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH33 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH34 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH35 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gauss_solve_mod_gmp_safety_wit_47 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (ps_addr_v: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (pv <> 0)) (PreH9 : (inv <> 0)) (PreH10 : (factor <> 0)) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (i <> k)) (PreH28 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH29 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH30 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_48 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (ps_addr_v: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (pv <> 0)) (PreH9 : (inv <> 0)) (PreH10 : (factor <> 0)) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (i <> k)) (PreH28 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH29 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH30 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gauss_solve_mod_gmp_safety_wit_49 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (ps_addr_v: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i = k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_50 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (ps_addr_v: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i = k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gauss_solve_mod_gmp_safety_wit_51 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (ps_addr_v: Z) (i_addr_v: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_52 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (ps_addr_v: Z) (i_addr_v: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gauss_solve_mod_gmp_safety_wit_53 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k_addr_v: Z) (Mfin: matrix) (lfin: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "k" ) )) # Int  |-> k_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gauss_solve_mod_gmp_safety_wit_54 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (k_addr_v: Z) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (i >= n_pre)) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH27 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH28 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur )
  **  ((( &( "k" ) )) # Int  |-> k_addr_v)
|--
  “ False ”
.

Definition gauss_solve_mod_gmp_safety_wit_55 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (k_addr_v: Z) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= ((i * cols ) + n_pre ))) (PreH24 : (((i * cols ) + n_pre ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (i * cols ))) (PreH26 : ((i * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH28 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH29 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur )
  **  ((( &( "k" ) )) # Int  |-> k_addr_v)
|--
  “ (((i * cols ) + n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * cols ) + n_pre )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_56 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (k_addr_v: Z) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= ((i * cols ) + n_pre ))) (PreH24 : (((i * cols ) + n_pre ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (i * cols ))) (PreH26 : ((i * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH28 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH29 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur )
  **  ((( &( "k" ) )) # Int  |-> k_addr_v)
|--
  “ ((i * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * cols )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_57 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (k_addr_v: Z) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= ((i * cols ) + n_pre ))) (PreH24 : (((i * cols ) + n_pre ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (i * cols ))) (PreH26 : ((i * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH28 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH29 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  (mpz_array x_pre n_pre (replace_Znth (i) ((Znth (((i * cols ) + n_pre )) (lfin) (0))) (lxcur)) )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  ((( &( "k" ) )) # Int  |-> k_addr_v)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition gauss_solve_mod_gmp_safety_wit_58 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (k_addr_v: Z) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= ((i * cols ) + n_pre ))) (PreH24 : (((i * cols ) + n_pre ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (i * cols ))) (PreH26 : ((i * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH28 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH29 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  (mpz_array x_pre n_pre (replace_Znth (i) ((Znth (((i * cols ) + n_pre )) (lfin) (0))) (lxcur)) )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  ((( &( "k" ) )) # Int  |-> k_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gauss_solve_mod_gmp_safety_wit_59 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (k_addr_v: Z) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (i >= n_pre)) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH27 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH28 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur )
  **  ((( &( "k" ) )) # Int  |-> k_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gauss_solve_mod_gmp_safety_wit_60 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (k_addr_v: Z) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= ((i * cols ) + n_pre ))) (PreH24 : (((i * cols ) + n_pre ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (i * cols ))) (PreH26 : ((i * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH28 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH29 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur )
  **  ((( &( "k" ) )) # Int  |-> k_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gauss_solve_mod_gmp_entail_wit_1 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH10 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH11 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) (PreH13 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (lcur: (@list Z))  (M: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre 0 M0_low_level_spec M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH10 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH11 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) (PreH13 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) ,
  TT && emp 
|--
  EX (M: matrix) ,
  “ (0 <= 0) ” 
  &&  “ (rep_matrix l_low_level_spec (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) M ) ” 
  &&  “ (gauss_inv zp_low_level_spec (Zlength (lx_low_level_spec)) 0 M0_low_level_spec M ) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_2 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k <= n_pre)) (PreH21 : (rep_matrix lcur n_pre cols M )) (PreH22 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((0 <> 0) -> ((k < n_pre) /\ ((Znth (((k * cols ) + k )) (lcur) (0)) <> 0))) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (pivot_search_zero_prefix n_pre k k M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k <= n_pre)) (PreH21 : (rep_matrix lcur n_pre cols M )) (PreH22 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  TT && emp 
|--
  “ (pivot_search_zero_prefix n_pre k k M ) ” 
  &&  “ (((k * (n_pre + 1 ) ) + k ) < (n_pre * (n_pre + 1 ) )) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k <= n_pre)) (PreH21 : (rep_matrix lcur n_pre cols M )) (PreH22 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (pivot_search_zero_prefix n_pre k k M )
.

Definition gauss_solve_mod_gmp_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k <= n_pre)) (PreH21 : (rep_matrix lcur n_pre cols M )) (PreH22 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (((k * (n_pre + 1 ) ) + k ) < (n_pre * (n_pre + 1 ) ))
.

Definition gauss_solve_mod_gmp_entail_wit_3_1 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (ps = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot <= n_pre)) (PreH27 : (0 <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH32 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH33 : (ps = 0)) (PreH34 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  (“ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= (pivot + 1 )) ” 
  &&  “ ((pivot + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((pivot + 1 ) * cols ) + k )) ” 
  &&  “ ((((pivot + 1 ) * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= ((pivot + 1 ) * cols )) ” 
  &&  “ (((pivot + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((pivot + 1 ) * cols ) + k )) ” 
  &&  “ ((((pivot + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((retval <> 0) -> (((pivot + 1 ) < n_pre) /\ ((Znth ((((pivot + 1 ) * cols ) + k )) (lcur) (0)) <> 0))) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (pivot_search_zero_prefix n_pre k (pivot + 1 ) M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
  ||
  (“ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= (pivot + 1 )) ” 
  &&  “ ((pivot + 1 ) <= n_pre) ” 
  &&  “ ((pivot + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((pivot + 1 ) * cols )) ” 
  &&  “ (((pivot + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((pivot + 1 ) * cols ) + k )) ” 
  &&  “ ((((pivot + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((retval <> 0) -> (((pivot + 1 ) < n_pre) /\ ((Znth ((((pivot + 1 ) * cols ) + k )) (lcur) (0)) <> 0))) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (pivot_search_zero_prefix n_pre k (pivot + 1 ) M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
.

Definition gauss_solve_mod_gmp_entail_wit_3_2 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (ps = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot <= n_pre)) (PreH27 : (0 <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH32 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH33 : (ps = 0)) (PreH34 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot <= n_pre) ” 
  &&  “ (0 <= ((pivot * cols ) + k )) ” 
  &&  “ (((pivot * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (pivot * cols )) ” 
  &&  “ ((pivot * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot * cols ) + k )) ” 
  &&  “ (((pivot * cols ) + k ) <= INT_MAX) ” 
  &&  “ (retval = (-1)) ” 
  &&  “ ((retval <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0))) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (pivot_search_zero_prefix n_pre k pivot M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_entail_wit_3_3 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (ps = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot <= n_pre)) (PreH27 : (0 <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH32 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH33 : (ps = 0)) (PreH34 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot <= n_pre) ” 
  &&  “ (0 <= ((pivot * cols ) + k )) ” 
  &&  “ (((pivot * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (pivot * cols )) ” 
  &&  “ ((pivot * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot * cols ) + k )) ” 
  &&  “ (((pivot * cols ) + k ) <= INT_MAX) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((retval <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0))) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (pivot_search_zero_prefix n_pre k pivot M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_entail_wit_4_1 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot <> k)) (PreH2 : (pivot <> n_pre)) (PreH3 : (ps <> 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = 1)) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (pivot_search_zero_prefix n_pre k pivot M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot <> k)) (PreH2 : (pivot <> n_pre)) (PreH3 : (ps <> 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = 1)) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
).

Definition gauss_solve_mod_gmp_entail_wit_4_1_split_goal_spatial := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot <> k)) (PreH2 : (pivot <> n_pre)) (PreH3 : (ps <> 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = 1)) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
.

Definition gauss_solve_mod_gmp_entail_wit_4_2 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot <> k)) (PreH2 : (pivot <> n_pre)) (PreH3 : (ps <> 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = (-1))) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (pivot_search_zero_prefix n_pre k pivot M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot <> k)) (PreH2 : (pivot <> n_pre)) (PreH3 : (ps <> 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = (-1))) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
).

Definition gauss_solve_mod_gmp_entail_wit_4_2_split_goal_spatial := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot <> k)) (PreH2 : (pivot <> n_pre)) (PreH3 : (ps <> 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = (-1))) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
.

Definition gauss_solve_mod_gmp_entail_wit_5_1 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M) (k) (pivot)) )) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH12 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH13 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH14 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (k <= pivot)) (PreH19 : (0 <= pivot)) (PreH20 : (pivot < n_pre)) (PreH21 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)) (PreH22 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH23 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH24 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (l1: (@list Z))  (M1: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M) (k) (pivot)) )) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH12 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH13 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH14 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (k <= pivot)) (PreH19 : (0 <= pivot)) (PreH20 : (pivot < n_pre)) (PreH21 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)) (PreH22 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH23 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH24 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  TT && emp 
|--
  EX (M1: matrix) ,
  “ (0 <= ((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) ” 
  &&  “ (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k ) < ((Zlength (lx_low_level_spec)) * ((Zlength (lx_low_level_spec)) + 1 ) )) ” 
  &&  “ (INT_MIN <= (k * ((Zlength (lx_low_level_spec)) + 1 ) )) ” 
  &&  “ ((k * ((Zlength (lx_low_level_spec)) + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) ” 
  &&  “ (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l2 (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec (Zlength (lx_low_level_spec)) k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l2) (0))) ” 
  &&  “ ((Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l2) (0)) < zp_low_level_spec) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_5_2 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot = k)) (PreH2 : (pivot <> n_pre)) (PreH3 : (ps <> 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = 1)) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (l1: (@list Z))  (M1: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot = k)) (PreH2 : (pivot <> n_pre)) (PreH3 : (ps <> 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = 1)) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  TT && emp 
|--
  EX (M1: matrix) ,
  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (0 <= ((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) ” 
  &&  “ (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k ) < ((Zlength (lx_low_level_spec)) * ((Zlength (lx_low_level_spec)) + 1 ) )) ” 
  &&  “ (INT_MIN <= (k * ((Zlength (lx_low_level_spec)) + 1 ) )) ” 
  &&  “ ((k * ((Zlength (lx_low_level_spec)) + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) ” 
  &&  “ (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lcur (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec (Zlength (lx_low_level_spec)) k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur) (0))) ” 
  &&  “ ((Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur) (0)) < zp_low_level_spec) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_5_3 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot = k)) (PreH2 : (pivot <> n_pre)) (PreH3 : (ps <> 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = (-1))) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (l1: (@list Z))  (M1: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot = k)) (PreH2 : (pivot <> n_pre)) (PreH3 : (ps <> 0)) (PreH4 : (pivot < n_pre)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot <= n_pre)) (PreH26 : (0 <= ((pivot * cols ) + k ))) (PreH27 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH31 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH32 : (ps = (-1))) (PreH33 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  TT && emp 
|--
  EX (M1: matrix) ,
  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (0 <= ((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) ” 
  &&  “ (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k ) < ((Zlength (lx_low_level_spec)) * ((Zlength (lx_low_level_spec)) + 1 ) )) ” 
  &&  “ (INT_MIN <= (k * ((Zlength (lx_low_level_spec)) + 1 ) )) ” 
  &&  “ ((k * ((Zlength (lx_low_level_spec)) + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) ” 
  &&  “ (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lcur (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec (Zlength (lx_low_level_spec)) k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur) (0))) ” 
  &&  “ ((Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur) (0)) < zp_low_level_spec) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_6 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (inv: Z) (PreH1 : (mod_inverse_spec zp_low_level_spec (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l1) (0)) inv )) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot < n_pre)) (PreH26 : (0 <= ((k * cols ) + k ))) (PreH27 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (k * cols ))) (PreH29 : ((k * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((k * cols ) + k ))) (PreH31 : (((k * cols ) + k ) <= INT_MAX)) (PreH32 : (rep_matrix l1 n_pre cols M1 )) (PreH33 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH34 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH35 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH36 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  (store_Z retval_2 inv )
  **  (store_Z retval (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l1) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval_3 0 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (zinv: Z) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_2 zinv )
  **  (store_Z retval_3 0 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (inv: Z) (PreH1 : (mod_inverse_spec zp_low_level_spec (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l1) (0)) inv )) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (aug_pre <> x_pre)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot < n_pre)) (PreH26 : (0 <= ((k * cols ) + k ))) (PreH27 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (k * cols ))) (PreH29 : ((k * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((k * cols ) + k ))) (PreH31 : (((k * cols ) + k ) <= INT_MAX)) (PreH32 : (rep_matrix l1 n_pre cols M1 )) (PreH33 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH34 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH35 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH36 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  (store_Z retval_2 inv )
  **  (store_Z retval (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l1) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval_3 0 )
|--
  EX (zinv: Z) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_2 zinv )
  **  (store_Z retval_3 0 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l1 )
).

Definition gauss_solve_mod_gmp_entail_wit_7 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M1: matrix) (l1: (@list Z)) (zinv_2: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (l2_2: (@list Z)) (PreH1 : (rep_matrix l2_2 n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M1) (k) (zinv_2)) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M1) (k) (zinv_2)) )) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot < n_pre)) (PreH24 : (0 <= zinv_2)) (PreH25 : (zinv_2 < zp_low_level_spec)) (PreH26 : (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv_2 )) (PreH27 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH28 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 )) (PreH29 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv zinv_2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2_2 )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z factor 0 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (l2: (@list Z))  (M2: matrix)  (zinv: Z) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (rep_matrix l2 n_pre cols M2 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M2 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M2 ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k 0 M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * cols ) l2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M1: matrix) (l1: (@list Z)) (zinv_2: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (l2_2: (@list Z)) (PreH1 : (rep_matrix l2_2 n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M1) (k) (zinv_2)) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M1) (k) (zinv_2)) )) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot < n_pre)) (PreH24 : (0 <= zinv_2)) (PreH25 : (zinv_2 < zp_low_level_spec)) (PreH26 : (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv_2 )) (PreH27 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH28 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 )) (PreH29 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) ,
  TT && emp 
|--
  EX (M2: matrix) ,
  “ (rep_matrix l2_2 (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) M2 ) ” 
  &&  “ (mat_mod zp_low_level_spec (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) M2 ) ” 
  &&  “ (gauss_inv zp_low_level_spec (Zlength (lx_low_level_spec)) k M0_low_level_spec M2 ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec (Zlength (lx_low_level_spec)) k 0 M2 ) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_8 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (zinv: Z) (M2: matrix) (l2: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= zinv)) (PreH26 : (zinv < zp_low_level_spec)) (PreH27 : (rep_matrix l2 n_pre cols M2 )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M2 )) (PreH29 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M2 )) (PreH30 : (pivot_column_prefix_ready zp_low_level_spec n_pre k 0 M2 )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * cols ) l2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= ((0 * cols ) + k )) ” 
  &&  “ (((0 * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (0 * cols )) ” 
  &&  “ ((0 * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((0 * cols ) + k )) ” 
  &&  “ (((0 * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k 0 Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (zinv: Z) (M2: matrix) (l2: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= zinv)) (PreH26 : (zinv < zp_low_level_spec)) (PreH27 : (rep_matrix l2 n_pre cols M2 )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M2 )) (PreH29 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M2 )) (PreH30 : (pivot_column_prefix_ready zp_low_level_spec n_pre k 0 M2 )) ,
  TT && emp 
|--
  EX (Mcur: matrix) ,
  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((0 * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) ” 
  &&  “ (((0 * ((Zlength (lx_low_level_spec)) + 1 ) ) + k ) < ((Zlength (lx_low_level_spec)) * ((Zlength (lx_low_level_spec)) + 1 ) )) ” 
  &&  “ (INT_MIN <= (0 * ((Zlength (lx_low_level_spec)) + 1 ) )) ” 
  &&  “ ((0 * ((Zlength (lx_low_level_spec)) + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((0 * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) ” 
  &&  “ (((0 * ((Zlength (lx_low_level_spec)) + 1 ) ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l2 (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) Mcur ) ” 
  &&  “ (gauss_inv zp_low_level_spec (Zlength (lx_low_level_spec)) k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec (Zlength (lx_low_level_spec)) k 0 Mcur ) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_9 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <> k) ” 
  &&  “ (0 <= (Znth (((i * cols ) + k )) (lcur2) (0))) ” 
  &&  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ ((Znth (((i * (n_pre + 1 ) ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (0 <= (Znth (((i * (n_pre + 1 ) ) + k )) (lcur2) (0))) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
).

Definition gauss_solve_mod_gmp_entail_wit_9_split_goal_1 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ ((Znth (((i * (n_pre + 1 ) ) + k )) (lcur2) (0)) < zp_low_level_spec) ”
.

Definition gauss_solve_mod_gmp_entail_wit_9_split_goal_2 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ (0 <= (Znth (((i * (n_pre + 1 ) ) + k )) (lcur2) (0))) ”
.

Definition gauss_solve_mod_gmp_entail_wit_9_split_goal_spatial := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
.

Definition gauss_solve_mod_gmp_entail_wit_10_1 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (retval: Z) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur) (k) (i) ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)))) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur) (k) (i) ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)))) )) (PreH3 : (retval <> 0)) (PreH4 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) > 0)) (PreH5 : (retval = 1)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (aug_pre <> x_pre)) (PreH10 : (pv <> 0)) (PreH11 : (inv <> 0)) (PreH12 : (factor <> 0)) (PreH13 : (cols = (n_pre + 1 ))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 256)) (PreH16 : (2 <= zp_low_level_spec)) (PreH17 : (prime zp_low_level_spec )) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i < n_pre)) (PreH29 : (i <> k)) (PreH30 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH31 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH32 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH33 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH34 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH35 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  (EX (zfactor2: Z)  (lnext: (@list Z))  (Mnext: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lnext n_pre cols Mnext ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mnext ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mnext ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mnext ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor2 )
  **  (mpz_array aug_pre (n_pre * cols ) lnext )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
  ||
  (EX (zfactor2: Z)  (lnext: (@list Z))  (Mnext: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lnext n_pre cols Mnext ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mnext ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mnext ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mnext ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor2 )
  **  (mpz_array aug_pre (n_pre * cols ) lnext )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
.

Definition gauss_solve_mod_gmp_entail_wit_10_2 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (pv <> 0)) (PreH9 : (inv <> 0)) (PreH10 : (factor <> 0)) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (i <> k)) (PreH28 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH29 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH30 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  (EX (zfactor2: Z)  (lnext: (@list Z))  (Mnext: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lnext n_pre cols Mnext ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mnext ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mnext ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mnext ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor2 )
  **  (mpz_array aug_pre (n_pre * cols ) lnext )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
  ||
  (EX (zfactor2: Z)  (lnext: (@list Z))  (Mnext: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lnext n_pre cols Mnext ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mnext ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mnext ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mnext ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor2 )
  **  (mpz_array aug_pre (n_pre * cols ) lnext )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
.

Definition gauss_solve_mod_gmp_entail_wit_10_3 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i = k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  (EX (zfactor2: Z)  (lnext: (@list Z))  (Mnext: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lnext n_pre cols Mnext ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mnext ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mnext ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mnext ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor2 )
  **  (mpz_array aug_pre (n_pre * cols ) lnext )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
  ||
  (EX (zfactor2: Z)  (lnext: (@list Z))  (Mnext: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lnext n_pre cols Mnext ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mnext ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mnext ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mnext ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor2 )
  **  (mpz_array aug_pre (n_pre * cols ) lnext )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
.

Definition gauss_solve_mod_gmp_entail_wit_11_1 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mnext: matrix) (lnext: (@list Z)) (zfactor2: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (i >= n_pre)) (PreH28 : (INT_MIN <= (i * cols ))) (PreH29 : ((i * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((i * cols ) + k ))) (PreH31 : (((i * cols ) + k ) <= INT_MAX)) (PreH32 : (rep_matrix lnext n_pre cols Mnext )) (PreH33 : (mat_mod zp_low_level_spec n_pre cols Mnext )) (PreH34 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mnext )) (PreH35 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mnext )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor2 )
  **  (mpz_array aug_pre (n_pre * cols ) lnext )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  (EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (INT_MIN <= (i * cols )) ” 
  &&  “ ((i * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((i * cols ) + k )) ” 
  &&  “ (((i * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
  ||
  (EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= ((i * cols ) + k )) ” 
  &&  “ (((i * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (i * cols )) ” 
  &&  “ ((i * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((i * cols ) + k )) ” 
  &&  “ (((i * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
.

Definition gauss_solve_mod_gmp_entail_wit_11_2 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mnext: matrix) (lnext: (@list Z)) (zfactor2: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (0 <= ((i * cols ) + k ))) (PreH28 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (i * cols ))) (PreH30 : ((i * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((i * cols ) + k ))) (PreH32 : (((i * cols ) + k ) <= INT_MAX)) (PreH33 : (rep_matrix lnext n_pre cols Mnext )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols Mnext )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mnext )) (PreH36 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mnext )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor2 )
  **  (mpz_array aug_pre (n_pre * cols ) lnext )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  (EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (INT_MIN <= (i * cols )) ” 
  &&  “ ((i * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((i * cols ) + k )) ” 
  &&  “ (((i * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
  ||
  (EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= ((i * cols ) + k )) ” 
  &&  “ (((i * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (i * cols )) ” 
  &&  “ ((i * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((i * cols ) + k )) ” 
  &&  “ (((i * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec ))
.

Definition gauss_solve_mod_gmp_entail_wit_12_1 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (zfactor: Z) (lcur2: (@list Z)) (Mcur: matrix) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot < n_pre)) (PreH26 : (0 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (i >= n_pre)) (PreH29 : (INT_MIN <= (i * cols ))) (PreH30 : ((i * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((i * cols ) + k ))) (PreH32 : (((i * cols ) + k ) <= INT_MAX)) (PreH33 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH36 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (zfactor3: Z)  (ldone: (@list Z))  (Mdone: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone ) ” 
  &&  “ (pivot_column_ready zp_low_level_spec n_pre k Mdone ) ” 
  &&  “ (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor3 )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (lcur2: (@list Z)) (Mcur: matrix) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot < n_pre)) (PreH26 : (0 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (i >= n_pre)) (PreH29 : (INT_MIN <= (i * cols ))) (PreH30 : ((i * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((i * cols ) + k ))) (PreH32 : (((i * cols ) + k ) <= INT_MAX)) (PreH33 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH35 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH36 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  TT && emp 
|--
  EX (Mdone: matrix) ,
  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (rep_matrix lcur2 (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) Mdone ) ” 
  &&  “ (mat_mod zp_low_level_spec (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec (Zlength (lx_low_level_spec)) k M0_low_level_spec Mdone ) ” 
  &&  “ (pivot_column_ready zp_low_level_spec (Zlength (lx_low_level_spec)) k Mdone ) ” 
  &&  “ (rref_prefix_mod zp_low_level_spec (Zlength (lx_low_level_spec)) (k + 1 ) Mdone ) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_12_2 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (zfactor: Z) (lcur2: (@list Z)) (Mcur: matrix) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot < n_pre)) (PreH26 : (0 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (0 <= ((i * cols ) + k ))) (PreH29 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH30 : (INT_MIN <= (i * cols ))) (PreH31 : ((i * cols ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((i * cols ) + k ))) (PreH33 : (((i * cols ) + k ) <= INT_MAX)) (PreH34 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH36 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH37 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (zfactor3: Z)  (ldone: (@list Z))  (Mdone: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone ) ” 
  &&  “ (pivot_column_ready zp_low_level_spec n_pre k Mdone ) ” 
  &&  “ (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor3 )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (lcur2: (@list Z)) (Mcur: matrix) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (k <= pivot)) (PreH25 : (pivot < n_pre)) (PreH26 : (0 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (0 <= ((i * cols ) + k ))) (PreH29 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH30 : (INT_MIN <= (i * cols ))) (PreH31 : ((i * cols ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((i * cols ) + k ))) (PreH33 : (((i * cols ) + k ) <= INT_MAX)) (PreH34 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH36 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH37 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  TT && emp 
|--
  EX (Mdone: matrix) ,
  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (rep_matrix lcur2 (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) Mdone ) ” 
  &&  “ (mat_mod zp_low_level_spec (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec (Zlength (lx_low_level_spec)) k M0_low_level_spec Mdone ) ” 
  &&  “ (pivot_column_ready zp_low_level_spec (Zlength (lx_low_level_spec)) k Mdone ) ” 
  &&  “ (rref_prefix_mod zp_low_level_spec (Zlength (lx_low_level_spec)) (k + 1 ) Mdone ) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_13 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  TT && emp 
|--
  “ (gauss_inv zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_13_split_goal_1 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  (gauss_inv zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone )
.

Definition gauss_solve_mod_gmp_entail_wit_14 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mdone: matrix) (ldone: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k <= n_pre)) (PreH23 : (0 <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (lcur: (@list Z))  (M: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mdone: matrix) (ldone: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k <= n_pre)) (PreH23 : (0 <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) ,
  TT && emp 
|--
  EX (M: matrix) ,
  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (rep_matrix ldone (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) M ) ” 
  &&  “ (gauss_inv zp_low_level_spec (Zlength (lx_low_level_spec)) k M0_low_level_spec M ) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_15 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (lcur: (@list Z)) (M: matrix) (k: Z) (cols: Z) (PreH1 : (k >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k <= n_pre)) (PreH21 : (rep_matrix lcur n_pre cols M )) (PreH22 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (lfin: (@list Z))  (Mfin: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lfin n_pre cols Mfin ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin ) ” 
  &&  “ (gauss_finished_matrix zp_low_level_spec n_pre Mfin ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (lcur: (@list Z)) (M: matrix) (k: Z) (cols: Z) (PreH1 : (k >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k <= n_pre)) (PreH21 : (rep_matrix lcur n_pre cols M )) (PreH22 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  TT && emp 
|--
  EX (Mfin: matrix) ,
  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (((Zlength (lx_low_level_spec)) + 1 ) = ((Zlength (lx_low_level_spec)) + 1 )) ” 
  &&  “ (rep_matrix lcur (Zlength (lx_low_level_spec)) ((Zlength (lx_low_level_spec)) + 1 ) Mfin ) ” 
  &&  “ (gauss_inv zp_low_level_spec (Zlength (lx_low_level_spec)) (Zlength (lx_low_level_spec)) M0_low_level_spec Mfin ) ” 
  &&  “ (gauss_finished_matrix zp_low_level_spec (Zlength (lx_low_level_spec)) Mfin ) ”
  &&  emp
).

Definition gauss_solve_mod_gmp_entail_wit_16 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (Mfin: matrix) (lfin: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  (EX (lxcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lfin n_pre cols Mfin ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin ) ” 
  &&  “ (gauss_finished_matrix zp_low_level_spec n_pre Mfin ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 >= n_pre) ” 
  &&  “ (INT_MIN <= (0 * cols )) ” 
  &&  “ ((0 * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((0 * cols ) + n_pre )) ” 
  &&  “ (((0 * cols ) + n_pre ) <= INT_MAX) ” 
  &&  “ (rhs_copy_prefix lxcur n_pre 0 Mfin ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur ))
  ||
  (EX (lxcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lfin n_pre cols Mfin ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin ) ” 
  &&  “ (gauss_finished_matrix zp_low_level_spec n_pre Mfin ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= ((0 * cols ) + n_pre )) ” 
  &&  “ (((0 * cols ) + n_pre ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (0 * cols )) ” 
  &&  “ ((0 * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((0 * cols ) + n_pre )) ” 
  &&  “ (((0 * cols ) + n_pre ) <= INT_MAX) ” 
  &&  “ (rhs_copy_prefix lxcur n_pre 0 Mfin ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur ))
.

Definition gauss_solve_mod_gmp_entail_wit_17 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (lxcur_2: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= ((i * cols ) + n_pre ))) (PreH24 : (((i * cols ) + n_pre ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (i * cols ))) (PreH26 : ((i * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH28 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH29 : (rhs_copy_prefix lxcur_2 n_pre i Mfin )) ,
  (mpz_array x_pre n_pre (replace_Znth (i) ((Znth (((i * cols ) + n_pre )) (lfin) (0))) (lxcur_2)) )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (store_Z p_pre zp_low_level_spec )
|--
  (EX (lxcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lfin n_pre cols Mfin ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin ) ” 
  &&  “ (gauss_finished_matrix zp_low_level_spec n_pre Mfin ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + n_pre )) ” 
  &&  “ ((((i + 1 ) * cols ) + n_pre ) <= INT_MAX) ” 
  &&  “ (rhs_copy_prefix lxcur n_pre (i + 1 ) Mfin ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur ))
  ||
  (EX (lxcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lfin n_pre cols Mfin ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin ) ” 
  &&  “ (gauss_finished_matrix zp_low_level_spec n_pre Mfin ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((i + 1 ) * cols ) + n_pre )) ” 
  &&  “ ((((i + 1 ) * cols ) + n_pre ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + n_pre )) ” 
  &&  “ ((((i + 1 ) * cols ) + n_pre ) <= INT_MAX) ” 
  &&  “ (rhs_copy_prefix lxcur n_pre (i + 1 ) Mfin ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur ))
.

Definition gauss_solve_mod_gmp_return_wit_1 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (i >= n_pre)) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH27 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH28 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur )
|--
  EX (X: vector)  (lx2: (@list Z))  (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (rep_vector lx2 n_pre X ) ” 
  &&  “ (gauss_success zp_low_level_spec n_pre M0_low_level_spec X ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx2 )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (i >= n_pre)) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH27 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH28 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
|--
  EX (X: vector)  (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rep_vector lxcur n_pre X ) ” 
  &&  “ (gauss_success zp_low_level_spec n_pre M0_low_level_spec X ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition gauss_solve_mod_gmp_return_wit_2 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= ((i * cols ) + n_pre ))) (PreH24 : (((i * cols ) + n_pre ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (i * cols ))) (PreH26 : ((i * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH28 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH29 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur )
|--
  EX (X: vector)  (lx2: (@list Z))  (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (rep_vector lx2 n_pre X ) ” 
  &&  “ (gauss_success zp_low_level_spec n_pre M0_low_level_spec X ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx2 )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= ((i * cols ) + n_pre ))) (PreH24 : (((i * cols ) + n_pre ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (i * cols ))) (PreH26 : ((i * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH28 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH29 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
|--
  EX (X: vector)  (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rep_vector lxcur n_pre X ) ” 
  &&  “ (gauss_success zp_low_level_spec n_pre M0_low_level_spec X ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition gauss_solve_mod_gmp_return_wit_3 := 
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot = n_pre)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (pivot >= n_pre)) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH29 : (ps = 0)) (PreH30 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (lx2: (@list Z))  (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (0 = 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx2 )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot = n_pre)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (pivot >= n_pre)) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH28 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH29 : (ps = 0)) (PreH30 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition gauss_solve_mod_gmp_partial_solve_wit_1 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (ps: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (ps = 0)) (PreH2 : (pivot < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot <= n_pre)) (PreH24 : (0 <= ((pivot * cols ) + k ))) (PreH25 : (((pivot * cols ) + k ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + k ))) (PreH29 : (((pivot * cols ) + k ) <= INT_MAX)) (PreH30 : (ps = 0)) (PreH31 : ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)))) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (ps = 0) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot <= n_pre) ” 
  &&  “ (0 <= ((pivot * cols ) + k )) ” 
  &&  “ (((pivot * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (pivot * cols )) ” 
  &&  “ ((pivot * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot * cols ) + k )) ” 
  &&  “ (((pivot * cols ) + k ) <= INT_MAX) ” 
  &&  “ (ps = 0) ” 
  &&  “ ((ps <> 0) -> ((pivot < n_pre) /\ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0))) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (pivot_search_zero_prefix n_pre k pivot M ) ”
  &&  (store_Z (aug_pre + (((pivot * cols ) + k ) * sizeof( "__mpz_struct" ))) (Znth (((pivot * cols ) + k )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre ((pivot * cols ) + k ) 0 (n_pre * cols ) lcur )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_2_pure := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (ps_addr_v: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH11 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH12 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH13 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH14 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (k <= pivot)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot < n_pre)) (PreH20 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)) (PreH21 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH22 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH23 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ (aug_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ”
.

Definition gauss_solve_mod_gmp_partial_solve_wit_2_aux := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH11 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH12 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH13 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH14 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (k <= pivot)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot < n_pre)) (PreH20 : ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0)) (PreH21 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH22 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH23 : (pivot_search_zero_prefix n_pre k pivot M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ ((Znth (((pivot * cols ) + k )) (lcur) (0)) <> 0) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (pivot_search_zero_prefix n_pre k pivot M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_2 := gauss_solve_mod_gmp_partial_solve_wit_2_pure -> gauss_solve_mod_gmp_partial_solve_wit_2_aux.

Definition gauss_solve_mod_gmp_partial_solve_wit_3 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (M1: matrix) (l1: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (k <= pivot)) (PreH21 : (pivot < n_pre)) (PreH22 : (0 <= ((k * cols ) + k ))) (PreH23 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (k * cols ))) (PreH25 : ((k * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((k * cols ) + k ))) (PreH27 : (((k * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l1 n_pre cols M1 )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH30 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH31 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH32 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_4 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot < n_pre)) (PreH23 : (0 <= ((k * cols ) + k ))) (PreH24 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (k * cols ))) (PreH26 : ((k * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((k * cols ) + k ))) (PreH28 : (((k * cols ) + k ) <= INT_MAX)) (PreH29 : (rep_matrix l1 n_pre cols M1 )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH31 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH32 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH33 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_5 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (k <= pivot)) (PreH22 : (pivot < n_pre)) (PreH23 : (0 <= ((k * cols ) + k ))) (PreH24 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (k * cols ))) (PreH26 : ((k * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((k * cols ) + k ))) (PreH28 : (((k * cols ) + k ) <= INT_MAX)) (PreH29 : (rep_matrix l1 n_pre cols M1 )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH31 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH32 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH33 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_6 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot < n_pre)) (PreH24 : (0 <= ((k * cols ) + k ))) (PreH25 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (k * cols ))) (PreH27 : ((k * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((k * cols ) + k ))) (PreH29 : (((k * cols ) + k ) <= INT_MAX)) (PreH30 : (rep_matrix l1 n_pre cols M1 )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH33 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH34 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_7 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (k <= pivot)) (PreH23 : (pivot < n_pre)) (PreH24 : (0 <= ((k * cols ) + k ))) (PreH25 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (k * cols ))) (PreH27 : ((k * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((k * cols ) + k ))) (PreH29 : (((k * cols ) + k ) <= INT_MAX)) (PreH30 : (rep_matrix l1 n_pre cols M1 )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH33 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH34 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_8 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= ((k * cols ) + k ))) (PreH26 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (k * cols ))) (PreH28 : ((k * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((k * cols ) + k ))) (PreH30 : (((k * cols ) + k ) <= INT_MAX)) (PreH31 : (rep_matrix l1 n_pre cols M1 )) (PreH32 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH34 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH35 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_9 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= ((k * cols ) + k ))) (PreH26 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (k * cols ))) (PreH28 : ((k * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((k * cols ) + k ))) (PreH30 : (((k * cols ) + k ) <= INT_MAX)) (PreH31 : (rep_matrix l1 n_pre cols M1 )) (PreH32 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH34 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH35 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  (store_Z retval 0 )
  **  (store_Z (aug_pre + (((k * cols ) + k ) * sizeof( "__mpz_struct" ))) (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (mpz_missing_i aug_pre ((k * cols ) + k ) 0 (n_pre * cols ) l1 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_10_pure := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (ps_addr_v: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= ((k * cols ) + k ))) (PreH26 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (k * cols ))) (PreH28 : ((k * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((k * cols ) + k ))) (PreH30 : (((k * cols ) + k ) <= INT_MAX)) (PreH31 : (rep_matrix l1 n_pre cols M1 )) (PreH32 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH34 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH35 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  ((( &( "factor" ) )) # Ptr  |-> retval_3)
  **  ((( &( "inv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "pv" ) )) # Ptr  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l1) (0)) < zp_low_level_spec) ”
.

Definition gauss_solve_mod_gmp_partial_solve_wit_10_aux := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (pivot: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= ((k * cols ) + k ))) (PreH26 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (k * cols ))) (PreH28 : ((k * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((k * cols ) + k ))) (PreH30 : (((k * cols ) + k ) <= INT_MAX)) (PreH31 : (rep_matrix l1 n_pre cols M1 )) (PreH32 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH33 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH34 : (0 < (Znth (((k * cols ) + k )) (l1) (0)))) (PreH35 : ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec)) ,
  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l1) (0)) < zp_low_level_spec) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l1 n_pre cols M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
  &&  (store_Z retval_2 0 )
  **  (store_Z retval (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l1) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval_3 0 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_10 := gauss_solve_mod_gmp_partial_solve_wit_10_pure -> gauss_solve_mod_gmp_partial_solve_wit_10_aux.

Definition gauss_solve_mod_gmp_partial_solve_wit_11_pure := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M1: matrix) (l1: (@list Z)) (zinv: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (ps_addr_v: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (k <= pivot)) (PreH21 : (pivot < n_pre)) (PreH22 : (0 <= zinv)) (PreH23 : (zinv < zp_low_level_spec)) (PreH24 : (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv )) (PreH25 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH26 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 ) ”
.

Definition gauss_solve_mod_gmp_partial_solve_wit_11_aux := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M1: matrix) (l1: (@list Z)) (zinv: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (k <= pivot)) (PreH21 : (pivot < n_pre)) (PreH22 : (0 <= zinv)) (PreH23 : (zinv < zp_low_level_spec)) (PreH24 : (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv )) (PreH25 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH26 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l1 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec M1 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l1 )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z factor 0 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_11 := gauss_solve_mod_gmp_partial_solve_wit_11_pure -> gauss_solve_mod_gmp_partial_solve_wit_11_aux.

Definition gauss_solve_mod_gmp_partial_solve_wit_12 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (pivot: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (aug_pre <> x_pre)) (PreH7 : (pv <> 0)) (PreH8 : (inv <> 0)) (PreH9 : (factor <> 0)) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * cols ))) (PreH17 : ((n_pre * cols ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (k <= pivot)) (PreH26 : (pivot < n_pre)) (PreH27 : (0 <= i)) (PreH28 : (i <= n_pre)) (PreH29 : (0 <= ((i * cols ) + k ))) (PreH30 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH31 : (INT_MIN <= (i * cols ))) (PreH32 : ((i * cols ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((i * cols ) + k ))) (PreH34 : (((i * cols ) + k ) <= INT_MAX)) (PreH35 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH37 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH38 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (i <> k) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= ((i * cols ) + k )) ” 
  &&  “ (((i * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (i * cols )) ” 
  &&  “ ((i * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((i * cols ) + k )) ” 
  &&  “ (((i * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z factor zfactor )
  **  (store_Z (aug_pre + (((i * cols ) + k ) * sizeof( "__mpz_struct" ))) (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_missing_i aug_pre ((i * cols ) + k ) 0 (n_pre * cols ) lcur2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_13 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (k <= pivot)) (PreH21 : (pivot < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (i <> k)) (PreH25 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH26 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH27 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH28 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH29 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH30 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <> k) ” 
  &&  “ (0 <= (Znth (((i * cols ) + k )) (lcur2) (0))) ” 
  &&  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_14_pure := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (ps_addr_v: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (pv <> 0)) (PreH9 : (inv <> 0)) (PreH10 : (factor <> 0)) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (i <> k)) (PreH28 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH29 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH30 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "ps" ) )) # Int  |-> ps_addr_v)
  **  ((( &( "fs" ) )) # Int  |-> retval)
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (k <> i) ” 
  &&  “ (0 <= (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0))) ” 
  &&  “ ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ”
.

Definition gauss_solve_mod_gmp_partial_solve_wit_14_aux := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (aug_pre <> x_pre)) (PreH8 : (pv <> 0)) (PreH9 : (inv <> 0)) (PreH10 : (factor <> 0)) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : (i <> k)) (PreH28 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH29 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH30 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH32 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (k <> i) ” 
  &&  “ (0 <= (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0))) ” 
  &&  “ ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) > 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <> k) ” 
  &&  “ (0 <= (Znth (((i * cols ) + k )) (lcur2) (0))) ” 
  &&  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor (Znth (((i * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_14 := gauss_solve_mod_gmp_partial_solve_wit_14_pure -> gauss_solve_mod_gmp_partial_solve_wit_14_aux.

Definition gauss_solve_mod_gmp_partial_solve_wit_15 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (Mdone: matrix) (ldone: (@list Z)) (zfactor3: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor3 )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone ) ” 
  &&  “ (pivot_column_ready zp_low_level_spec n_pre k Mdone ) ” 
  &&  “ (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone ) ”
  &&  (store_Z factor zfactor3 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_16 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (Mdone: matrix) (ldone: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone ) ” 
  &&  “ (pivot_column_ready zp_low_level_spec n_pre k Mdone ) ” 
  &&  “ (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone ) ”
  &&  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_17 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone ) ” 
  &&  “ (pivot_column_ready zp_low_level_spec n_pre k Mdone ) ” 
  &&  “ (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone ) ”
  &&  (store_Z inv zinv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_18 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (Mdone: matrix) (ldone: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone ) ” 
  &&  “ (pivot_column_ready zp_low_level_spec n_pre k Mdone ) ” 
  &&  “ (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone ) ”
  &&  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_19 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone ) ” 
  &&  “ (pivot_column_ready zp_low_level_spec n_pre k Mdone ) ” 
  &&  “ (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone ) ”
  &&  (store_Z pv (Znth (((k * ((Zlength (lx_low_level_spec)) + 1 ) ) + k )) (l1) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_20 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (pivot: Z) (Mdone: matrix) (ldone: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (aug_pre <> x_pre)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH19 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (k <= pivot)) (PreH24 : (pivot < n_pre)) (PreH25 : (rep_matrix ldone n_pre cols Mdone )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols Mdone )) (PreH27 : (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone )) (PreH28 : (pivot_column_ready zp_low_level_spec n_pre k Mdone )) (PreH29 : (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone )) ,
  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (pv <> 0) ” 
  &&  “ (inv <> 0) ” 
  &&  “ (factor <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mdone ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre k M0_low_level_spec Mdone ) ” 
  &&  “ (pivot_column_ready zp_low_level_spec n_pre k Mdone ) ” 
  &&  “ (rref_prefix_mod zp_low_level_spec n_pre (k + 1 ) Mdone ) ”
  &&  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition gauss_solve_mod_gmp_partial_solve_wit_21 := 
forall (x_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mfin: matrix) (lfin: (@list Z)) (lxcur: (@list Z)) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (aug_pre <> x_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lfin n_pre cols Mfin )) (PreH19 : (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin )) (PreH20 : (gauss_finished_matrix zp_low_level_spec n_pre Mfin )) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= ((i * cols ) + n_pre ))) (PreH24 : (((i * cols ) + n_pre ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (i * cols ))) (PreH26 : ((i * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((i * cols ) + n_pre ))) (PreH28 : (((i * cols ) + n_pre ) <= INT_MAX)) (PreH29 : (rhs_copy_prefix lxcur n_pre i Mfin )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lfin )
  **  (mpz_array x_pre n_pre lxcur )
|--
  “ (i < n_pre) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lfin n_pre cols Mfin ) ” 
  &&  “ (gauss_inv zp_low_level_spec n_pre n_pre M0_low_level_spec Mfin ) ” 
  &&  “ (gauss_finished_matrix zp_low_level_spec n_pre Mfin ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= ((i * cols ) + n_pre )) ” 
  &&  “ (((i * cols ) + n_pre ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (i * cols )) ” 
  &&  “ ((i * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((i * cols ) + n_pre )) ” 
  &&  “ (((i * cols ) + n_pre ) <= INT_MAX) ” 
  &&  “ (rhs_copy_prefix lxcur n_pre i Mfin ) ”
  &&  (store_Z (x_pre + (i * sizeof( "__mpz_struct" ))) (Znth (i) (lxcur) (0)) )
  **  (store_Z (aug_pre + (((i * cols ) + n_pre ) * sizeof( "__mpz_struct" ))) (Znth (((i * cols ) + n_pre )) (lfin) (0)) )
  **  (mpz_missing_i x_pre i 0 n_pre lxcur )
  **  (mpz_missing_i aug_pre ((i * cols ) + n_pre ) 0 (n_pre * cols ) lfin )
  **  (store_Z p_pre zp_low_level_spec )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_gauss_solve_mod_gmp_safety_wit_1 : gauss_solve_mod_gmp_safety_wit_1.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_2 : gauss_solve_mod_gmp_safety_wit_2.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_3 : gauss_solve_mod_gmp_safety_wit_3.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_4 : gauss_solve_mod_gmp_safety_wit_4.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_5 : gauss_solve_mod_gmp_safety_wit_5.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_6 : gauss_solve_mod_gmp_safety_wit_6.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_7 : gauss_solve_mod_gmp_safety_wit_7.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_8 : gauss_solve_mod_gmp_safety_wit_8.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_9 : gauss_solve_mod_gmp_safety_wit_9.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_10 : gauss_solve_mod_gmp_safety_wit_10.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_11 : gauss_solve_mod_gmp_safety_wit_11.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_12 : gauss_solve_mod_gmp_safety_wit_12.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_13 : gauss_solve_mod_gmp_safety_wit_13.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_14 : gauss_solve_mod_gmp_safety_wit_14.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_15 : gauss_solve_mod_gmp_safety_wit_15.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_16 : gauss_solve_mod_gmp_safety_wit_16.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_17 : gauss_solve_mod_gmp_safety_wit_17.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_18 : gauss_solve_mod_gmp_safety_wit_18.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_19 : gauss_solve_mod_gmp_safety_wit_19.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_20 : gauss_solve_mod_gmp_safety_wit_20.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_21 : gauss_solve_mod_gmp_safety_wit_21.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_22 : gauss_solve_mod_gmp_safety_wit_22.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_23 : gauss_solve_mod_gmp_safety_wit_23.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_24 : gauss_solve_mod_gmp_safety_wit_24.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_25 : gauss_solve_mod_gmp_safety_wit_25.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_26 : gauss_solve_mod_gmp_safety_wit_26.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_27 : gauss_solve_mod_gmp_safety_wit_27.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_28 : gauss_solve_mod_gmp_safety_wit_28.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_29 : gauss_solve_mod_gmp_safety_wit_29.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_30 : gauss_solve_mod_gmp_safety_wit_30.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_31 : gauss_solve_mod_gmp_safety_wit_31.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_32 : gauss_solve_mod_gmp_safety_wit_32.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_33 : gauss_solve_mod_gmp_safety_wit_33.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_34 : gauss_solve_mod_gmp_safety_wit_34.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_35 : gauss_solve_mod_gmp_safety_wit_35.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_36 : gauss_solve_mod_gmp_safety_wit_36.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_37 : gauss_solve_mod_gmp_safety_wit_37.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_38 : gauss_solve_mod_gmp_safety_wit_38.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_39 : gauss_solve_mod_gmp_safety_wit_39.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_40 : gauss_solve_mod_gmp_safety_wit_40.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_41 : gauss_solve_mod_gmp_safety_wit_41.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_42 : gauss_solve_mod_gmp_safety_wit_42.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_43 : gauss_solve_mod_gmp_safety_wit_43.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_44 : gauss_solve_mod_gmp_safety_wit_44.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_45 : gauss_solve_mod_gmp_safety_wit_45.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_46 : gauss_solve_mod_gmp_safety_wit_46.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_47 : gauss_solve_mod_gmp_safety_wit_47.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_48 : gauss_solve_mod_gmp_safety_wit_48.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_49 : gauss_solve_mod_gmp_safety_wit_49.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_50 : gauss_solve_mod_gmp_safety_wit_50.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_51 : gauss_solve_mod_gmp_safety_wit_51.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_52 : gauss_solve_mod_gmp_safety_wit_52.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_53 : gauss_solve_mod_gmp_safety_wit_53.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_54 : gauss_solve_mod_gmp_safety_wit_54.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_55 : gauss_solve_mod_gmp_safety_wit_55.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_56 : gauss_solve_mod_gmp_safety_wit_56.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_57 : gauss_solve_mod_gmp_safety_wit_57.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_58 : gauss_solve_mod_gmp_safety_wit_58.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_59 : gauss_solve_mod_gmp_safety_wit_59.
Axiom proof_of_gauss_solve_mod_gmp_safety_wit_60 : gauss_solve_mod_gmp_safety_wit_60.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_1 : gauss_solve_mod_gmp_entail_wit_1.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_2 : gauss_solve_mod_gmp_entail_wit_2.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_3_1 : gauss_solve_mod_gmp_entail_wit_3_1.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_3_2 : gauss_solve_mod_gmp_entail_wit_3_2.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_3_3 : gauss_solve_mod_gmp_entail_wit_3_3.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_4_1 : gauss_solve_mod_gmp_entail_wit_4_1.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_4_2 : gauss_solve_mod_gmp_entail_wit_4_2.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_5_1 : gauss_solve_mod_gmp_entail_wit_5_1.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_5_2 : gauss_solve_mod_gmp_entail_wit_5_2.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_5_3 : gauss_solve_mod_gmp_entail_wit_5_3.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_6 : gauss_solve_mod_gmp_entail_wit_6.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_7 : gauss_solve_mod_gmp_entail_wit_7.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_8 : gauss_solve_mod_gmp_entail_wit_8.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_9 : gauss_solve_mod_gmp_entail_wit_9.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_10_1 : gauss_solve_mod_gmp_entail_wit_10_1.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_10_2 : gauss_solve_mod_gmp_entail_wit_10_2.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_10_3 : gauss_solve_mod_gmp_entail_wit_10_3.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_11_1 : gauss_solve_mod_gmp_entail_wit_11_1.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_11_2 : gauss_solve_mod_gmp_entail_wit_11_2.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_12_1 : gauss_solve_mod_gmp_entail_wit_12_1.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_12_2 : gauss_solve_mod_gmp_entail_wit_12_2.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_13 : gauss_solve_mod_gmp_entail_wit_13.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_14 : gauss_solve_mod_gmp_entail_wit_14.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_15 : gauss_solve_mod_gmp_entail_wit_15.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_16 : gauss_solve_mod_gmp_entail_wit_16.
Axiom proof_of_gauss_solve_mod_gmp_entail_wit_17 : gauss_solve_mod_gmp_entail_wit_17.
Axiom proof_of_gauss_solve_mod_gmp_return_wit_1 : gauss_solve_mod_gmp_return_wit_1.
Axiom proof_of_gauss_solve_mod_gmp_return_wit_2 : gauss_solve_mod_gmp_return_wit_2.
Axiom proof_of_gauss_solve_mod_gmp_return_wit_3 : gauss_solve_mod_gmp_return_wit_3.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_1 : gauss_solve_mod_gmp_partial_solve_wit_1.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_2_pure : gauss_solve_mod_gmp_partial_solve_wit_2_pure.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_2 : gauss_solve_mod_gmp_partial_solve_wit_2.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_3 : gauss_solve_mod_gmp_partial_solve_wit_3.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_4 : gauss_solve_mod_gmp_partial_solve_wit_4.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_5 : gauss_solve_mod_gmp_partial_solve_wit_5.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_6 : gauss_solve_mod_gmp_partial_solve_wit_6.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_7 : gauss_solve_mod_gmp_partial_solve_wit_7.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_8 : gauss_solve_mod_gmp_partial_solve_wit_8.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_9 : gauss_solve_mod_gmp_partial_solve_wit_9.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_10_pure : gauss_solve_mod_gmp_partial_solve_wit_10_pure.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_10 : gauss_solve_mod_gmp_partial_solve_wit_10.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_11_pure : gauss_solve_mod_gmp_partial_solve_wit_11_pure.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_11 : gauss_solve_mod_gmp_partial_solve_wit_11.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_12 : gauss_solve_mod_gmp_partial_solve_wit_12.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_13 : gauss_solve_mod_gmp_partial_solve_wit_13.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_14_pure : gauss_solve_mod_gmp_partial_solve_wit_14_pure.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_14 : gauss_solve_mod_gmp_partial_solve_wit_14.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_15 : gauss_solve_mod_gmp_partial_solve_wit_15.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_16 : gauss_solve_mod_gmp_partial_solve_wit_16.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_17 : gauss_solve_mod_gmp_partial_solve_wit_17.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_18 : gauss_solve_mod_gmp_partial_solve_wit_18.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_19 : gauss_solve_mod_gmp_partial_solve_wit_19.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_20 : gauss_solve_mod_gmp_partial_solve_wit_20.
Axiom proof_of_gauss_solve_mod_gmp_partial_solve_wit_21 : gauss_solve_mod_gmp_partial_solve_wit_21.

End VC_Correct.
