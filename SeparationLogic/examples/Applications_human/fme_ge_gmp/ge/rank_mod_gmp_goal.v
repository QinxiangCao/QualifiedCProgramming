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

(*----- Function rank_mod_gmp -----*)

Definition rank_mod_gmp_safety_wit_1 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 256)) (PreH5 : (2 <= zp_low_level_spec)) (PreH6 : (prime zp_low_level_spec )) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) (PreH10 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition rank_mod_gmp_safety_wit_2 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 256)) (PreH5 : (2 <= zp_low_level_spec)) (PreH6 : (prime zp_low_level_spec )) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) (PreH10 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rank_mod_gmp_safety_wit_3 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 256)) (PreH5 : (2 <= zp_low_level_spec)) (PreH6 : (prime zp_low_level_spec )) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) (PreH10 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "cols" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_4 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lcur n_pre cols M )) (PreH19 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  ((( &( "found" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |-> k)
  **  ((( &( "col" ) )) # Int  |-> k)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_5 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (0 <= ((pivot * cols ) + col ))) (PreH23 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 1)) (PreH33 : (k <= pivot)) (PreH34 : (pivot < n_pre)) (PreH35 : (k <= col)) (PreH36 : (col < n_pre)) (PreH37 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_6 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (col >= n_pre)) (PreH23 : (INT_MIN <= (pivot * cols ))) (PreH24 : ((pivot * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH26 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (rep_matrix lcur n_pre cols M )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH31 : (found = 1)) (PreH32 : (k <= pivot)) (PreH33 : (pivot < n_pre)) (PreH34 : (k <= col)) (PreH35 : (col < n_pre)) (PreH36 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_7 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (col >= n_pre)) (PreH23 : (INT_MIN <= (pivot * cols ))) (PreH24 : ((pivot * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH26 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (rep_matrix lcur n_pre cols M )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH31 : (found = 1)) (PreH32 : (k <= pivot)) (PreH33 : (pivot < n_pre)) (PreH34 : (k <= col)) (PreH35 : (col < n_pre)) (PreH36 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_8 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (pivot >= n_pre)) (PreH23 : (INT_MIN <= (pivot * cols ))) (PreH24 : ((pivot * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH26 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (rep_matrix lcur n_pre cols M )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH31 : (found = 0)) (PreH32 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_9 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (pivot >= n_pre)) (PreH23 : (INT_MIN <= (pivot * cols ))) (PreH24 : ((pivot * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH26 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (rep_matrix lcur n_pre cols M )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH31 : (found = 1)) (PreH32 : (k <= pivot)) (PreH33 : (pivot < n_pre)) (PreH34 : (k <= col)) (PreH35 : (col < n_pre)) (PreH36 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_10 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (pivot >= n_pre)) (PreH23 : (INT_MIN <= (pivot * cols ))) (PreH24 : ((pivot * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH26 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (rep_matrix lcur n_pre cols M )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH31 : (found = 1)) (PreH32 : (k <= pivot)) (PreH33 : (pivot < n_pre)) (PreH34 : (k <= col)) (PreH35 : (col < n_pre)) (PreH36 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_11 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (col >= n_pre)) (PreH23 : (INT_MIN <= (pivot * cols ))) (PreH24 : ((pivot * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH26 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (rep_matrix lcur n_pre cols M )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH31 : (found = 0)) (PreH32 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_12 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (0 <= ((pivot * cols ) + col ))) (PreH23 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 1)) (PreH33 : (k <= pivot)) (PreH34 : (pivot < n_pre)) (PreH35 : (k <= col)) (PreH36 : (col < n_pre)) (PreH37 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_13 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (0 <= ((pivot * cols ) + col ))) (PreH23 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 0)) (PreH33 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_14 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found <> 0)) (PreH2 : (pivot < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (col >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 0)) (PreH33 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_15 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found = 0)) (PreH2 : (pivot < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (0 <= ((pivot * cols ) + col ))) (PreH24 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (found = 1)) (PreH34 : (k <= pivot)) (PreH35 : (pivot < n_pre)) (PreH36 : (k <= col)) (PreH37 : (col < n_pre)) (PreH38 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_16 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found <> 0)) (PreH2 : (pivot < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (0 <= ((pivot * cols ) + col ))) (PreH24 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (found = 0)) (PreH34 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_17 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (col <> n_pre)) (PreH2 : (found = 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (col >= n_pre)) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (found = 0)) (PreH34 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_18 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (col = n_pre)) (PreH2 : (found = 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 0)) (PreH35 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ ((pivot + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot + 1 )) ”
.

Definition rank_mod_gmp_safety_wit_19 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (col = n_pre)) (PreH2 : (found = 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 0)) (PreH35 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rank_mod_gmp_safety_wit_20 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (col = n_pre)) (PreH2 : (found = 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (col >= n_pre)) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (found = 0)) (PreH34 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ ((pivot + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot + 1 )) ”
.

Definition rank_mod_gmp_safety_wit_21 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (col = n_pre)) (PreH2 : (found = 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (col >= n_pre)) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (found = 0)) (PreH34 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rank_mod_gmp_safety_wit_22 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (col <> n_pre)) (PreH2 : (found = 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 0)) (PreH35 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (((pivot * cols ) + col ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((pivot * cols ) + col )) ”
.

Definition rank_mod_gmp_safety_wit_23 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (col <> n_pre)) (PreH2 : (found = 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 0)) (PreH35 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ ((pivot * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot * cols )) ”
.

Definition rank_mod_gmp_safety_wit_24 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) < 0)) (PreH2 : (retval = (-1))) (PreH3 : (col <> n_pre)) (PreH4 : (found = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= pivot)) (PreH21 : (pivot <= n_pre)) (PreH22 : (0 <= col)) (PreH23 : (col <= n_pre)) (PreH24 : (0 <= found)) (PreH25 : (found <= 1)) (PreH26 : (0 <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH31 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH32 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (found = 0)) (PreH37 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_25 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) = 0)) (PreH2 : (retval = 0)) (PreH3 : (col <> n_pre)) (PreH4 : (found = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= pivot)) (PreH21 : (pivot <= n_pre)) (PreH22 : (0 <= col)) (PreH23 : (col <= n_pre)) (PreH24 : (0 <= found)) (PreH25 : (found <= 1)) (PreH26 : (0 <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH31 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH32 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (found = 0)) (PreH37 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_26 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) > 0)) (PreH2 : (retval = 1)) (PreH3 : (col <> n_pre)) (PreH4 : (found = 0)) (PreH5 : (pivot < n_pre)) (PreH6 : (aug_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= pivot)) (PreH21 : (pivot <= n_pre)) (PreH22 : (0 <= col)) (PreH23 : (col <= n_pre)) (PreH24 : (0 <= found)) (PreH25 : (found <= 1)) (PreH26 : (0 <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (pivot * cols ))) (PreH29 : ((pivot * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH31 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH32 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (rep_matrix lcur n_pre cols M )) (PreH35 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH36 : (found = 0)) (PreH37 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_27 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_28 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_29 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_30 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((col + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (col + 1 )) ”
.

Definition rank_mod_gmp_safety_wit_31 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rank_mod_gmp_safety_wit_32 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rank_mod_gmp_safety_wit_33 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rank_mod_gmp_safety_wit_34 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (pivot >= n_pre)) (PreH23 : (INT_MIN <= (pivot * cols ))) (PreH24 : ((pivot * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH26 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (rep_matrix lcur n_pre cols M )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH31 : (found = 0)) (PreH32 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_35 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (col >= n_pre)) (PreH23 : (INT_MIN <= (pivot * cols ))) (PreH24 : ((pivot * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH26 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (rep_matrix lcur n_pre cols M )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH31 : (found = 0)) (PreH32 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_36 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (pivot >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= pivot)) (PreH17 : (pivot <= n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col <= n_pre)) (PreH20 : (0 <= found)) (PreH21 : (found <= 1)) (PreH22 : (0 <= ((pivot * cols ) + col ))) (PreH23 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 0)) (PreH33 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_37 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found <> 0)) (PreH2 : (pivot < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (0 <= ((pivot * cols ) + col ))) (PreH24 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (found = 1)) (PreH34 : (k <= pivot)) (PreH35 : (pivot < n_pre)) (PreH36 : (k <= col)) (PreH37 : (col < n_pre)) (PreH38 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_38 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found <> 0)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (pivot >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 0)) (PreH33 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_39 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found <> 0)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (col >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 0)) (PreH33 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_40 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found <> 0)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (0 <= ((pivot * cols ) + col ))) (PreH24 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (found = 0)) (PreH34 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_41 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found = 0)) (PreH2 : (found <> 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 1)) (PreH35 : (k <= pivot)) (PreH36 : (pivot < n_pre)) (PreH37 : (k <= col)) (PreH38 : (col < n_pre)) (PreH39 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_42 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= ((k * cols ) + k ))) (PreH17 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH18 : (INT_MIN <= (k * cols ))) (PreH19 : ((k * cols ) <= INT_MAX)) (PreH20 : (INT_MIN <= ((k * cols ) + k ))) (PreH21 : (((k * cols ) + k ) <= INT_MAX)) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH28 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH29 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((( &( "factor" ) )) # Ptr  |-> retval_3)
  **  ((( &( "inv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "pv" ) )) # Ptr  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
|--
  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k * cols ) + k )) ”
.

Definition rank_mod_gmp_safety_wit_43 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= ((k * cols ) + k ))) (PreH17 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH18 : (INT_MIN <= (k * cols ))) (PreH19 : ((k * cols ) <= INT_MAX)) (PreH20 : (INT_MIN <= ((k * cols ) + k ))) (PreH21 : (((k * cols ) + k ) <= INT_MAX)) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH28 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH29 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((( &( "factor" ) )) # Ptr  |-> retval_3)
  **  ((( &( "inv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "pv" ) )) # Ptr  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
|--
  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * cols )) ”
.

Definition rank_mod_gmp_safety_wit_44 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (zinv: Z) (M2: matrix) (l2: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= zinv)) (PreH19 : (zinv < zp_low_level_spec)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (rep_matrix l2 n_pre cols M2 )) (PreH23 : (mat_mod zp_low_level_spec n_pre cols M2 )) (PreH24 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M2 )) (PreH25 : (pivot_column_prefix_ready zp_low_level_spec n_pre k 0 M2 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * cols ) l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_45 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (zfactor: Z) (lcur2: (@list Z)) (Mcur: matrix) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (pv <> 0)) (PreH5 : (inv <> 0)) (PreH6 : (factor <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : (0 <= k)) (PreH18 : (k < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (i >= n_pre)) (PreH22 : (INT_MIN <= (i * cols ))) (PreH23 : ((i * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + k ))) (PreH25 : (((i * cols ) + k ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH31 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_46 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  ((( &( "fs" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
|--
  “ (((i * cols ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * cols ) + k )) ”
.

Definition rank_mod_gmp_safety_wit_47 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  ((( &( "fs" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
|--
  “ ((i * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * cols )) ”
.

Definition rank_mod_gmp_safety_wit_48 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (PreH1 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < 0)) (PreH2 : (retval = (-1))) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (i <> k)) (PreH23 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH24 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH28 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH29 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH30 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  ((( &( "fs" ) )) # Int  |->_)
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_49 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (PreH1 : ((Znth (((i * cols ) + k )) (lcur2) (0)) = 0)) (PreH2 : (retval = 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (i <> k)) (PreH23 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH24 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH28 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH29 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH30 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  ((( &( "fs" ) )) # Int  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_50 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (PreH1 : ((Znth (((i * cols ) + k )) (lcur2) (0)) > 0)) (PreH2 : (retval = 1)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (i <> k)) (PreH23 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH24 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH28 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH29 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH30 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  ((( &( "fs" ) )) # Int  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rank_mod_gmp_safety_wit_51 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((i * cols ) + k )) (lcur2) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (i <> k)) (PreH24 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH25 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH29 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH31 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  ((( &( "fs" ) )) # Int  |-> retval)
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_52 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((i * cols ) + k )) (lcur2) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (i <> k)) (PreH24 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH25 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH29 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH31 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  ((( &( "fs" ) )) # Int  |-> retval)
|--
  “ False ”
.

Definition rank_mod_gmp_safety_wit_53 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur) (k) (i) ((Znth (((i * cols ) + k )) (lcur2) (0)))) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur) (k) (i) ((Znth (((i * cols ) + k )) (lcur2) (0)))) )) (PreH3 : (retval <> 0)) (PreH4 : ((Znth (((i * cols ) + k )) (lcur2) (0)) > 0)) (PreH5 : (retval = 1)) (PreH6 : (aug_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (pv <> 0)) (PreH9 : (inv <> 0)) (PreH10 : (factor <> 0)) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (cols = (n_pre + 1 ))) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 256)) (PreH15 : (2 <= zp_low_level_spec)) (PreH16 : (prime zp_low_level_spec )) (PreH17 : (0 <= (n_pre * cols ))) (PreH18 : ((n_pre * cols ) <= INT_MAX)) (PreH19 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH20 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (i <> k)) (PreH26 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH27 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition rank_mod_gmp_safety_wit_54 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur) (k) (i) ((Znth (((i * cols ) + k )) (lcur2) (0)))) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur) (k) (i) ((Znth (((i * cols ) + k )) (lcur2) (0)))) )) (PreH3 : (retval <> 0)) (PreH4 : ((Znth (((i * cols ) + k )) (lcur2) (0)) > 0)) (PreH5 : (retval = 1)) (PreH6 : (aug_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (pv <> 0)) (PreH9 : (inv <> 0)) (PreH10 : (factor <> 0)) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (cols = (n_pre + 1 ))) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 256)) (PreH15 : (2 <= zp_low_level_spec)) (PreH16 : (prime zp_low_level_spec )) (PreH17 : (0 <= (n_pre * cols ))) (PreH18 : ((n_pre * cols ) <= INT_MAX)) (PreH19 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH20 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (i <> k)) (PreH26 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH27 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rank_mod_gmp_safety_wit_55 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((i * cols ) + k )) (lcur2) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (i <> k)) (PreH24 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH25 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH29 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH31 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition rank_mod_gmp_safety_wit_56 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((i * cols ) + k )) (lcur2) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (i <> k)) (PreH24 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH25 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH29 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH31 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rank_mod_gmp_safety_wit_57 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i = k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition rank_mod_gmp_safety_wit_58 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i = k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rank_mod_gmp_safety_wit_59 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (cols = (n_pre + 1 ))) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH12 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH16 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (rep_matrix ldone n_pre cols Mdone )) (PreH18 : (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition rank_mod_gmp_safety_wit_60 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (cols = (n_pre + 1 ))) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH12 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH16 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (rep_matrix ldone n_pre cols Mdone )) (PreH18 : (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rank_mod_gmp_entail_wit_1 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 256)) (PreH5 : (2 <= zp_low_level_spec)) (PreH6 : (prime zp_low_level_spec )) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) (PreH10 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  EX (lcur: (@list Z))  (M: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre 0 M0_low_level_spec M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 256)) (PreH5 : (2 <= zp_low_level_spec)) (PreH6 : (prime zp_low_level_spec )) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) (PreH10 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  EX (M: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M0_low_level_spec ) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre 0 M0_low_level_spec M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
).

Definition rank_mod_gmp_entail_wit_2 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lcur n_pre cols M )) (PreH19 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (search_submatrix_zero_prefix_mod n_pre k k k M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lcur n_pre cols M )) (PreH19 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  “ (search_submatrix_zero_prefix_mod n_pre k k k M ) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ”
  &&  (store_Z p_pre zp_low_level_spec )
).

Definition rank_mod_gmp_entail_wit_2_split_goal_1 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lcur n_pre cols M )) (PreH19 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  “ (search_submatrix_zero_prefix_mod n_pre k k k M ) ”
.

Definition rank_mod_gmp_entail_wit_2_split_goal_2 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lcur n_pre cols M )) (PreH19 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  “ (((k * cols ) + k ) < (n_pre * cols )) ”
.

Definition rank_mod_gmp_entail_wit_2_split_goal_spatial := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (k: Z) (cols: Z) (M: matrix) (lcur: (@list Z)) (PreH1 : (k < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lcur n_pre cols M )) (PreH19 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  (store_Z p_pre zp_low_level_spec )
.

Definition rank_mod_gmp_entail_wit_3_1 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (col = n_pre)) (PreH2 : (found = 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 0)) (PreH35 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  (“ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (pivot + 1 )) ” 
  &&  “ ((pivot + 1 ) <= n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (0 <= found) ” 
  &&  “ (found <= 1) ” 
  &&  “ (0 <= (((pivot + 1 ) * cols ) + k )) ” 
  &&  “ ((((pivot + 1 ) * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= ((pivot + 1 ) * cols )) ” 
  &&  “ (((pivot + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((pivot + 1 ) * cols ) + k )) ” 
  &&  “ ((((pivot + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (found = 0) ” 
  &&  “ (search_submatrix_zero_prefix_mod n_pre k (pivot + 1 ) k M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (“ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (pivot + 1 )) ” 
  &&  “ ((pivot + 1 ) <= n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (0 <= found) ” 
  &&  “ (found <= 1) ” 
  &&  “ ((pivot + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((pivot + 1 ) * cols )) ” 
  &&  “ (((pivot + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((pivot + 1 ) * cols ) + k )) ” 
  &&  “ ((((pivot + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (found = 0) ” 
  &&  “ (search_submatrix_zero_prefix_mod n_pre k (pivot + 1 ) k M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
.

Definition rank_mod_gmp_entail_wit_3_2 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (col = n_pre)) (PreH2 : (found = 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (col >= n_pre)) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (found = 0)) (PreH34 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  (“ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (pivot + 1 )) ” 
  &&  “ ((pivot + 1 ) <= n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (0 <= found) ” 
  &&  “ (found <= 1) ” 
  &&  “ (0 <= (((pivot + 1 ) * cols ) + k )) ” 
  &&  “ ((((pivot + 1 ) * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= ((pivot + 1 ) * cols )) ” 
  &&  “ (((pivot + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((pivot + 1 ) * cols ) + k )) ” 
  &&  “ ((((pivot + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (found = 0) ” 
  &&  “ (search_submatrix_zero_prefix_mod n_pre k (pivot + 1 ) k M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (“ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (pivot + 1 )) ” 
  &&  “ ((pivot + 1 ) <= n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (0 <= found) ” 
  &&  “ (found <= 1) ” 
  &&  “ ((pivot + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((pivot + 1 ) * cols )) ” 
  &&  “ (((pivot + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((pivot + 1 ) * cols ) + k )) ” 
  &&  “ ((((pivot + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (found = 0) ” 
  &&  “ (search_submatrix_zero_prefix_mod n_pre k (pivot + 1 ) k M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
.

Definition rank_mod_gmp_entail_wit_3_3 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z p_pre zp_low_level_spec )
|--
  (“ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot <= n_pre) ” 
  &&  “ (0 <= (col + 1 )) ” 
  &&  “ ((col + 1 ) <= n_pre) ” 
  &&  “ (0 <= found) ” 
  &&  “ (found <= 1) ” 
  &&  “ (0 <= ((pivot * cols ) + (col + 1 ) )) ” 
  &&  “ (((pivot * cols ) + (col + 1 ) ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (pivot * cols )) ” 
  &&  “ ((pivot * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot * cols ) + (col + 1 ) )) ” 
  &&  “ (((pivot * cols ) + (col + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (found = 0) ” 
  &&  “ (search_submatrix_zero_prefix_mod n_pre k pivot (col + 1 ) M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (“ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot <= n_pre) ” 
  &&  “ (0 <= (col + 1 )) ” 
  &&  “ ((col + 1 ) <= n_pre) ” 
  &&  “ (0 <= found) ” 
  &&  “ (found <= 1) ” 
  &&  “ ((col + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= (pivot * cols )) ” 
  &&  “ ((pivot * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot * cols ) + (col + 1 ) )) ” 
  &&  “ (((pivot * cols ) + (col + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (found = 0) ” 
  &&  “ (search_submatrix_zero_prefix_mod n_pre k pivot (col + 1 ) M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
.

Definition rank_mod_gmp_entail_wit_3_4 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot <= n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= ((pivot * cols ) + col )) ” 
  &&  “ (((pivot * cols ) + col ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (pivot * cols )) ” 
  &&  “ ((pivot * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot * cols ) + col )) ” 
  &&  “ (((pivot * cols ) + col ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (k <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  “ (k <= col) ” 
  &&  “ (k <= pivot) ”
  &&  (store_Z p_pre zp_low_level_spec )
).

Definition rank_mod_gmp_entail_wit_3_4_split_goal_1 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  “ (k <= col) ”
.

Definition rank_mod_gmp_entail_wit_3_4_split_goal_2 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  “ (k <= pivot) ”
.

Definition rank_mod_gmp_entail_wit_3_4_split_goal_spatial := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  (store_Z p_pre zp_low_level_spec )
.

Definition rank_mod_gmp_entail_wit_3_5 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot <= n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= ((pivot * cols ) + col )) ” 
  &&  “ (((pivot * cols ) + col ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (pivot * cols )) ” 
  &&  “ ((pivot * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot * cols ) + col )) ” 
  &&  “ (((pivot * cols ) + col ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (k <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  “ (k <= col) ” 
  &&  “ (k <= pivot) ”
  &&  (store_Z p_pre zp_low_level_spec )
).

Definition rank_mod_gmp_entail_wit_3_5_split_goal_1 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  “ (k <= col) ”
.

Definition rank_mod_gmp_entail_wit_3_5_split_goal_2 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  “ (k <= pivot) ”
.

Definition rank_mod_gmp_entail_wit_3_5_split_goal_spatial := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (col <> n_pre)) (PreH5 : (found = 0)) (PreH6 : (pivot < n_pre)) (PreH7 : (aug_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= pivot)) (PreH22 : (pivot <= n_pre)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (0 <= found)) (PreH26 : (found <= 1)) (PreH27 : (0 <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH29 : (INT_MIN <= (pivot * cols ))) (PreH30 : ((pivot * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH32 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH35 : (rep_matrix lcur n_pre cols M )) (PreH36 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH37 : (found = 0)) (PreH38 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  (store_Z p_pre zp_low_level_spec )
.

Definition rank_mod_gmp_entail_wit_4 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found <> 0)) (PreH2 : (found <> 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 1)) (PreH35 : (k <= pivot)) (PreH36 : (pivot < n_pre)) (PreH37 : (k <= col)) (PreH38 : (col < n_pre)) (PreH39 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (k <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found <> 0)) (PreH2 : (found <> 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 1)) (PreH35 : (k <= pivot)) (PreH36 : (pivot < n_pre)) (PreH37 : (k <= col)) (PreH38 : (col < n_pre)) (PreH39 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
).

Definition rank_mod_gmp_entail_wit_4_split_goal_1 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found <> 0)) (PreH2 : (found <> 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 1)) (PreH35 : (k <= pivot)) (PreH36 : (pivot < n_pre)) (PreH37 : (k <= col)) (PreH38 : (col < n_pre)) (PreH39 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ”
.

Definition rank_mod_gmp_entail_wit_4_split_goal_spatial := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found <> 0)) (PreH2 : (found <> 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 1)) (PreH35 : (k <= pivot)) (PreH36 : (pivot < n_pre)) (PreH37 : (k <= col)) (PreH38 : (col < n_pre)) (PreH39 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
.

Definition rank_mod_gmp_entail_wit_5 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (col: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (cols = (n_pre + 1 ))) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH12 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (k <= pivot)) (PreH16 : (pivot < n_pre)) (PreH17 : (k <= col)) (PreH18 : (col < n_pre)) (PreH19 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH23 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (k <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
.

Definition rank_mod_gmp_entail_wit_6_1 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (col: Z) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M) (k) (pivot)) )) (PreH2 : (pivot <> k)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (k <= pivot)) (PreH18 : (pivot < n_pre)) (PreH19 : (k <= col)) (PreH20 : (col < n_pre)) (PreH21 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) (PreH22 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH24 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH25 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
|--
  EX (lswap: (@list Z))  (Mswap: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lswap n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap ) ” 
  &&  “ ((Znth (((k * cols ) + col )) (lswap) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lswap )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (col: Z) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M) (k) (pivot)) )) (PreH2 : (pivot <> k)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (k <= pivot)) (PreH18 : (pivot < n_pre)) (PreH19 : (k <= col)) (PreH20 : (col < n_pre)) (PreH21 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) (PreH22 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH24 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH25 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  EX (Mswap: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l2 n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap ) ” 
  &&  “ ((Znth (((k * cols ) + col )) (l2) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
).

Definition rank_mod_gmp_entail_wit_6_2 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (col: Z) (PreH1 : (pivot = k)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (k <= pivot)) (PreH17 : (pivot < n_pre)) (PreH18 : (k <= col)) (PreH19 : (col < n_pre)) (PreH20 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH24 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
|--
  EX (lswap: (@list Z))  (Mswap: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lswap n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap ) ” 
  &&  “ ((Znth (((k * cols ) + col )) (lswap) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lswap )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (col: Z) (PreH1 : (pivot = k)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (k <= pivot)) (PreH17 : (pivot < n_pre)) (PreH18 : (k <= col)) (PreH19 : (col < n_pre)) (PreH20 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH24 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
|--
  EX (Mswap: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap ) ” 
  &&  “ ((Znth (((k * cols ) + col )) (lcur) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
).

Definition rank_mod_gmp_entail_wit_7 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mswap_2: matrix) (lswap_2: (@list Z)) (cols: Z) (k: Z) (col: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (cols = (n_pre + 1 ))) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH12 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (0 <= col)) (PreH16 : (col < n_pre)) (PreH17 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (rep_matrix lswap_2 n_pre (n_pre + 1 ) Mswap_2 )) (PreH20 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap_2 )) (PreH21 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap_2 )) (PreH22 : ((Znth (((k * cols ) + col )) (lswap_2) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lswap_2 )
|--
  EX (lswap: (@list Z))  (Mswap: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lswap n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap ) ” 
  &&  “ ((Znth (((k * cols ) + col )) (lswap) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lswap )
.

Definition rank_mod_gmp_entail_wit_8_1 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (col: Z) (Mswap: matrix) (lswap: (@list Z)) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_col_swap (Mswap) (k) (col)) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_col_swap (Mswap) (k) (col)) )) (PreH3 : (col <> k)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col < n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (rep_matrix lswap n_pre (n_pre + 1 ) Mswap )) (PreH23 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap )) (PreH24 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap )) (PreH25 : ((Znth (((k * cols ) + col )) (lswap) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
|--
  EX (l1: (@list Z))  (M1: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (col: Z) (Mswap: matrix) (lswap: (@list Z)) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_col_swap (Mswap) (k) (col)) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_col_swap (Mswap) (k) (col)) )) (PreH3 : (col <> k)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= col)) (PreH19 : (col < n_pre)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (rep_matrix lswap n_pre (n_pre + 1 ) Mswap )) (PreH23 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap )) (PreH24 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap )) (PreH25 : ((Znth (((k * cols ) + col )) (lswap) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
|--
  EX (l1: (@list Z))  (M1: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
).

Definition rank_mod_gmp_entail_wit_8_2 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (col: Z) (Mswap: matrix) (lswap: (@list Z)) (PreH1 : (col = k)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= col)) (PreH17 : (col < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix lswap n_pre (n_pre + 1 ) Mswap )) (PreH21 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap )) (PreH22 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap )) (PreH23 : ((Znth (((k * cols ) + col )) (lswap) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lswap )
|--
  EX (l1: (@list Z))  (M1: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (col: Z) (Mswap: matrix) (lswap: (@list Z)) (PreH1 : (col = k)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= col)) (PreH17 : (col < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix lswap n_pre (n_pre + 1 ) Mswap )) (PreH21 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap )) (PreH22 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap )) (PreH23 : ((Znth (((k * cols ) + col )) (lswap) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lswap )
|--
  EX (l1: (@list Z))  (M1: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
).

Definition rank_mod_gmp_entail_wit_9 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (inv: Z) (PreH1 : (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) inv )) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : (0 <= ((k * cols ) + k ))) (PreH18 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH19 : (INT_MIN <= (k * cols ))) (PreH20 : ((k * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= ((k * cols ) + k ))) (PreH22 : (((k * cols ) + k ) <= INT_MAX)) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH29 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH30 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (store_Z retval_2 inv )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval_3 0 )
|--
  EX (zinv: Z) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv ) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_2 zinv )
  **  (store_Z retval_3 0 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l1 )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (inv: Z) (PreH1 : (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) inv )) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : (0 <= ((k * cols ) + k ))) (PreH18 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH19 : (INT_MIN <= (k * cols ))) (PreH20 : ((k * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= ((k * cols ) + k ))) (PreH22 : (((k * cols ) + k ) <= INT_MAX)) (PreH23 : (0 <= k)) (PreH24 : (k < n_pre)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH29 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH30 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (store_Z retval_2 inv )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval_3 0 )
|--
  EX (zinv: Z) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv ) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_2 zinv )
  **  (store_Z retval_3 0 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l1 )
).

Definition rank_mod_gmp_entail_wit_10 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M1: matrix) (l1: (@list Z)) (zinv_2: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (l2_2: (@list Z)) (PreH1 : (rep_matrix l2_2 n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M1) (k) (zinv_2)) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M1) (k) (zinv_2)) )) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= zinv_2)) (PreH21 : (zinv_2 < zp_low_level_spec)) (PreH22 : (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv_2 )) (PreH23 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH26 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 )) (PreH27 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv zinv_2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2_2 )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z factor 0 )
|--
  EX (l2: (@list Z))  (M2: matrix)  (zinv: Z) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l2 n_pre cols M2 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M2 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M2 ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k 0 M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * cols ) l2 )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M1: matrix) (l1: (@list Z)) (zinv_2: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (l2_2: (@list Z)) (PreH1 : (rep_matrix l2_2 n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M1) (k) (zinv_2)) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M1) (k) (zinv_2)) )) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= zinv_2)) (PreH21 : (zinv_2 < zp_low_level_spec)) (PreH22 : (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv_2 )) (PreH23 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH26 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 )) (PreH27 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv zinv_2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2_2 )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z factor 0 )
|--
  EX (l2: (@list Z))  (M2: matrix)  (zinv: Z) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l2 n_pre cols M2 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M2 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M2 ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k 0 M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * cols ) l2 )
).

Definition rank_mod_gmp_entail_wit_11 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (zinv: Z) (M2: matrix) (l2: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= zinv)) (PreH19 : (zinv < zp_low_level_spec)) (PreH20 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH21 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (rep_matrix l2 n_pre cols M2 )) (PreH23 : (mat_mod zp_low_level_spec n_pre cols M2 )) (PreH24 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M2 )) (PreH25 : (pivot_column_prefix_ready zp_low_level_spec n_pre k 0 M2 )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * cols ) l2 )
|--
  EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= ((0 * cols ) + k )) ” 
  &&  “ (((0 * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (0 * cols )) ” 
  &&  “ ((0 * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((0 * cols ) + k )) ” 
  &&  “ (((0 * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k 0 Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
.

Definition rank_mod_gmp_entail_wit_12 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <> k) ” 
  &&  “ (0 <= (Znth (((i * cols ) + k )) (lcur2) (0))) ” 
  &&  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (0 <= (Znth (((i * cols ) + k )) (lcur2) (0))) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
).

Definition rank_mod_gmp_entail_wit_12_split_goal_1 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ”
.

Definition rank_mod_gmp_entail_wit_12_split_goal_2 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ”
.

Definition rank_mod_gmp_entail_wit_12_split_goal_3 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec) ”
.

Definition rank_mod_gmp_entail_wit_12_split_goal_4 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur2 )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  “ (0 <= (Znth (((i * cols ) + k )) (lcur2) (0))) ”
.

Definition rank_mod_gmp_entail_wit_12_split_goal_spatial := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
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

Definition rank_mod_gmp_entail_wit_13_1 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur_2: matrix) (lcur2_2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (l2: (@list Z)) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur_2) (k) (i) ((Znth (((i * cols ) + k )) (lcur2_2) (0)))) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (Mcur_2) (k) (i) ((Znth (((i * cols ) + k )) (lcur2_2) (0)))) )) (PreH3 : (retval <> 0)) (PreH4 : ((Znth (((i * cols ) + k )) (lcur2_2) (0)) > 0)) (PreH5 : (retval = 1)) (PreH6 : (aug_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (pv <> 0)) (PreH9 : (inv <> 0)) (PreH10 : (factor <> 0)) (PreH11 : (cols = (n_pre + 1 ))) (PreH12 : (cols = (n_pre + 1 ))) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 256)) (PreH15 : (2 <= zp_low_level_spec)) (PreH16 : (prime zp_low_level_spec )) (PreH17 : (0 <= (n_pre * cols ))) (PreH18 : ((n_pre * cols ) <= INT_MAX)) (PreH19 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH20 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (i <> k)) (PreH26 : (0 <= (Znth (((i * cols ) + k )) (lcur2_2) (0)))) (PreH27 : ((Znth (((i * cols ) + k )) (lcur2_2) (0)) < zp_low_level_spec)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2_2 n_pre (n_pre + 1 ) Mcur_2 )) (PreH31 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur_2 )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur_2 )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur_2 )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2_2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
|--
  (EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 ))
  ||
  (EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 ))
.

Definition rank_mod_gmp_entail_wit_13_2 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur_2: matrix) (lcur2_2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Znth (((i * cols ) + k )) (lcur2_2) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (i <> k)) (PreH24 : (0 <= (Znth (((i * cols ) + k )) (lcur2_2) (0)))) (PreH25 : ((Znth (((i * cols ) + k )) (lcur2_2) (0)) < zp_low_level_spec)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (rep_matrix lcur2_2 n_pre (n_pre + 1 ) Mcur_2 )) (PreH29 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur_2 )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur_2 )) (PreH31 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur_2 )) ,
  (store_Z factor (Znth (((i * cols ) + k )) (lcur2_2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2_2 )
|--
  (EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 ))
  ||
  (EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 ))
.

Definition rank_mod_gmp_entail_wit_13_3 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur_2: matrix) (lcur2_2: (@list Z)) (zfactor_2: Z) (PreH1 : (i = k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2_2 n_pre cols Mcur_2 )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur_2 )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur_2 )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur_2 )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor_2 )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2_2 )
|--
  (EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 ))
  ||
  (EX (zfactor: Z)  (lcur2: (@list Z))  (Mcur: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ” 
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + k )) ” 
  &&  “ ((((i + 1 ) * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1 ) Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 ))
.

Definition rank_mod_gmp_entail_wit_14_1 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (zfactor: Z) (lcur2: (@list Z)) (Mcur: matrix) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (pv <> 0)) (PreH5 : (inv <> 0)) (PreH6 : (factor <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : (0 <= k)) (PreH18 : (k < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (i >= n_pre)) (PreH22 : (INT_MIN <= (i * cols ))) (PreH23 : ((i * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + k ))) (PreH25 : (((i * cols ) + k ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH31 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
|--
  EX (zfactor3: Z)  (ldone: (@list Z))  (Mdone: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor3 )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (zfactor: Z) (lcur2: (@list Z)) (Mcur: matrix) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (pv <> 0)) (PreH5 : (inv <> 0)) (PreH6 : (factor <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : (0 <= k)) (PreH18 : (k < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (i >= n_pre)) (PreH22 : (INT_MIN <= (i * cols ))) (PreH23 : ((i * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + k ))) (PreH25 : (((i * cols ) + k ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH31 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
|--
  EX (zfactor3: Z)  (Mdone: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor3 )
).

Definition rank_mod_gmp_entail_wit_14_2 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (zfactor: Z) (lcur2: (@list Z)) (Mcur: matrix) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (pv <> 0)) (PreH5 : (inv <> 0)) (PreH6 : (factor <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : (0 <= k)) (PreH18 : (k < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (0 <= ((i * cols ) + k ))) (PreH22 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH23 : (INT_MIN <= (i * cols ))) (PreH24 : ((i * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + k ))) (PreH26 : (((i * cols ) + k ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH32 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
|--
  EX (zfactor3: Z)  (ldone: (@list Z))  (Mdone: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor3 )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (zfactor: Z) (lcur2: (@list Z)) (Mcur: matrix) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (pv <> 0)) (PreH5 : (inv <> 0)) (PreH6 : (factor <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH16 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH17 : (0 <= k)) (PreH18 : (k < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (0 <= ((i * cols ) + k ))) (PreH22 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH23 : (INT_MIN <= (i * cols ))) (PreH24 : ((i * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + k ))) (PreH26 : (((i * cols ) + k ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH32 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
|--
  EX (zfactor3: Z)  (Mdone: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor3 )
).

Definition rank_mod_gmp_entail_wit_15 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (Mdone_2: matrix) (ldone_2: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix ldone_2 n_pre cols Mdone_2 )) (PreH21 : (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone_2 )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone_2 )
|--
  EX (ldone: (@list Z))  (Mdone: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
.

Definition rank_mod_gmp_entail_wit_16 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (cols = (n_pre + 1 ))) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH12 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH16 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (rep_matrix ldone n_pre cols Mdone )) (PreH18 : (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
.

Definition rank_mod_gmp_entail_wit_17 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (Mdone: matrix) (ldone: (@list Z)) (cols: Z) (k: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (cols = (n_pre + 1 ))) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH12 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH16 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (rep_matrix ldone n_pre cols Mdone )) (PreH18 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mdone )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
|--
  EX (lcur: (@list Z))  (M: matrix) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition rank_mod_gmp_return_wit_1 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (lcur: (@list Z)) (M: matrix) (k: Z) (cols: Z) (PreH1 : (k >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lcur n_pre cols M )) (PreH19 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (lcur: (@list Z)) (M: matrix) (k: Z) (cols: Z) (PreH1 : (k >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH18 : (rep_matrix lcur n_pre cols M )) (PreH19 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition rank_mod_gmp_return_wit_2 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found = 0)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (pivot >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 0)) (PreH33 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found = 0)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (pivot >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 0)) (PreH33 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition rank_mod_gmp_return_wit_3 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found = 0)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (col >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 0)) (PreH33 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found = 0)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (col >= n_pre)) (PreH24 : (INT_MIN <= (pivot * cols ))) (PreH25 : ((pivot * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH27 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur n_pre cols M )) (PreH31 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH32 : (found = 0)) (PreH33 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition rank_mod_gmp_return_wit_4 := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found = 0)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (0 <= ((pivot * cols ) + col ))) (PreH24 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (found = 0)) (PreH34 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (found = 0)) (PreH2 : (pivot >= n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < n_pre)) (PreH17 : (0 <= pivot)) (PreH18 : (pivot <= n_pre)) (PreH19 : (0 <= col)) (PreH20 : (col <= n_pre)) (PreH21 : (0 <= found)) (PreH22 : (found <= 1)) (PreH23 : (0 <= ((pivot * cols ) + col ))) (PreH24 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH25 : (INT_MIN <= (pivot * cols ))) (PreH26 : ((pivot * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH28 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (rep_matrix lcur n_pre cols M )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH33 : (found = 0)) (PreH34 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z))  (M2: matrix) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M2 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition rank_mod_gmp_partial_solve_wit_1 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (found: Z) (col: Z) (pivot: Z) (k: Z) (cols: Z) (PreH1 : (col <> n_pre)) (PreH2 : (found = 0)) (PreH3 : (pivot < n_pre)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= pivot)) (PreH19 : (pivot <= n_pre)) (PreH20 : (0 <= col)) (PreH21 : (col <= n_pre)) (PreH22 : (0 <= found)) (PreH23 : (found <= 1)) (PreH24 : (0 <= ((pivot * cols ) + col ))) (PreH25 : (((pivot * cols ) + col ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (pivot * cols ))) (PreH27 : ((pivot * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= ((pivot * cols ) + col ))) (PreH29 : (((pivot * cols ) + col ) <= INT_MAX)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix lcur n_pre cols M )) (PreH33 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) (PreH34 : (found = 0)) (PreH35 : (search_submatrix_zero_prefix_mod n_pre k pivot col M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (col <> n_pre) ” 
  &&  “ (found = 0) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot <= n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col <= n_pre) ” 
  &&  “ (0 <= found) ” 
  &&  “ (found <= 1) ” 
  &&  “ (0 <= ((pivot * cols ) + col )) ” 
  &&  “ (((pivot * cols ) + col ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (pivot * cols )) ” 
  &&  “ ((pivot * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot * cols ) + col )) ” 
  &&  “ (((pivot * cols ) + col ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre cols M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ” 
  &&  “ (found = 0) ” 
  &&  “ (search_submatrix_zero_prefix_mod n_pre k pivot col M ) ”
  &&  (store_Z (aug_pre + (((pivot * cols ) + col ) * sizeof( "__mpz_struct" ))) (Znth (((pivot * cols ) + col )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre ((pivot * cols ) + col ) 0 (n_pre * cols ) lcur )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition rank_mod_gmp_partial_solve_wit_2_pure := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (col: Z) (PreH1 : (pivot <> k)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (k <= pivot)) (PreH17 : (pivot < n_pre)) (PreH18 : (k <= col)) (PreH19 : (col < n_pre)) (PreH20 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH24 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
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

Definition rank_mod_gmp_partial_solve_wit_2_aux := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M: matrix) (lcur: (@list Z)) (cols: Z) (k: Z) (pivot: Z) (col: Z) (PreH1 : (pivot <> k)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (k <= pivot)) (PreH17 : (pivot < n_pre)) (PreH18 : (k <= col)) (PreH19 : (col < n_pre)) (PreH20 : ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (rep_matrix lcur n_pre (n_pre + 1 ) M )) (PreH24 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
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
  &&  “ (pivot <> k) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (k <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (k <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ ((Znth (((pivot * cols ) + col )) (lcur) (0)) <> 0) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur n_pre (n_pre + 1 ) M ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
.

Definition rank_mod_gmp_partial_solve_wit_2 := rank_mod_gmp_partial_solve_wit_2_pure -> rank_mod_gmp_partial_solve_wit_2_aux.

Definition rank_mod_gmp_partial_solve_wit_3_pure := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (col: Z) (Mswap: matrix) (lswap: (@list Z)) (PreH1 : (col <> k)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= col)) (PreH17 : (col < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix lswap n_pre (n_pre + 1 ) Mswap )) (PreH21 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap )) (PreH22 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap )) (PreH23 : ((Znth (((k * cols ) + col )) (lswap) (0)) <> 0)) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lswap )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ (rep_matrix lswap n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap ) ”
.

Definition rank_mod_gmp_partial_solve_wit_3_aux := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (col: Z) (Mswap: matrix) (lswap: (@list Z)) (PreH1 : (col <> k)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (0 <= col)) (PreH17 : (col < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix lswap n_pre (n_pre + 1 ) Mswap )) (PreH21 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap )) (PreH22 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap )) (PreH23 : ((Znth (((k * cols ) + col )) (lswap) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lswap )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ (rep_matrix lswap n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (col <> k) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lswap n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mswap ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap ) ” 
  &&  “ ((Znth (((k * cols ) + col )) (lswap) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lswap )
.

Definition rank_mod_gmp_partial_solve_wit_3 := rank_mod_gmp_partial_solve_wit_3_pure -> rank_mod_gmp_partial_solve_wit_3_aux.

Definition rank_mod_gmp_partial_solve_wit_4 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (cols = (n_pre + 1 ))) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH12 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH13 : (0 <= ((k * cols ) + k ))) (PreH14 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH15 : (INT_MIN <= (k * cols ))) (PreH16 : ((k * cols ) <= INT_MAX)) (PreH17 : (INT_MIN <= ((k * cols ) + k ))) (PreH18 : (((k * cols ) + k ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH24 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH25 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH26 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
.

Definition rank_mod_gmp_partial_solve_wit_5 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= ((k * cols ) + k ))) (PreH15 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH16 : (INT_MIN <= (k * cols ))) (PreH17 : ((k * cols ) <= INT_MAX)) (PreH18 : (INT_MIN <= ((k * cols ) + k ))) (PreH19 : (((k * cols ) + k ) <= INT_MAX)) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH24 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH26 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH27 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
|--
  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
.

Definition rank_mod_gmp_partial_solve_wit_6 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (2 <= zp_low_level_spec)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 <= (n_pre * cols ))) (PreH11 : ((n_pre * cols ) <= INT_MAX)) (PreH12 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH13 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH14 : (0 <= ((k * cols ) + k ))) (PreH15 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH16 : (INT_MIN <= (k * cols ))) (PreH17 : ((k * cols ) <= INT_MAX)) (PreH18 : (INT_MIN <= ((k * cols ) + k ))) (PreH19 : (((k * cols ) + k ) <= INT_MAX)) (PreH20 : (0 <= k)) (PreH21 : (k < n_pre)) (PreH22 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH24 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH26 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH27 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
|--
  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
.

Definition rank_mod_gmp_partial_solve_wit_7 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= ((k * cols ) + k ))) (PreH16 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH17 : (INT_MIN <= (k * cols ))) (PreH18 : ((k * cols ) <= INT_MAX)) (PreH19 : (INT_MIN <= ((k * cols ) + k ))) (PreH20 : (((k * cols ) + k ) <= INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH27 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH28 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
.

Definition rank_mod_gmp_partial_solve_wit_8 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (2 <= zp_low_level_spec)) (PreH10 : (prime zp_low_level_spec )) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH14 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH15 : (0 <= ((k * cols ) + k ))) (PreH16 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH17 : (INT_MIN <= (k * cols ))) (PreH18 : ((k * cols ) <= INT_MAX)) (PreH19 : (INT_MIN <= ((k * cols ) + k ))) (PreH20 : (((k * cols ) + k ) <= INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < n_pre)) (PreH23 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH27 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH28 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
.

Definition rank_mod_gmp_partial_solve_wit_9 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= ((k * cols ) + k ))) (PreH17 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH18 : (INT_MIN <= (k * cols ))) (PreH19 : ((k * cols ) <= INT_MAX)) (PreH20 : (INT_MIN <= ((k * cols ) + k ))) (PreH21 : (((k * cols ) + k ) <= INT_MAX)) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH28 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH29 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
|--
  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
.

Definition rank_mod_gmp_partial_solve_wit_10 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= ((k * cols ) + k ))) (PreH17 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH18 : (INT_MIN <= (k * cols ))) (PreH19 : ((k * cols ) <= INT_MAX)) (PreH20 : (INT_MIN <= ((k * cols ) + k ))) (PreH21 : (((k * cols ) + k ) <= INT_MAX)) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH28 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH29 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
|--
  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  (store_Z retval 0 )
  **  (store_Z (aug_pre + (((k * cols ) + k ) * sizeof( "__mpz_struct" ))) (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (mpz_missing_i aug_pre ((k * cols ) + k ) 0 (n_pre * cols ) l1 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition rank_mod_gmp_partial_solve_wit_11_pure := 
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= ((k * cols ) + k ))) (PreH17 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH18 : (INT_MIN <= (k * cols ))) (PreH19 : ((k * cols ) <= INT_MAX)) (PreH20 : (INT_MIN <= ((k * cols ) + k ))) (PreH21 : (((k * cols ) + k ) <= INT_MAX)) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH28 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH29 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  ((( &( "factor" ) )) # Ptr  |-> retval_3)
  **  ((( &( "inv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "pv" ) )) # Ptr  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ”
) \/
(
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (k <= INT_MAX)) (PreH2 : (cols <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (cols >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (retval_3 <> 0)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval <> 0)) (PreH10 : (aug_pre <> 0)) (PreH11 : (p_pre <> 0)) (PreH12 : (cols = (n_pre + 1 ))) (PreH13 : (cols = (n_pre + 1 ))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 256)) (PreH16 : (2 <= zp_low_level_spec)) (PreH17 : (prime zp_low_level_spec )) (PreH18 : (0 <= (n_pre * cols ))) (PreH19 : ((n_pre * cols ) <= INT_MAX)) (PreH20 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH21 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH22 : (0 <= ((k * cols ) + k ))) (PreH23 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (k * cols ))) (PreH25 : ((k * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((k * cols ) + k ))) (PreH27 : (((k * cols ) + k ) <= INT_MAX)) (PreH28 : (0 <= k)) (PreH29 : (k < n_pre)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH33 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH34 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH35 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  ((( &( "factor" ) )) # Ptr  |-> retval_3)
  **  ((( &( "inv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "pv" ) )) # Ptr  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
).

Definition rank_mod_gmp_partial_solve_wit_11_pure_split_goal_1 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (k <= INT_MAX)) (PreH2 : (cols <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (cols >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (retval_3 <> 0)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval <> 0)) (PreH10 : (aug_pre <> 0)) (PreH11 : (p_pre <> 0)) (PreH12 : (cols = (n_pre + 1 ))) (PreH13 : (cols = (n_pre + 1 ))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 256)) (PreH16 : (2 <= zp_low_level_spec)) (PreH17 : (prime zp_low_level_spec )) (PreH18 : (0 <= (n_pre * cols ))) (PreH19 : ((n_pre * cols ) <= INT_MAX)) (PreH20 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH21 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH22 : (0 <= ((k * cols ) + k ))) (PreH23 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (k * cols ))) (PreH25 : ((k * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((k * cols ) + k ))) (PreH27 : (((k * cols ) + k ) <= INT_MAX)) (PreH28 : (0 <= k)) (PreH29 : (k < n_pre)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH33 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH34 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH35 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  ((( &( "factor" ) )) # Ptr  |-> retval_3)
  **  ((( &( "inv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "pv" ) )) # Ptr  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ”
.

Definition rank_mod_gmp_partial_solve_wit_11_pure_split_goal_2 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (k <= INT_MAX)) (PreH2 : (cols <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (cols >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (retval_3 <> 0)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval <> 0)) (PreH10 : (aug_pre <> 0)) (PreH11 : (p_pre <> 0)) (PreH12 : (cols = (n_pre + 1 ))) (PreH13 : (cols = (n_pre + 1 ))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 256)) (PreH16 : (2 <= zp_low_level_spec)) (PreH17 : (prime zp_low_level_spec )) (PreH18 : (0 <= (n_pre * cols ))) (PreH19 : ((n_pre * cols ) <= INT_MAX)) (PreH20 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH21 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH22 : (0 <= ((k * cols ) + k ))) (PreH23 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (k * cols ))) (PreH25 : ((k * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((k * cols ) + k ))) (PreH27 : (((k * cols ) + k ) <= INT_MAX)) (PreH28 : (0 <= k)) (PreH29 : (k < n_pre)) (PreH30 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH32 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH33 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH34 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH35 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  ((( &( "factor" ) )) # Ptr  |-> retval_3)
  **  ((( &( "inv" ) )) # Ptr  |-> retval_2)
  **  ((( &( "pv" ) )) # Ptr  |-> retval)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ”
.

Definition rank_mod_gmp_partial_solve_wit_11_aux := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (cols: Z) (k: Z) (M1: matrix) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= ((k * cols ) + k ))) (PreH17 : (((k * cols ) + k ) < (n_pre * cols ))) (PreH18 : (INT_MIN <= (k * cols ))) (PreH19 : ((k * cols ) <= INT_MAX)) (PreH20 : (INT_MIN <= ((k * cols ) + k ))) (PreH21 : (((k * cols ) + k ) <= INT_MAX)) (PreH22 : (0 <= k)) (PreH23 : (k < n_pre)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH26 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M1 )) (PreH28 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) (PreH29 : ((Znth (((k * cols ) + k )) (l1) (0)) <> 0)) ,
  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) < zp_low_level_spec) ” 
  &&  “ (0 < (Znth (((k * cols ) + k )) (l1) (0))) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (k * cols )) ” 
  &&  “ ((k * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((k * cols ) + k )) ” 
  &&  “ (((k * cols ) + k ) <= INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ” 
  &&  “ ((Znth (((k * cols ) + k )) (l1) (0)) <> 0) ”
  &&  (store_Z retval_2 0 )
  **  (store_Z retval (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) l1 )
  **  (store_Z retval_3 0 )
.

Definition rank_mod_gmp_partial_solve_wit_11 := rank_mod_gmp_partial_solve_wit_11_pure -> rank_mod_gmp_partial_solve_wit_11_aux.

Definition rank_mod_gmp_partial_solve_wit_12_pure := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M1: matrix) (l1: (@list Z)) (zinv: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= zinv)) (PreH19 : (zinv < zp_low_level_spec)) (PreH20 : (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv )) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH24 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 )) (PreH25 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l1 )
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

Definition rank_mod_gmp_partial_solve_wit_12_aux := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (M1: matrix) (l1: (@list Z)) (zinv: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= zinv)) (PreH19 : (zinv < zp_low_level_spec)) (PreH20 : (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv )) (PreH21 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH23 : (rep_matrix l1 n_pre (n_pre + 1 ) M1 )) (PreH24 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 )) (PreH25 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor 0 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l1 )
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
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= zinv) ” 
  &&  “ (zinv < zp_low_level_spec) ” 
  &&  “ (mod_inverse_spec zp_low_level_spec (Znth (((k * cols ) + k )) (l1) (0)) zinv ) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix l1 n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M1 ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec M1 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l1 )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z factor 0 )
.

Definition rank_mod_gmp_partial_solve_wit_12 := rank_mod_gmp_partial_solve_wit_12_pure -> rank_mod_gmp_partial_solve_wit_12_aux.

Definition rank_mod_gmp_partial_solve_wit_13 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (i: Z) (k: Z) (cols: Z) (factor: Z) (inv: Z) (pv: Z) (Mcur: matrix) (lcur2: (@list Z)) (zfactor: Z) (PreH1 : (i <> k)) (PreH2 : (i < n_pre)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (pv <> 0)) (PreH6 : (inv <> 0)) (PreH7 : (factor <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH17 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= ((i * cols ) + k ))) (PreH23 : (((i * cols ) + k ) < (n_pre * cols ))) (PreH24 : (INT_MIN <= (i * cols ))) (PreH25 : ((i * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((i * cols ) + k ))) (PreH27 : (((i * cols ) + k ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH30 : (rep_matrix lcur2 n_pre cols Mcur )) (PreH31 : (mat_mod zp_low_level_spec n_pre cols Mcur )) (PreH32 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH33 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor )
  **  (mpz_array aug_pre (n_pre * cols ) lcur2 )
|--
  “ (i <> k) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= ((i * cols ) + k )) ” 
  &&  “ (((i * cols ) + k ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (i * cols )) ” 
  &&  “ ((i * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((i * cols ) + k )) ” 
  &&  “ (((i * cols ) + k ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre cols Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z factor zfactor )
  **  (store_Z (aug_pre + (((i * cols ) + k ) * sizeof( "__mpz_struct" ))) (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_missing_i aug_pre ((i * cols ) + k ) 0 (n_pre * cols ) lcur2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
.

Definition rank_mod_gmp_partial_solve_wit_14 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (i <> k)) (PreH21 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH22 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH23 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH25 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH26 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH27 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH28 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <> k) ” 
  &&  “ (0 <= (Znth (((i * cols ) + k )) (lcur2) (0))) ” 
  &&  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
.

Definition rank_mod_gmp_partial_solve_wit_15_pure := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((i * cols ) + k )) (lcur2) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (i <> k)) (PreH24 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH25 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH29 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH31 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "pv" ) )) # Ptr  |-> pv)
  **  ((( &( "inv" ) )) # Ptr  |-> inv)
  **  ((( &( "factor" ) )) # Ptr  |-> factor)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
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
  &&  “ (0 <= (Znth (((i * cols ) + k )) (lcur2) (0))) ” 
  &&  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ”
.

Definition rank_mod_gmp_partial_solve_wit_15_aux := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (Mcur: matrix) (lcur2: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Znth (((i * cols ) + k )) (lcur2) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (pv <> 0)) (PreH7 : (inv <> 0)) (PreH8 : (factor <> 0)) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (cols = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 256)) (PreH13 : (2 <= zp_low_level_spec)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH18 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (i <> k)) (PreH24 : (0 <= (Znth (((i * cols ) + k )) (lcur2) (0)))) (PreH25 : ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH28 : (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur )) (PreH29 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur )) (PreH30 : (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur )) (PreH31 : (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur )) ,
  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
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
  &&  “ (0 <= (Znth (((i * cols ) + k )) (lcur2) (0))) ” 
  &&  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) > 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <> k) ” 
  &&  “ (0 <= (Znth (((i * cols ) + k )) (lcur2) (0))) ” 
  &&  “ ((Znth (((i * cols ) + k )) (lcur2) (0)) < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix lcur2 n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) Mcur ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mcur ) ” 
  &&  “ (pivot_column_prefix_ready zp_low_level_spec n_pre k i Mcur ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor (Znth (((i * cols ) + k )) (lcur2) (0)) )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur2 )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
.

Definition rank_mod_gmp_partial_solve_wit_15 := rank_mod_gmp_partial_solve_wit_15_pure -> rank_mod_gmp_partial_solve_wit_15_aux.

Definition rank_mod_gmp_partial_solve_wit_16 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (Mdone: matrix) (ldone: (@list Z)) (zfactor3: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix ldone n_pre cols Mdone )) (PreH21 : (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (store_Z factor zfactor3 )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  (store_Z factor zfactor3 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
.

Definition rank_mod_gmp_partial_solve_wit_17 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (Mdone: matrix) (ldone: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix ldone n_pre cols Mdone )) (PreH21 : (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone )) ,
  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((factor)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
.

Definition rank_mod_gmp_partial_solve_wit_18 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (zinv: Z) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix ldone n_pre cols Mdone )) (PreH21 : (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z inv zinv )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  (store_Z inv zinv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
.

Definition rank_mod_gmp_partial_solve_wit_19 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (Mdone: matrix) (ldone: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix ldone n_pre cols Mdone )) (PreH21 : (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone )) ,
  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((inv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
.

Definition rank_mod_gmp_partial_solve_wit_20 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (l1: (@list Z)) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (Mdone: matrix) (ldone: (@list Z)) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix ldone n_pre cols Mdone )) (PreH21 : (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  (store_Z pv (Znth (((k * cols ) + k )) (l1) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
.

Definition rank_mod_gmp_partial_solve_wit_21 := 
forall (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M0_low_level_spec: matrix) (pv: Z) (inv: Z) (factor: Z) (cols: Z) (k: Z) (Mdone: matrix) (ldone: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (pv <> 0)) (PreH4 : (inv <> 0)) (PreH5 : (factor <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH15 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < n_pre)) (PreH18 : (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec )) (PreH20 : (rep_matrix ldone n_pre cols Mdone )) (PreH21 : (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone )) ,
  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
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
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M0_low_level_spec ) ” 
  &&  “ (rep_matrix ldone n_pre cols Mdone ) ” 
  &&  “ (rank_inv_mod zp_low_level_spec n_pre (k + 1 ) M0_low_level_spec Mdone ) ”
  &&  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((pv)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) ldone )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_rank_mod_gmp_safety_wit_1 : rank_mod_gmp_safety_wit_1.
Axiom proof_of_rank_mod_gmp_safety_wit_2 : rank_mod_gmp_safety_wit_2.
Axiom proof_of_rank_mod_gmp_safety_wit_3 : rank_mod_gmp_safety_wit_3.
Axiom proof_of_rank_mod_gmp_safety_wit_4 : rank_mod_gmp_safety_wit_4.
Axiom proof_of_rank_mod_gmp_safety_wit_5 : rank_mod_gmp_safety_wit_5.
Axiom proof_of_rank_mod_gmp_safety_wit_6 : rank_mod_gmp_safety_wit_6.
Axiom proof_of_rank_mod_gmp_safety_wit_7 : rank_mod_gmp_safety_wit_7.
Axiom proof_of_rank_mod_gmp_safety_wit_8 : rank_mod_gmp_safety_wit_8.
Axiom proof_of_rank_mod_gmp_safety_wit_9 : rank_mod_gmp_safety_wit_9.
Axiom proof_of_rank_mod_gmp_safety_wit_10 : rank_mod_gmp_safety_wit_10.
Axiom proof_of_rank_mod_gmp_safety_wit_11 : rank_mod_gmp_safety_wit_11.
Axiom proof_of_rank_mod_gmp_safety_wit_12 : rank_mod_gmp_safety_wit_12.
Axiom proof_of_rank_mod_gmp_safety_wit_13 : rank_mod_gmp_safety_wit_13.
Axiom proof_of_rank_mod_gmp_safety_wit_14 : rank_mod_gmp_safety_wit_14.
Axiom proof_of_rank_mod_gmp_safety_wit_15 : rank_mod_gmp_safety_wit_15.
Axiom proof_of_rank_mod_gmp_safety_wit_16 : rank_mod_gmp_safety_wit_16.
Axiom proof_of_rank_mod_gmp_safety_wit_17 : rank_mod_gmp_safety_wit_17.
Axiom proof_of_rank_mod_gmp_safety_wit_18 : rank_mod_gmp_safety_wit_18.
Axiom proof_of_rank_mod_gmp_safety_wit_19 : rank_mod_gmp_safety_wit_19.
Axiom proof_of_rank_mod_gmp_safety_wit_20 : rank_mod_gmp_safety_wit_20.
Axiom proof_of_rank_mod_gmp_safety_wit_21 : rank_mod_gmp_safety_wit_21.
Axiom proof_of_rank_mod_gmp_safety_wit_22 : rank_mod_gmp_safety_wit_22.
Axiom proof_of_rank_mod_gmp_safety_wit_23 : rank_mod_gmp_safety_wit_23.
Axiom proof_of_rank_mod_gmp_safety_wit_24 : rank_mod_gmp_safety_wit_24.
Axiom proof_of_rank_mod_gmp_safety_wit_25 : rank_mod_gmp_safety_wit_25.
Axiom proof_of_rank_mod_gmp_safety_wit_26 : rank_mod_gmp_safety_wit_26.
Axiom proof_of_rank_mod_gmp_safety_wit_27 : rank_mod_gmp_safety_wit_27.
Axiom proof_of_rank_mod_gmp_safety_wit_28 : rank_mod_gmp_safety_wit_28.
Axiom proof_of_rank_mod_gmp_safety_wit_29 : rank_mod_gmp_safety_wit_29.
Axiom proof_of_rank_mod_gmp_safety_wit_30 : rank_mod_gmp_safety_wit_30.
Axiom proof_of_rank_mod_gmp_safety_wit_31 : rank_mod_gmp_safety_wit_31.
Axiom proof_of_rank_mod_gmp_safety_wit_32 : rank_mod_gmp_safety_wit_32.
Axiom proof_of_rank_mod_gmp_safety_wit_33 : rank_mod_gmp_safety_wit_33.
Axiom proof_of_rank_mod_gmp_safety_wit_34 : rank_mod_gmp_safety_wit_34.
Axiom proof_of_rank_mod_gmp_safety_wit_35 : rank_mod_gmp_safety_wit_35.
Axiom proof_of_rank_mod_gmp_safety_wit_36 : rank_mod_gmp_safety_wit_36.
Axiom proof_of_rank_mod_gmp_safety_wit_37 : rank_mod_gmp_safety_wit_37.
Axiom proof_of_rank_mod_gmp_safety_wit_38 : rank_mod_gmp_safety_wit_38.
Axiom proof_of_rank_mod_gmp_safety_wit_39 : rank_mod_gmp_safety_wit_39.
Axiom proof_of_rank_mod_gmp_safety_wit_40 : rank_mod_gmp_safety_wit_40.
Axiom proof_of_rank_mod_gmp_safety_wit_41 : rank_mod_gmp_safety_wit_41.
Axiom proof_of_rank_mod_gmp_safety_wit_42 : rank_mod_gmp_safety_wit_42.
Axiom proof_of_rank_mod_gmp_safety_wit_43 : rank_mod_gmp_safety_wit_43.
Axiom proof_of_rank_mod_gmp_safety_wit_44 : rank_mod_gmp_safety_wit_44.
Axiom proof_of_rank_mod_gmp_safety_wit_45 : rank_mod_gmp_safety_wit_45.
Axiom proof_of_rank_mod_gmp_safety_wit_46 : rank_mod_gmp_safety_wit_46.
Axiom proof_of_rank_mod_gmp_safety_wit_47 : rank_mod_gmp_safety_wit_47.
Axiom proof_of_rank_mod_gmp_safety_wit_48 : rank_mod_gmp_safety_wit_48.
Axiom proof_of_rank_mod_gmp_safety_wit_49 : rank_mod_gmp_safety_wit_49.
Axiom proof_of_rank_mod_gmp_safety_wit_50 : rank_mod_gmp_safety_wit_50.
Axiom proof_of_rank_mod_gmp_safety_wit_51 : rank_mod_gmp_safety_wit_51.
Axiom proof_of_rank_mod_gmp_safety_wit_52 : rank_mod_gmp_safety_wit_52.
Axiom proof_of_rank_mod_gmp_safety_wit_53 : rank_mod_gmp_safety_wit_53.
Axiom proof_of_rank_mod_gmp_safety_wit_54 : rank_mod_gmp_safety_wit_54.
Axiom proof_of_rank_mod_gmp_safety_wit_55 : rank_mod_gmp_safety_wit_55.
Axiom proof_of_rank_mod_gmp_safety_wit_56 : rank_mod_gmp_safety_wit_56.
Axiom proof_of_rank_mod_gmp_safety_wit_57 : rank_mod_gmp_safety_wit_57.
Axiom proof_of_rank_mod_gmp_safety_wit_58 : rank_mod_gmp_safety_wit_58.
Axiom proof_of_rank_mod_gmp_safety_wit_59 : rank_mod_gmp_safety_wit_59.
Axiom proof_of_rank_mod_gmp_safety_wit_60 : rank_mod_gmp_safety_wit_60.
Axiom proof_of_rank_mod_gmp_entail_wit_1 : rank_mod_gmp_entail_wit_1.
Axiom proof_of_rank_mod_gmp_entail_wit_2 : rank_mod_gmp_entail_wit_2.
Axiom proof_of_rank_mod_gmp_entail_wit_3_1 : rank_mod_gmp_entail_wit_3_1.
Axiom proof_of_rank_mod_gmp_entail_wit_3_2 : rank_mod_gmp_entail_wit_3_2.
Axiom proof_of_rank_mod_gmp_entail_wit_3_3 : rank_mod_gmp_entail_wit_3_3.
Axiom proof_of_rank_mod_gmp_entail_wit_3_4 : rank_mod_gmp_entail_wit_3_4.
Axiom proof_of_rank_mod_gmp_entail_wit_3_5 : rank_mod_gmp_entail_wit_3_5.
Axiom proof_of_rank_mod_gmp_entail_wit_4 : rank_mod_gmp_entail_wit_4.
Axiom proof_of_rank_mod_gmp_entail_wit_5 : rank_mod_gmp_entail_wit_5.
Axiom proof_of_rank_mod_gmp_entail_wit_6_1 : rank_mod_gmp_entail_wit_6_1.
Axiom proof_of_rank_mod_gmp_entail_wit_6_2 : rank_mod_gmp_entail_wit_6_2.
Axiom proof_of_rank_mod_gmp_entail_wit_7 : rank_mod_gmp_entail_wit_7.
Axiom proof_of_rank_mod_gmp_entail_wit_8_1 : rank_mod_gmp_entail_wit_8_1.
Axiom proof_of_rank_mod_gmp_entail_wit_8_2 : rank_mod_gmp_entail_wit_8_2.
Axiom proof_of_rank_mod_gmp_entail_wit_9 : rank_mod_gmp_entail_wit_9.
Axiom proof_of_rank_mod_gmp_entail_wit_10 : rank_mod_gmp_entail_wit_10.
Axiom proof_of_rank_mod_gmp_entail_wit_11 : rank_mod_gmp_entail_wit_11.
Axiom proof_of_rank_mod_gmp_entail_wit_12 : rank_mod_gmp_entail_wit_12.
Axiom proof_of_rank_mod_gmp_entail_wit_13_1 : rank_mod_gmp_entail_wit_13_1.
Axiom proof_of_rank_mod_gmp_entail_wit_13_2 : rank_mod_gmp_entail_wit_13_2.
Axiom proof_of_rank_mod_gmp_entail_wit_13_3 : rank_mod_gmp_entail_wit_13_3.
Axiom proof_of_rank_mod_gmp_entail_wit_14_1 : rank_mod_gmp_entail_wit_14_1.
Axiom proof_of_rank_mod_gmp_entail_wit_14_2 : rank_mod_gmp_entail_wit_14_2.
Axiom proof_of_rank_mod_gmp_entail_wit_15 : rank_mod_gmp_entail_wit_15.
Axiom proof_of_rank_mod_gmp_entail_wit_16 : rank_mod_gmp_entail_wit_16.
Axiom proof_of_rank_mod_gmp_entail_wit_17 : rank_mod_gmp_entail_wit_17.
Axiom proof_of_rank_mod_gmp_return_wit_1 : rank_mod_gmp_return_wit_1.
Axiom proof_of_rank_mod_gmp_return_wit_2 : rank_mod_gmp_return_wit_2.
Axiom proof_of_rank_mod_gmp_return_wit_3 : rank_mod_gmp_return_wit_3.
Axiom proof_of_rank_mod_gmp_return_wit_4 : rank_mod_gmp_return_wit_4.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_1 : rank_mod_gmp_partial_solve_wit_1.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_2_pure : rank_mod_gmp_partial_solve_wit_2_pure.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_2 : rank_mod_gmp_partial_solve_wit_2.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_3_pure : rank_mod_gmp_partial_solve_wit_3_pure.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_3 : rank_mod_gmp_partial_solve_wit_3.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_4 : rank_mod_gmp_partial_solve_wit_4.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_5 : rank_mod_gmp_partial_solve_wit_5.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_6 : rank_mod_gmp_partial_solve_wit_6.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_7 : rank_mod_gmp_partial_solve_wit_7.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_8 : rank_mod_gmp_partial_solve_wit_8.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_9 : rank_mod_gmp_partial_solve_wit_9.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_10 : rank_mod_gmp_partial_solve_wit_10.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_11_pure : rank_mod_gmp_partial_solve_wit_11_pure.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_11 : rank_mod_gmp_partial_solve_wit_11.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_12_pure : rank_mod_gmp_partial_solve_wit_12_pure.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_12 : rank_mod_gmp_partial_solve_wit_12.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_13 : rank_mod_gmp_partial_solve_wit_13.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_14 : rank_mod_gmp_partial_solve_wit_14.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_15_pure : rank_mod_gmp_partial_solve_wit_15_pure.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_15 : rank_mod_gmp_partial_solve_wit_15.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_16 : rank_mod_gmp_partial_solve_wit_16.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_17 : rank_mod_gmp_partial_solve_wit_17.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_18 : rank_mod_gmp_partial_solve_wit_18.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_19 : rank_mod_gmp_partial_solve_wit_19.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_20 : rank_mod_gmp_partial_solve_wit_20.
Axiom proof_of_rank_mod_gmp_partial_solve_wit_21 : rank_mod_gmp_partial_solve_wit_21.

End VC_Correct.
