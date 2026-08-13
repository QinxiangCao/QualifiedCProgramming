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

(*----- Function build_inverse_cols_gmp -----*)

Definition build_inverse_cols_gmp_safety_wit_1 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH21 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH22 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH23 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  ((( &( "col" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
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
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_inverse_cols_gmp_safety_wit_2 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (partial_rep_matrix_cols linv2 n_pre col Bcur )) (PreH3 : (col < n_pre)) (PreH4 : (a_pre <> 0)) (PreH5 : (inv_pre <> 0)) (PreH6 : (aug_pre <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (a_pre <> inv_pre)) (PreH10 : (a_pre <> aug_pre)) (PreH11 : (a_pre <> x_pre)) (PreH12 : (inv_pre <> aug_pre)) (PreH13 : (inv_pre <> x_pre)) (PreH14 : (aug_pre <> x_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 256)) (PreH17 : (2 <= zp_low_level_spec)) (PreH18 : (prime zp_low_level_spec )) (PreH19 : (0 <= (n_pre * n_pre ))) (PreH20 : ((n_pre * n_pre ) <= INT_MAX)) (PreH21 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH22 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH23 : (0 <= col)) (PreH24 : (col <= n_pre)) (PreH25 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH27 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH28 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_inverse_cols_gmp_safety_wit_3 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (Inv2: matrix) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (partial_rep_matrix_cols linv2 n_pre (col + 1 ) Inv2 )) (PreH3 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Inv2 (col + 1 ) )) (PreH4 : (col < n_pre)) (PreH5 : (a_pre <> 0)) (PreH6 : (inv_pre <> 0)) (PreH7 : (aug_pre <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (a_pre <> inv_pre)) (PreH11 : (a_pre <> aug_pre)) (PreH12 : (a_pre <> x_pre)) (PreH13 : (inv_pre <> aug_pre)) (PreH14 : (inv_pre <> x_pre)) (PreH15 : (aug_pre <> x_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 256)) (PreH18 : (2 <= zp_low_level_spec)) (PreH19 : (prime zp_low_level_spec )) (PreH20 : (0 <= (n_pre * n_pre ))) (PreH21 : ((n_pre * n_pre ) <= INT_MAX)) (PreH22 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH23 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH24 : (0 <= col)) (PreH25 : (col <= n_pre)) (PreH26 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH29 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_inverse_cols_gmp_safety_wit_4 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (partial_rep_matrix_cols linv2 n_pre col Bcur )) (PreH4 : (col < n_pre)) (PreH5 : (a_pre <> 0)) (PreH6 : (inv_pre <> 0)) (PreH7 : (aug_pre <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (a_pre <> inv_pre)) (PreH11 : (a_pre <> aug_pre)) (PreH12 : (a_pre <> x_pre)) (PreH13 : (inv_pre <> aug_pre)) (PreH14 : (inv_pre <> x_pre)) (PreH15 : (aug_pre <> x_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 256)) (PreH18 : (2 <= zp_low_level_spec)) (PreH19 : (prime zp_low_level_spec )) (PreH20 : (0 <= (n_pre * n_pre ))) (PreH21 : ((n_pre * n_pre ) <= INT_MAX)) (PreH22 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH23 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH24 : (0 <= col)) (PreH25 : (col <= n_pre)) (PreH26 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH29 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
|--
  “ False ”
.

Definition build_inverse_cols_gmp_safety_wit_5 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (Inv2: matrix) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 1)) (PreH3 : (partial_rep_matrix_cols linv2 n_pre (col + 1 ) Inv2 )) (PreH4 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Inv2 (col + 1 ) )) (PreH5 : (col < n_pre)) (PreH6 : (a_pre <> 0)) (PreH7 : (inv_pre <> 0)) (PreH8 : (aug_pre <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (a_pre <> inv_pre)) (PreH12 : (a_pre <> aug_pre)) (PreH13 : (a_pre <> x_pre)) (PreH14 : (inv_pre <> aug_pre)) (PreH15 : (inv_pre <> x_pre)) (PreH16 : (aug_pre <> x_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (2 <= zp_low_level_spec)) (PreH20 : (prime zp_low_level_spec )) (PreH21 : (0 <= (n_pre * n_pre ))) (PreH22 : ((n_pre * n_pre ) <= INT_MAX)) (PreH23 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH24 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH25 : (0 <= col)) (PreH26 : (col <= n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH30 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
|--
  “ False ”
.

Definition build_inverse_cols_gmp_safety_wit_6 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (partial_rep_matrix_cols linv2 n_pre col Bcur )) (PreH4 : (col < n_pre)) (PreH5 : (a_pre <> 0)) (PreH6 : (inv_pre <> 0)) (PreH7 : (aug_pre <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (a_pre <> inv_pre)) (PreH11 : (a_pre <> aug_pre)) (PreH12 : (a_pre <> x_pre)) (PreH13 : (inv_pre <> aug_pre)) (PreH14 : (inv_pre <> x_pre)) (PreH15 : (aug_pre <> x_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 256)) (PreH18 : (2 <= zp_low_level_spec)) (PreH19 : (prime zp_low_level_spec )) (PreH20 : (0 <= (n_pre * n_pre ))) (PreH21 : ((n_pre * n_pre ) <= INT_MAX)) (PreH22 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH23 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH24 : (0 <= col)) (PreH25 : (col <= n_pre)) (PreH26 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH29 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_inverse_cols_gmp_safety_wit_7 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (Inv2: matrix) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (partial_rep_matrix_cols linv2 n_pre (col + 1 ) Inv2 )) (PreH4 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Inv2 (col + 1 ) )) (PreH5 : (col < n_pre)) (PreH6 : (a_pre <> 0)) (PreH7 : (inv_pre <> 0)) (PreH8 : (aug_pre <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (a_pre <> inv_pre)) (PreH12 : (a_pre <> aug_pre)) (PreH13 : (a_pre <> x_pre)) (PreH14 : (inv_pre <> aug_pre)) (PreH15 : (inv_pre <> x_pre)) (PreH16 : (aug_pre <> x_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (2 <= zp_low_level_spec)) (PreH20 : (prime zp_low_level_spec )) (PreH21 : (0 <= (n_pre * n_pre ))) (PreH22 : ((n_pre * n_pre ) <= INT_MAX)) (PreH23 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH24 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH25 : (0 <= col)) (PreH26 : (col <= n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH30 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
|--
  “ ((col + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (col + 1 )) ”
.

Definition build_inverse_cols_gmp_safety_wit_8 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (Inv2: matrix) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (partial_rep_matrix_cols linv2 n_pre (col + 1 ) Inv2 )) (PreH4 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Inv2 (col + 1 ) )) (PreH5 : (col < n_pre)) (PreH6 : (a_pre <> 0)) (PreH7 : (inv_pre <> 0)) (PreH8 : (aug_pre <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (a_pre <> inv_pre)) (PreH12 : (a_pre <> aug_pre)) (PreH13 : (a_pre <> x_pre)) (PreH14 : (inv_pre <> aug_pre)) (PreH15 : (inv_pre <> x_pre)) (PreH16 : (aug_pre <> x_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (2 <= zp_low_level_spec)) (PreH20 : (prime zp_low_level_spec )) (PreH21 : (0 <= (n_pre * n_pre ))) (PreH22 : ((n_pre * n_pre ) <= INT_MAX)) (PreH23 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH24 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH25 : (0 <= col)) (PreH26 : (col <= n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH30 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_inverse_cols_gmp_safety_wit_9 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (Bfin: matrix) (linv_fin: (@list Z)) (laug_cur: (@list Z)) (lx_cur: (@list Z)) (col: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : (col = n_pre)) (PreH21 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH23 : (rep_matrix linv_fin n_pre n_pre Bfin )) (PreH24 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bfin n_pre )) (PreH25 : (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bfin )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_fin )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
  **  (mpz_array x_pre n_pre lx_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_inverse_cols_gmp_entail_wit_1 := 
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH21 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH22 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH23 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  EX (lx_cur: (@list Z))  (laug_cur: (@list Z))  (linv_cur: (@list Z))  (Bcur: matrix) ,
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
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_cols linv_cur n_pre 0 Bcur ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur 0 ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
  **  (mpz_array x_pre n_pre lx_cur )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (linv_low_level_spec)) = (n_pre * n_pre ))) (PreH21 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH22 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH23 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  TT && emp 
|--
  EX (Bcur: matrix) ,
  “ (0 <= 0) ” 
  &&  “ (partial_rep_matrix_cols linv_low_level_spec (Zlength (lx_low_level_spec)) 0 Bcur ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec (Zlength (lx_low_level_spec)) A_low_level_spec Bcur 0 ) ”
  &&  emp
).

Definition build_inverse_cols_gmp_entail_wit_2 := 
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur_2: matrix) (linv_cur_2: (@list Z)) (Inv2: matrix) (lx2: (@list Z)) (laug2: (@list Z)) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (partial_rep_matrix_cols linv2 n_pre (col + 1 ) Inv2 )) (PreH4 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Inv2 (col + 1 ) )) (PreH5 : (col < n_pre)) (PreH6 : (a_pre <> 0)) (PreH7 : (inv_pre <> 0)) (PreH8 : (aug_pre <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (a_pre <> inv_pre)) (PreH12 : (a_pre <> aug_pre)) (PreH13 : (a_pre <> x_pre)) (PreH14 : (inv_pre <> aug_pre)) (PreH15 : (inv_pre <> x_pre)) (PreH16 : (aug_pre <> x_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (2 <= zp_low_level_spec)) (PreH20 : (prime zp_low_level_spec )) (PreH21 : (0 <= (n_pre * n_pre ))) (PreH22 : ((n_pre * n_pre ) <= INT_MAX)) (PreH23 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH24 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH25 : (0 <= col)) (PreH26 : (col <= n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (partial_rep_matrix_cols linv_cur_2 n_pre col Bcur_2 )) (PreH30 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur_2 col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
|--
  EX (lx_cur: (@list Z))  (laug_cur: (@list Z))  (linv_cur: (@list Z))  (Bcur: matrix) ,
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
  &&  “ (0 <= (col + 1 )) ” 
  &&  “ ((col + 1 ) <= n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_cols linv_cur n_pre (col + 1 ) Bcur ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur (col + 1 ) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
  **  (mpz_array x_pre n_pre lx_cur )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur_2: matrix) (linv_cur_2: (@list Z)) (Inv2: matrix) (linv2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (partial_rep_matrix_cols linv2 n_pre (col + 1 ) Inv2 )) (PreH4 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Inv2 (col + 1 ) )) (PreH5 : (col < n_pre)) (PreH6 : (a_pre <> 0)) (PreH7 : (inv_pre <> 0)) (PreH8 : (aug_pre <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (a_pre <> inv_pre)) (PreH12 : (a_pre <> aug_pre)) (PreH13 : (a_pre <> x_pre)) (PreH14 : (inv_pre <> aug_pre)) (PreH15 : (inv_pre <> x_pre)) (PreH16 : (aug_pre <> x_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (2 <= zp_low_level_spec)) (PreH20 : (prime zp_low_level_spec )) (PreH21 : (0 <= (n_pre * n_pre ))) (PreH22 : ((n_pre * n_pre ) <= INT_MAX)) (PreH23 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH24 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH25 : (0 <= col)) (PreH26 : (col <= n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (partial_rep_matrix_cols linv_cur_2 n_pre col Bcur_2 )) (PreH30 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur_2 col )) ,
  TT && emp 
|--
  EX (Bcur: matrix) ,
  “ (0 <= (col + 1 )) ” 
  &&  “ ((col + 1 ) <= n_pre) ” 
  &&  “ (partial_rep_matrix_cols linv2 n_pre (col + 1 ) Bcur ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur (col + 1 ) ) ”
  &&  emp
).

Definition build_inverse_cols_gmp_entail_wit_3 := 
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (lx_cur_2: (@list Z)) (laug_cur_2: (@list Z)) (linv_cur: (@list Z)) (Bcur: matrix) (col: Z) (PreH1 : (col >= n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> inv_pre)) (PreH8 : (a_pre <> aug_pre)) (PreH9 : (a_pre <> x_pre)) (PreH10 : (inv_pre <> aug_pre)) (PreH11 : (inv_pre <> x_pre)) (PreH12 : (aug_pre <> x_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 256)) (PreH15 : (2 <= zp_low_level_spec)) (PreH16 : (prime zp_low_level_spec )) (PreH17 : (0 <= (n_pre * n_pre ))) (PreH18 : ((n_pre * n_pre ) <= INT_MAX)) (PreH19 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH20 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH21 : (0 <= col)) (PreH22 : (col <= n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH26 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur_2 )
  **  (mpz_array x_pre n_pre lx_cur_2 )
|--
  EX (lx_cur: (@list Z))  (laug_cur: (@list Z))  (linv_fin: (@list Z))  (Bfin: matrix) ,
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
  &&  “ (col = n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (rep_matrix linv_fin n_pre n_pre Bfin ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bfin n_pre ) ” 
  &&  “ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bfin ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_fin )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
  **  (mpz_array x_pre n_pre lx_cur )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (linv_cur: (@list Z)) (Bcur: matrix) (col: Z) (PreH1 : (col >= n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> inv_pre)) (PreH8 : (a_pre <> aug_pre)) (PreH9 : (a_pre <> x_pre)) (PreH10 : (inv_pre <> aug_pre)) (PreH11 : (inv_pre <> x_pre)) (PreH12 : (aug_pre <> x_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 256)) (PreH15 : (2 <= zp_low_level_spec)) (PreH16 : (prime zp_low_level_spec )) (PreH17 : (0 <= (n_pre * n_pre ))) (PreH18 : ((n_pre * n_pre ) <= INT_MAX)) (PreH19 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH20 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH21 : (0 <= col)) (PreH22 : (col <= n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH26 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  TT && emp 
|--
  EX (Bfin: matrix) ,
  “ (col = n_pre) ” 
  &&  “ (rep_matrix linv_cur n_pre n_pre Bfin ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bfin n_pre ) ” 
  &&  “ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bfin ) ”
  &&  emp
).

Definition build_inverse_cols_gmp_return_wit_1 := 
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (Bres: matrix) (Bfin: matrix) (linv_fin: (@list Z)) (laug_cur: (@list Z)) (lx_cur: (@list Z)) (col: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : (col = n_pre)) (PreH21 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH23 : (rep_matrix linv_fin n_pre n_pre Bfin )) (PreH24 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bfin n_pre )) (PreH25 : (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bfin )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_fin )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
  **  (mpz_array x_pre n_pre lx_cur )
|--
  EX (lx2: (@list Z))  (laug2: (@list Z))  (linv2: (@list Z)) ,
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((1 = 1) -> exists (Bres: matrix) , ((rep_matrix linv2 n_pre n_pre Bres ) /\ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres ))) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (Bres: matrix) (Bfin: matrix) (linv_fin: (@list Z)) (col: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : (col = n_pre)) (PreH21 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH23 : (rep_matrix linv_fin n_pre n_pre Bfin )) (PreH24 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bfin n_pre )) (PreH25 : (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bfin )) ,
  TT && emp 
|--
  “ ((1 = 1) -> exists (Bres: matrix) , ((rep_matrix linv_fin n_pre n_pre Bres ) /\ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres ))) ”
  &&  emp
).

Definition build_inverse_cols_gmp_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (Bres: matrix) (Bfin: matrix) (linv_fin: (@list Z)) (col: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : (col = n_pre)) (PreH21 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH22 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH23 : (rep_matrix linv_fin n_pre n_pre Bfin )) (PreH24 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bfin n_pre )) (PreH25 : (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bfin )) ,
  ((1 = 1) -> exists (Bres: matrix) , ((rep_matrix linv_fin n_pre n_pre Bres ) /\ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres )))
.

Definition build_inverse_cols_gmp_return_wit_2 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (Bres: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (lx2_2: (@list Z)) (laug2_2: (@list Z)) (linv2_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (partial_rep_matrix_cols linv2_2 n_pre col Bcur )) (PreH4 : (col < n_pre)) (PreH5 : (a_pre <> 0)) (PreH6 : (inv_pre <> 0)) (PreH7 : (aug_pre <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (a_pre <> inv_pre)) (PreH11 : (a_pre <> aug_pre)) (PreH12 : (a_pre <> x_pre)) (PreH13 : (inv_pre <> aug_pre)) (PreH14 : (inv_pre <> x_pre)) (PreH15 : (aug_pre <> x_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 256)) (PreH18 : (2 <= zp_low_level_spec)) (PreH19 : (prime zp_low_level_spec )) (PreH20 : (0 <= (n_pre * n_pre ))) (PreH21 : ((n_pre * n_pre ) <= INT_MAX)) (PreH22 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH23 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH24 : (0 <= col)) (PreH25 : (col <= n_pre)) (PreH26 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH29 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2_2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2_2 )
  **  (mpz_array x_pre n_pre lx2_2 )
|--
  EX (lx2: (@list Z))  (laug2: (@list Z))  (linv2: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 = 1) -> exists (Bres: matrix) , ((rep_matrix linv2 n_pre n_pre Bres ) /\ (matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bres ))) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
.

Definition build_inverse_cols_gmp_partial_solve_wit_1_pure := 
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (laug_cur: (@list Z)) (lx_cur: (@list Z)) (PreH1 : (col < n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> inv_pre)) (PreH8 : (a_pre <> aug_pre)) (PreH9 : (a_pre <> x_pre)) (PreH10 : (inv_pre <> aug_pre)) (PreH11 : (inv_pre <> x_pre)) (PreH12 : (aug_pre <> x_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 256)) (PreH15 : (2 <= zp_low_level_spec)) (PreH16 : (prime zp_low_level_spec )) (PreH17 : (0 <= (n_pre * n_pre ))) (PreH18 : ((n_pre * n_pre ) <= INT_MAX)) (PreH19 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH20 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH21 : (0 <= col)) (PreH22 : (col <= n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH26 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
  **  (mpz_array x_pre n_pre lx_cur )
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
  &&  “ (0 <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_cols linv_cur n_pre col Bcur ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col ) ” 
  &&  “ ((Zlength (lx_cur)) = n_pre) ”
) \/
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (laug_cur: (@list Z)) (lx_cur: (@list Z)) (PreH1 : (col <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (col >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (col < n_pre)) (PreH6 : (a_pre <> 0)) (PreH7 : (inv_pre <> 0)) (PreH8 : (aug_pre <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (a_pre <> inv_pre)) (PreH12 : (a_pre <> aug_pre)) (PreH13 : (a_pre <> x_pre)) (PreH14 : (inv_pre <> aug_pre)) (PreH15 : (inv_pre <> x_pre)) (PreH16 : (aug_pre <> x_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (2 <= zp_low_level_spec)) (PreH20 : (prime zp_low_level_spec )) (PreH21 : (0 <= (n_pre * n_pre ))) (PreH22 : ((n_pre * n_pre ) <= INT_MAX)) (PreH23 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH24 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH25 : (0 <= col)) (PreH26 : (col <= n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH30 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
  **  (mpz_array x_pre n_pre lx_cur )
|--
  “ ((Zlength (lx_cur)) = n_pre) ”
).

Definition build_inverse_cols_gmp_partial_solve_wit_1_pure_split_goal_1 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (laug_cur: (@list Z)) (lx_cur: (@list Z)) (PreH1 : (col <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (col >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (col < n_pre)) (PreH6 : (a_pre <> 0)) (PreH7 : (inv_pre <> 0)) (PreH8 : (aug_pre <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (a_pre <> inv_pre)) (PreH12 : (a_pre <> aug_pre)) (PreH13 : (a_pre <> x_pre)) (PreH14 : (inv_pre <> aug_pre)) (PreH15 : (inv_pre <> x_pre)) (PreH16 : (aug_pre <> x_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (2 <= zp_low_level_spec)) (PreH20 : (prime zp_low_level_spec )) (PreH21 : (0 <= (n_pre * n_pre ))) (PreH22 : ((n_pre * n_pre ) <= INT_MAX)) (PreH23 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH24 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH25 : (0 <= col)) (PreH26 : (col <= n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH30 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
  **  (mpz_array x_pre n_pre lx_cur )
|--
  “ ((Zlength (lx_cur)) = n_pre) ”
.

Definition build_inverse_cols_gmp_partial_solve_wit_1_aux := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (col: Z) (Bcur: matrix) (linv_cur: (@list Z)) (laug_cur: (@list Z)) (lx_cur: (@list Z)) (PreH1 : (col < n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> inv_pre)) (PreH8 : (a_pre <> aug_pre)) (PreH9 : (a_pre <> x_pre)) (PreH10 : (inv_pre <> aug_pre)) (PreH11 : (inv_pre <> x_pre)) (PreH12 : (aug_pre <> x_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 256)) (PreH15 : (2 <= zp_low_level_spec)) (PreH16 : (prime zp_low_level_spec )) (PreH17 : (0 <= (n_pre * n_pre ))) (PreH18 : ((n_pre * n_pre ) <= INT_MAX)) (PreH19 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH20 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH21 : (0 <= col)) (PreH22 : (col <= n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (partial_rep_matrix_cols linv_cur n_pre col Bcur )) (PreH26 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
  **  (mpz_array x_pre n_pre lx_cur )
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
  &&  “ (0 <= col) ” 
  &&  “ (col < n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_cols linv_cur n_pre col Bcur ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col ) ” 
  &&  “ ((Zlength (lx_cur)) = n_pre) ” 
  &&  “ (col < n_pre) ” 
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
  &&  “ (0 <= col) ” 
  &&  “ (col <= n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_cols linv_cur n_pre col Bcur ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Bcur col ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
  **  (mpz_array x_pre n_pre lx_cur )
.

Definition build_inverse_cols_gmp_partial_solve_wit_1 := build_inverse_cols_gmp_partial_solve_wit_1_pure -> build_inverse_cols_gmp_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_build_inverse_cols_gmp_safety_wit_1 : build_inverse_cols_gmp_safety_wit_1.
Axiom proof_of_build_inverse_cols_gmp_safety_wit_2 : build_inverse_cols_gmp_safety_wit_2.
Axiom proof_of_build_inverse_cols_gmp_safety_wit_3 : build_inverse_cols_gmp_safety_wit_3.
Axiom proof_of_build_inverse_cols_gmp_safety_wit_4 : build_inverse_cols_gmp_safety_wit_4.
Axiom proof_of_build_inverse_cols_gmp_safety_wit_5 : build_inverse_cols_gmp_safety_wit_5.
Axiom proof_of_build_inverse_cols_gmp_safety_wit_6 : build_inverse_cols_gmp_safety_wit_6.
Axiom proof_of_build_inverse_cols_gmp_safety_wit_7 : build_inverse_cols_gmp_safety_wit_7.
Axiom proof_of_build_inverse_cols_gmp_safety_wit_8 : build_inverse_cols_gmp_safety_wit_8.
Axiom proof_of_build_inverse_cols_gmp_safety_wit_9 : build_inverse_cols_gmp_safety_wit_9.
Axiom proof_of_build_inverse_cols_gmp_entail_wit_1 : build_inverse_cols_gmp_entail_wit_1.
Axiom proof_of_build_inverse_cols_gmp_entail_wit_2 : build_inverse_cols_gmp_entail_wit_2.
Axiom proof_of_build_inverse_cols_gmp_entail_wit_3 : build_inverse_cols_gmp_entail_wit_3.
Axiom proof_of_build_inverse_cols_gmp_return_wit_1 : build_inverse_cols_gmp_return_wit_1.
Axiom proof_of_build_inverse_cols_gmp_return_wit_2 : build_inverse_cols_gmp_return_wit_2.
Axiom proof_of_build_inverse_cols_gmp_partial_solve_wit_1_pure : build_inverse_cols_gmp_partial_solve_wit_1_pure.
Axiom proof_of_build_inverse_cols_gmp_partial_solve_wit_1 : build_inverse_cols_gmp_partial_solve_wit_1.

End VC_Correct.
