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

(*----- Function solve_basis_into_col_gmp -----*)

Definition solve_basis_into_col_gmp_safety_wit_1 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (laug2: (@list Z)) (lx2: (@list Z)) (l2: (@list Z)) (M2: matrix) (retval: Z) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) M2 )) (PreH2 : (retval = 0)) (PreH3 : (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH4 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH5 : (a_pre <> 0)) (PreH6 : (inv_pre <> 0)) (PreH7 : (aug_pre <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (a_pre <> inv_pre)) (PreH11 : (a_pre <> aug_pre)) (PreH12 : (a_pre <> x_pre)) (PreH13 : (inv_pre <> aug_pre)) (PreH14 : (inv_pre <> x_pre)) (PreH15 : (aug_pre <> x_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 256)) (PreH18 : (2 <= zp_low_level_spec)) (PreH19 : (prime zp_low_level_spec )) (PreH20 : (0 <= (n_pre * n_pre ))) (PreH21 : ((n_pre * n_pre ) <= INT_MAX)) (PreH22 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH23 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH24 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH25 : (0 <= col_pre)) (PreH26 : (col_pre < n_pre)) (PreH27 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH30 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_basis_into_col_gmp_safety_wit_2 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (laug2: (@list Z)) (X: vector) (lx2: (@list Z)) (l2: (@list Z)) (M2: matrix) (retval: Z) (PreH1 : (rep_matrix l2 n_pre (n_pre + 1 ) M2 )) (PreH2 : (retval = 1)) (PreH3 : (rep_vector lx2 n_pre X )) (PreH4 : (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X )) (PreH5 : (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH6 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH7 : (a_pre <> 0)) (PreH8 : (inv_pre <> 0)) (PreH9 : (aug_pre <> 0)) (PreH10 : (x_pre <> 0)) (PreH11 : (p_pre <> 0)) (PreH12 : (a_pre <> inv_pre)) (PreH13 : (a_pre <> aug_pre)) (PreH14 : (a_pre <> x_pre)) (PreH15 : (inv_pre <> aug_pre)) (PreH16 : (inv_pre <> x_pre)) (PreH17 : (aug_pre <> x_pre)) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 256)) (PreH20 : (2 <= zp_low_level_spec)) (PreH21 : (prime zp_low_level_spec )) (PreH22 : (0 <= (n_pre * n_pre ))) (PreH23 : ((n_pre * n_pre ) <= INT_MAX)) (PreH24 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH25 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH26 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH27 : (0 <= col_pre)) (PreH28 : (col_pre < n_pre)) (PreH29 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH32 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_basis_into_col_gmp_safety_wit_3 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (laug2: (@list Z)) (lx2: (@list Z)) (l2: (@list Z)) (M2: matrix) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (rep_matrix l2 n_pre (n_pre + 1 ) M2 )) (PreH3 : (retval = 0)) (PreH4 : (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH5 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH6 : (a_pre <> 0)) (PreH7 : (inv_pre <> 0)) (PreH8 : (aug_pre <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (a_pre <> inv_pre)) (PreH12 : (a_pre <> aug_pre)) (PreH13 : (a_pre <> x_pre)) (PreH14 : (inv_pre <> aug_pre)) (PreH15 : (inv_pre <> x_pre)) (PreH16 : (aug_pre <> x_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (2 <= zp_low_level_spec)) (PreH20 : (prime zp_low_level_spec )) (PreH21 : (0 <= (n_pre * n_pre ))) (PreH22 : ((n_pre * n_pre ) <= INT_MAX)) (PreH23 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH24 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH25 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH26 : (0 <= col_pre)) (PreH27 : (col_pre < n_pre)) (PreH28 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH30 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH31 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
|--
  “ False ”
.

Definition solve_basis_into_col_gmp_safety_wit_4 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (laug2: (@list Z)) (X: vector) (lx2: (@list Z)) (l2: (@list Z)) (M2: matrix) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (rep_matrix l2 n_pre (n_pre + 1 ) M2 )) (PreH3 : (retval = 1)) (PreH4 : (rep_vector lx2 n_pre X )) (PreH5 : (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X )) (PreH6 : (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH7 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH8 : (a_pre <> 0)) (PreH9 : (inv_pre <> 0)) (PreH10 : (aug_pre <> 0)) (PreH11 : (x_pre <> 0)) (PreH12 : (p_pre <> 0)) (PreH13 : (a_pre <> inv_pre)) (PreH14 : (a_pre <> aug_pre)) (PreH15 : (a_pre <> x_pre)) (PreH16 : (inv_pre <> aug_pre)) (PreH17 : (inv_pre <> x_pre)) (PreH18 : (aug_pre <> x_pre)) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 256)) (PreH21 : (2 <= zp_low_level_spec)) (PreH22 : (prime zp_low_level_spec )) (PreH23 : (0 <= (n_pre * n_pre ))) (PreH24 : ((n_pre * n_pre ) <= INT_MAX)) (PreH25 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH26 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH27 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH28 : (0 <= col_pre)) (PreH29 : (col_pre < n_pre)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH33 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
|--
  “ False ”
.

Definition solve_basis_into_col_gmp_safety_wit_5 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (laug2: (@list Z)) (lx2: (@list Z)) (l2: (@list Z)) (M2: matrix) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (rep_matrix l2 n_pre (n_pre + 1 ) M2 )) (PreH3 : (retval = 0)) (PreH4 : (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH5 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH6 : (a_pre <> 0)) (PreH7 : (inv_pre <> 0)) (PreH8 : (aug_pre <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (a_pre <> inv_pre)) (PreH12 : (a_pre <> aug_pre)) (PreH13 : (a_pre <> x_pre)) (PreH14 : (inv_pre <> aug_pre)) (PreH15 : (inv_pre <> x_pre)) (PreH16 : (aug_pre <> x_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (2 <= zp_low_level_spec)) (PreH20 : (prime zp_low_level_spec )) (PreH21 : (0 <= (n_pre * n_pre ))) (PreH22 : ((n_pre * n_pre ) <= INT_MAX)) (PreH23 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH24 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH25 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH26 : (0 <= col_pre)) (PreH27 : (col_pre < n_pre)) (PreH28 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH30 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH31 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx2 )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_basis_into_col_gmp_safety_wit_6 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (M2: matrix) (laug2: (@list Z)) (lx2: (@list Z)) (X: vector) (linv2: (@list Z)) (PreH1 : (partial_rep_matrix_cols linv2 n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X)) )) (PreH2 : (a_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> inv_pre)) (PreH8 : (a_pre <> aug_pre)) (PreH9 : (a_pre <> x_pre)) (PreH10 : (inv_pre <> aug_pre)) (PreH11 : (inv_pre <> x_pre)) (PreH12 : (aug_pre <> x_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 256)) (PreH15 : (2 <= zp_low_level_spec)) (PreH16 : (prime zp_low_level_spec )) (PreH17 : (0 <= (n_pre * n_pre ))) (PreH18 : ((n_pre * n_pre ) <= INT_MAX)) (PreH19 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH20 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH21 : (0 <= col_pre)) (PreH22 : (col_pre < n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH26 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) (PreH27 : (rep_matrix laug2 n_pre (n_pre + 1 ) M2 )) (PreH28 : (rep_vector lx2 n_pre X )) (PreH29 : (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X )) ,
  (mpz_array x_pre n_pre lx2 )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_basis_into_col_gmp_entail_wit_1 := 
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (laug2_2: (@list Z)) (X_2: vector) (lx2_2: (@list Z)) (l2: (@list Z)) (M2_2: matrix) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (rep_matrix l2 n_pre (n_pre + 1 ) M2_2 )) (PreH3 : (retval = 1)) (PreH4 : (rep_vector lx2_2 n_pre X_2 )) (PreH5 : (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X_2 )) (PreH6 : (rep_matrix laug2_2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH7 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH8 : (a_pre <> 0)) (PreH9 : (inv_pre <> 0)) (PreH10 : (aug_pre <> 0)) (PreH11 : (x_pre <> 0)) (PreH12 : (p_pre <> 0)) (PreH13 : (a_pre <> inv_pre)) (PreH14 : (a_pre <> aug_pre)) (PreH15 : (a_pre <> x_pre)) (PreH16 : (inv_pre <> aug_pre)) (PreH17 : (inv_pre <> x_pre)) (PreH18 : (aug_pre <> x_pre)) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 256)) (PreH21 : (2 <= zp_low_level_spec)) (PreH22 : (prime zp_low_level_spec )) (PreH23 : (0 <= (n_pre * n_pre ))) (PreH24 : ((n_pre * n_pre ) <= INT_MAX)) (PreH25 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH26 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH27 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH28 : (0 <= col_pre)) (PreH29 : (col_pre < n_pre)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH33 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx2_2 )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
|--
  EX (lx2: (@list Z))  (X: vector)  (laug2: (@list Z))  (M2: matrix) ,
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
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre ) ” 
  &&  “ (rep_matrix laug2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rep_vector lx2 n_pre X ) ” 
  &&  “ (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (laug2_2: (@list Z)) (X_2: vector) (lx2_2: (@list Z)) (l2: (@list Z)) (M2_2: matrix) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (rep_matrix l2 n_pre (n_pre + 1 ) M2_2 )) (PreH3 : (retval = 1)) (PreH4 : (rep_vector lx2_2 n_pre X_2 )) (PreH5 : (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X_2 )) (PreH6 : (rep_matrix laug2_2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH7 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH8 : (a_pre <> 0)) (PreH9 : (inv_pre <> 0)) (PreH10 : (aug_pre <> 0)) (PreH11 : (x_pre <> 0)) (PreH12 : (p_pre <> 0)) (PreH13 : (a_pre <> inv_pre)) (PreH14 : (a_pre <> aug_pre)) (PreH15 : (a_pre <> x_pre)) (PreH16 : (inv_pre <> aug_pre)) (PreH17 : (inv_pre <> x_pre)) (PreH18 : (aug_pre <> x_pre)) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 256)) (PreH21 : (2 <= zp_low_level_spec)) (PreH22 : (prime zp_low_level_spec )) (PreH23 : (0 <= (n_pre * n_pre ))) (PreH24 : ((n_pre * n_pre ) <= INT_MAX)) (PreH25 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH26 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH27 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH28 : (0 <= col_pre)) (PreH29 : (col_pre < n_pre)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH33 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  TT && emp 
|--
  EX (X: vector) ,
  “ (rep_vector lx2_2 (Zlength (lx_low_level_spec)) X ) ” 
  &&  “ (gauss_success zp_low_level_spec (Zlength (lx_low_level_spec)) (matrix_aug_basis ((Zlength (lx_low_level_spec))) (A_low_level_spec) (col_pre)) X ) ”
  &&  emp
).

Definition solve_basis_into_col_gmp_return_wit_1 := 
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (M2: matrix) (laug2_2: (@list Z)) (lx2_2: (@list Z)) (X: vector) (linv2_2: (@list Z)) (PreH1 : (partial_rep_matrix_cols linv2_2 n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X)) )) (PreH2 : (a_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> inv_pre)) (PreH8 : (a_pre <> aug_pre)) (PreH9 : (a_pre <> x_pre)) (PreH10 : (inv_pre <> aug_pre)) (PreH11 : (inv_pre <> x_pre)) (PreH12 : (aug_pre <> x_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 256)) (PreH15 : (2 <= zp_low_level_spec)) (PreH16 : (prime zp_low_level_spec )) (PreH17 : (0 <= (n_pre * n_pre ))) (PreH18 : ((n_pre * n_pre ) <= INT_MAX)) (PreH19 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH20 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH21 : (0 <= col_pre)) (PreH22 : (col_pre < n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH26 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) (PreH27 : (rep_matrix laug2_2 n_pre (n_pre + 1 ) M2 )) (PreH28 : (rep_vector lx2_2 n_pre X )) (PreH29 : (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X )) ,
  (mpz_array x_pre n_pre lx2_2 )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2_2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2_2 )
|--
  EX (Inv2: matrix)  (lx2: (@list Z))  (laug2: (@list Z))  (linv2: (@list Z)) ,
  “ (1 = 1) ” 
  &&  “ (partial_rep_matrix_cols linv2 n_pre (col_pre + 1 ) Inv2 ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Inv2 (col_pre + 1 ) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
) \/
(
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (M2: matrix) (laug2_2: (@list Z)) (lx2_2: (@list Z)) (X: vector) (linv2_2: (@list Z)) (PreH1 : (partial_rep_matrix_cols linv2_2 n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X)) )) (PreH2 : (a_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> inv_pre)) (PreH8 : (a_pre <> aug_pre)) (PreH9 : (a_pre <> x_pre)) (PreH10 : (inv_pre <> aug_pre)) (PreH11 : (inv_pre <> x_pre)) (PreH12 : (aug_pre <> x_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 256)) (PreH15 : (2 <= zp_low_level_spec)) (PreH16 : (prime zp_low_level_spec )) (PreH17 : (0 <= (n_pre * n_pre ))) (PreH18 : ((n_pre * n_pre ) <= INT_MAX)) (PreH19 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH20 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH21 : (0 <= col_pre)) (PreH22 : (col_pre < n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH26 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) (PreH27 : (rep_matrix laug2_2 n_pre (n_pre + 1 ) M2 )) (PreH28 : (rep_vector lx2_2 n_pre X )) (PreH29 : (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X )) ,
  TT && emp 
|--
  EX (Inv2: matrix) ,
  “ (partial_rep_matrix_cols linv2_2 n_pre (col_pre + 1 ) Inv2 ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec Inv2 (col_pre + 1 ) ) ”
  &&  emp
).

Definition solve_basis_into_col_gmp_return_wit_2 := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (laug2_2: (@list Z)) (lx2_2: (@list Z)) (l2: (@list Z)) (M2: matrix) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (rep_matrix l2 n_pre (n_pre + 1 ) M2 )) (PreH3 : (retval = 0)) (PreH4 : (rep_matrix laug2_2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH5 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH6 : (a_pre <> 0)) (PreH7 : (inv_pre <> 0)) (PreH8 : (aug_pre <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (a_pre <> inv_pre)) (PreH12 : (a_pre <> aug_pre)) (PreH13 : (a_pre <> x_pre)) (PreH14 : (inv_pre <> aug_pre)) (PreH15 : (inv_pre <> x_pre)) (PreH16 : (aug_pre <> x_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (2 <= zp_low_level_spec)) (PreH20 : (prime zp_low_level_spec )) (PreH21 : (0 <= (n_pre * n_pre ))) (PreH22 : ((n_pre * n_pre ) <= INT_MAX)) (PreH23 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH24 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH25 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH26 : (0 <= col_pre)) (PreH27 : (col_pre < n_pre)) (PreH28 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH29 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH30 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH31 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
  **  (mpz_array x_pre n_pre lx2_2 )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
|--
  EX (lx2: (@list Z))  (laug2: (@list Z))  (linv2: (@list Z)) ,
  “ (0 = 0) ” 
  &&  “ (partial_rep_matrix_cols linv2 n_pre col_pre B_low_level_spec ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
.

Definition solve_basis_into_col_gmp_partial_solve_wit_1_pure := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (0 <= col_pre)) (PreH22 : (col_pre < n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH26 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
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
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ”
.

Definition solve_basis_into_col_gmp_partial_solve_wit_1_aux := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (laug_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH21 : (0 <= col_pre)) (PreH22 : (col_pre < n_pre)) (PreH23 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH26 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
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
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
.

Definition solve_basis_into_col_gmp_partial_solve_wit_1 := solve_basis_into_col_gmp_partial_solve_wit_1_pure -> solve_basis_into_col_gmp_partial_solve_wit_1_aux.

Definition solve_basis_into_col_gmp_partial_solve_wit_2_pure := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (laug2: (@list Z)) (PreH1 : (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH3 : (a_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (a_pre <> inv_pre)) (PreH9 : (a_pre <> aug_pre)) (PreH10 : (a_pre <> x_pre)) (PreH11 : (inv_pre <> aug_pre)) (PreH12 : (inv_pre <> x_pre)) (PreH13 : (aug_pre <> x_pre)) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 256)) (PreH16 : (2 <= zp_low_level_spec)) (PreH17 : (prime zp_low_level_spec )) (PreH18 : (0 <= (n_pre * n_pre ))) (PreH19 : ((n_pre * n_pre ) <= INT_MAX)) (PreH20 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH21 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH22 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH23 : (0 <= col_pre)) (PreH24 : (col_pre < n_pre)) (PreH25 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH27 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH28 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
.

Definition solve_basis_into_col_gmp_partial_solve_wit_2_aux := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (laug2: (@list Z)) (PreH1 : (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH2 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) (PreH3 : (a_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (a_pre <> inv_pre)) (PreH9 : (a_pre <> aug_pre)) (PreH10 : (a_pre <> x_pre)) (PreH11 : (inv_pre <> aug_pre)) (PreH12 : (inv_pre <> x_pre)) (PreH13 : (aug_pre <> x_pre)) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 256)) (PreH16 : (2 <= zp_low_level_spec)) (PreH17 : (prime zp_low_level_spec )) (PreH18 : (0 <= (n_pre * n_pre ))) (PreH19 : ((n_pre * n_pre ) <= INT_MAX)) (PreH20 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH21 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH22 : ((Zlength (lx_low_level_spec)) = n_pre)) (PreH23 : (0 <= col_pre)) (PreH24 : (col_pre < n_pre)) (PreH25 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH27 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH28 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (aug_pre <> x_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ” 
  &&  “ (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ” 
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
  &&  “ ((Zlength (lx_low_level_spec)) = n_pre) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
.

Definition solve_basis_into_col_gmp_partial_solve_wit_2 := solve_basis_into_col_gmp_partial_solve_wit_2_pure -> solve_basis_into_col_gmp_partial_solve_wit_2_aux.

Definition solve_basis_into_col_gmp_partial_solve_wit_3_pure := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (M2: matrix) (laug2: (@list Z)) (lx2: (@list Z)) (X: vector) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : (0 <= col_pre)) (PreH21 : (col_pre < n_pre)) (PreH22 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH23 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH25 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) (PreH26 : (rep_matrix laug2 n_pre (n_pre + 1 ) M2 )) (PreH27 : (rep_vector lx2 n_pre X )) (PreH28 : (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
|--
  “ (x_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (x_pre <> inv_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (rep_vector lx2 n_pre X ) ” 
  &&  “ (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec ) ”
.

Definition solve_basis_into_col_gmp_partial_solve_wit_3_aux := 
forall (x_pre: Z) (aug_pre: Z) (inv_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (linv_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (B_low_level_spec: matrix) (A_low_level_spec: matrix) (M2: matrix) (laug2: (@list Z)) (lx2: (@list Z)) (X: vector) (PreH1 : (a_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> inv_pre)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (a_pre <> x_pre)) (PreH9 : (inv_pre <> aug_pre)) (PreH10 : (inv_pre <> x_pre)) (PreH11 : (aug_pre <> x_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 256)) (PreH14 : (2 <= zp_low_level_spec)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 <= (n_pre * n_pre ))) (PreH17 : ((n_pre * n_pre ) <= INT_MAX)) (PreH18 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH19 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH20 : (0 <= col_pre)) (PreH21 : (col_pre < n_pre)) (PreH22 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH23 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH24 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) (PreH25 : (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre )) (PreH26 : (rep_matrix laug2 n_pre (n_pre + 1 ) M2 )) (PreH27 : (rep_vector lx2 n_pre X )) (PreH28 : (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
  **  (mpz_array x_pre n_pre lx2 )
|--
  “ (x_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (x_pre <> inv_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (rep_vector lx2 n_pre X ) ” 
  &&  “ (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec ) ” 
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
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec ) ” 
  &&  “ (inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec B_low_level_spec col_pre ) ” 
  &&  “ (rep_matrix laug2 n_pre (n_pre + 1 ) M2 ) ” 
  &&  “ (rep_vector lx2 n_pre X ) ” 
  &&  “ (gauss_success zp_low_level_spec n_pre (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) X ) ”
  &&  (mpz_array x_pre n_pre lx2 )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
.

Definition solve_basis_into_col_gmp_partial_solve_wit_3 := solve_basis_into_col_gmp_partial_solve_wit_3_pure -> solve_basis_into_col_gmp_partial_solve_wit_3_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_solve_basis_into_col_gmp_safety_wit_1 : solve_basis_into_col_gmp_safety_wit_1.
Axiom proof_of_solve_basis_into_col_gmp_safety_wit_2 : solve_basis_into_col_gmp_safety_wit_2.
Axiom proof_of_solve_basis_into_col_gmp_safety_wit_3 : solve_basis_into_col_gmp_safety_wit_3.
Axiom proof_of_solve_basis_into_col_gmp_safety_wit_4 : solve_basis_into_col_gmp_safety_wit_4.
Axiom proof_of_solve_basis_into_col_gmp_safety_wit_5 : solve_basis_into_col_gmp_safety_wit_5.
Axiom proof_of_solve_basis_into_col_gmp_safety_wit_6 : solve_basis_into_col_gmp_safety_wit_6.
Axiom proof_of_solve_basis_into_col_gmp_entail_wit_1 : solve_basis_into_col_gmp_entail_wit_1.
Axiom proof_of_solve_basis_into_col_gmp_return_wit_1 : solve_basis_into_col_gmp_return_wit_1.
Axiom proof_of_solve_basis_into_col_gmp_return_wit_2 : solve_basis_into_col_gmp_return_wit_2.
Axiom proof_of_solve_basis_into_col_gmp_partial_solve_wit_1_pure : solve_basis_into_col_gmp_partial_solve_wit_1_pure.
Axiom proof_of_solve_basis_into_col_gmp_partial_solve_wit_1 : solve_basis_into_col_gmp_partial_solve_wit_1.
Axiom proof_of_solve_basis_into_col_gmp_partial_solve_wit_2_pure : solve_basis_into_col_gmp_partial_solve_wit_2_pure.
Axiom proof_of_solve_basis_into_col_gmp_partial_solve_wit_2 : solve_basis_into_col_gmp_partial_solve_wit_2.
Axiom proof_of_solve_basis_into_col_gmp_partial_solve_wit_3_pure : solve_basis_into_col_gmp_partial_solve_wit_3_pure.
Axiom proof_of_solve_basis_into_col_gmp_partial_solve_wit_3 : solve_basis_into_col_gmp_partial_solve_wit_3.

End VC_Correct.
