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

(*----- Function build_aug_basis_gmp -----*)

Definition build_aug_basis_gmp_safety_wit_1 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (laug_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (a_pre <> aug_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (0 <= (n_pre * n_pre ))) (PreH9 : ((n_pre * n_pre ) <= INT_MAX)) (PreH10 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH11 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH12 : (0 <= col_pre)) (PreH13 : (col_pre < n_pre)) (PreH14 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_2 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (laug_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (a_pre <> aug_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (0 <= (n_pre * n_pre ))) (PreH9 : ((n_pre * n_pre ) <= INT_MAX)) (PreH10 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH11 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH12 : (0 <= col_pre)) (PreH13 : (col_pre < n_pre)) (PreH14 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_3 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (laug_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (a_pre <> aug_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (0 <= (n_pre * n_pre ))) (PreH9 : ((n_pre * n_pre ) <= INT_MAX)) (PreH10 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH11 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH12 : (0 <= col_pre)) (PreH13 : (col_pre < n_pre)) (PreH14 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cols" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_aug_basis_gmp_safety_wit_4 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (laug_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (a_pre <> aug_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (0 <= (n_pre * n_pre ))) (PreH9 : ((n_pre * n_pre ) <= INT_MAX)) (PreH10 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH11 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH12 : (0 <= col_pre)) (PreH13 : (col_pre < n_pre)) (PreH14 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "cols" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_aug_basis_gmp_safety_wit_5 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (idx = (i * cols ))) (PreH20 : (0 <= idx)) (PreH21 : (idx <= (n_pre * cols ))) (PreH22 : (INT_MIN <= idx)) (PreH23 : (idx <= INT_MAX)) (PreH24 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH26 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_aug_basis_gmp_safety_wit_6 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j < cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ False ”
.

Definition build_aug_basis_gmp_safety_wit_7 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j < cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ False ”
.

Definition build_aug_basis_gmp_safety_wit_8 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j <> n_pre)) (PreH2 : (j < cols)) (PreH3 : (a_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> aug_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (0 <= (n_pre * n_pre ))) (PreH13 : ((n_pre * n_pre ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= col_pre)) (PreH17 : (col_pre < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= j)) (PreH21 : (j <= cols)) (PreH22 : (idx = ((i * cols ) + j ))) (PreH23 : (0 <= idx)) (PreH24 : (idx <= (n_pre * cols ))) (PreH25 : (idx < (n_pre * cols ))) (PreH26 : (j >= n_pre)) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ False ”
.

Definition build_aug_basis_gmp_safety_wit_9 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_10 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_11 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_aug_basis_gmp_safety_wit_12 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_aug_basis_gmp_safety_wit_13 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j <> n_pre)) (PreH2 : (j < cols)) (PreH3 : (a_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> aug_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (0 <= (n_pre * n_pre ))) (PreH13 : ((n_pre * n_pre ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= col_pre)) (PreH17 : (col_pre < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= j)) (PreH21 : (j <= cols)) (PreH22 : (idx = ((i * cols ) + j ))) (PreH23 : (0 <= idx)) (PreH24 : (idx <= (n_pre * cols ))) (PreH25 : (idx < (n_pre * cols ))) (PreH26 : (0 <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (((i * n_pre ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * n_pre ) + j )) ”
.

Definition build_aug_basis_gmp_safety_wit_14 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j <> n_pre)) (PreH2 : (j < cols)) (PreH3 : (a_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> aug_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (0 <= (n_pre * n_pre ))) (PreH13 : ((n_pre * n_pre ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= col_pre)) (PreH17 : (col_pre < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= j)) (PreH21 : (j <= cols)) (PreH22 : (idx = ((i * cols ) + j ))) (PreH23 : (0 <= idx)) (PreH24 : (idx <= (n_pre * cols ))) (PreH25 : (idx < (n_pre * cols ))) (PreH26 : (0 <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ ((i * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * n_pre )) ”
.

Definition build_aug_basis_gmp_safety_wit_15 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (1) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_16 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (1) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_17 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (1) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_18 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (1) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_19 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (0) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_20 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (0) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_21 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (0) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_22 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (0) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_23 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j <> n_pre)) (PreH2 : (j < cols)) (PreH3 : (a_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> aug_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (0 <= (n_pre * n_pre ))) (PreH13 : ((n_pre * n_pre ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= col_pre)) (PreH17 : (col_pre < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= j)) (PreH21 : (j <= cols)) (PreH22 : (idx = ((i * cols ) + j ))) (PreH23 : (0 <= idx)) (PreH24 : (idx <= (n_pre * cols ))) (PreH25 : (idx < (n_pre * cols ))) (PreH26 : (0 <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) ((Znth (((i * n_pre ) + j )) (la_low_level_spec) (0))) (laug_cur)) )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_24 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j <> n_pre)) (PreH2 : (j < cols)) (PreH3 : (a_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> aug_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (0 <= (n_pre * n_pre ))) (PreH13 : ((n_pre * n_pre ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= col_pre)) (PreH17 : (col_pre < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= j)) (PreH21 : (j <= cols)) (PreH22 : (idx = ((i * cols ) + j ))) (PreH23 : (0 <= idx)) (PreH24 : (idx <= (n_pre * cols ))) (PreH25 : (idx < (n_pre * cols ))) (PreH26 : (0 <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) ((Znth (((i * n_pre ) + j )) (la_low_level_spec) (0))) (laug_cur)) )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_25 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (1) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_26 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (1) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_27 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (1) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_28 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (1) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_29 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (0) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_30 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (0) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_31 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (0) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_32 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (0) (laug_cur)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_33 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j <> n_pre)) (PreH2 : (j < cols)) (PreH3 : (a_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> aug_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (0 <= (n_pre * n_pre ))) (PreH13 : ((n_pre * n_pre ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= col_pre)) (PreH17 : (col_pre < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= j)) (PreH21 : (j <= cols)) (PreH22 : (idx = ((i * cols ) + j ))) (PreH23 : (0 <= idx)) (PreH24 : (idx <= (n_pre * cols ))) (PreH25 : (idx < (n_pre * cols ))) (PreH26 : (0 <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) ((Znth (((i * n_pre ) + j )) (la_low_level_spec) (0))) (laug_cur)) )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_34 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j <> n_pre)) (PreH2 : (j < cols)) (PreH3 : (a_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> aug_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (0 <= (n_pre * n_pre ))) (PreH13 : ((n_pre * n_pre ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= col_pre)) (PreH17 : (col_pre < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= j)) (PreH21 : (j <= cols)) (PreH22 : (idx = ((i * cols ) + j ))) (PreH23 : (0 <= idx)) (PreH24 : (idx <= (n_pre * cols ))) (PreH25 : (idx < (n_pre * cols ))) (PreH26 : (0 <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) ((Znth (((i * n_pre ) + j )) (la_low_level_spec) (0))) (laug_cur)) )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_35 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (idx < (n_pre * cols ))) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_36 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (idx < (n_pre * cols ))) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_37 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (idx < (n_pre * cols ))) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_38 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (idx < (n_pre * cols ))) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_39 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_40 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_safety_wit_41 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_aug_basis_gmp_safety_wit_42 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_aug_basis_gmp_entail_wit_1 := 
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (laug_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (a_pre <> aug_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (0 <= (n_pre * n_pre ))) (PreH9 : ((n_pre * n_pre ) <= INT_MAX)) (PreH10 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH11 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH12 : (0 <= col_pre)) (PreH13 : (col_pre < n_pre)) (PreH14 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_low_level_spec )
|--
  EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (0 * (n_pre + 1 ) )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre (n_pre + 1 ) 0 (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug_cur )
) \/
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (laug_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (a_pre <> aug_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (0 <= (n_pre * n_pre ))) (PreH9 : ((n_pre * n_pre ) <= INT_MAX)) (PreH10 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH11 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH12 : (0 <= col_pre)) (PreH13 : (col_pre < n_pre)) (PreH14 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  TT && emp 
|--
  “ (partial_rep_matrix laug_low_level_spec n_pre (n_pre + 1 ) 0 (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  emp
).

Definition build_aug_basis_gmp_entail_wit_1_split_goal_1 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (laug_low_level_spec: (@list Z)) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (PreH1 : (a_pre <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (a_pre <> aug_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (2 <= zp_low_level_spec)) (PreH8 : (0 <= (n_pre * n_pre ))) (PreH9 : ((n_pre * n_pre ) <= INT_MAX)) (PreH10 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH11 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH12 : (0 <= col_pre)) (PreH13 : (col_pre < n_pre)) (PreH14 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) ,
  (partial_rep_matrix laug_low_level_spec n_pre (n_pre + 1 ) 0 (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )
.

Definition build_aug_basis_gmp_entail_wit_2 := 
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (idx = (i * cols ))) (PreH20 : (0 <= idx)) (PreH21 : (idx <= (n_pre * cols ))) (PreH22 : (INT_MIN <= idx)) (PreH23 : (idx <= INT_MAX)) (PreH24 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH26 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur_2 )
|--
  EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= cols) ” 
  &&  “ (idx = ((i * cols ) + 0 )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * cols )) ” 
  &&  “ (idx < (n_pre * cols )) ” 
  &&  “ (0 <= ((i * n_pre ) + 0 )) ” 
  &&  “ (((i * n_pre ) + 0 ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + 0 )) ” 
  &&  “ (((i * n_pre ) + 0 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= idx) ” 
  &&  “ (idx <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
) \/
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (idx = (i * cols ))) (PreH20 : (0 <= idx)) (PreH21 : (idx <= (n_pre * cols ))) (PreH22 : (INT_MIN <= idx)) (PreH23 : (idx <= INT_MAX)) (PreH24 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH26 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  TT && emp 
|--
  “ (((i * n_pre ) + 0 ) < (n_pre * n_pre )) ” 
  &&  “ ((i * (n_pre + 1 ) ) < (n_pre * (n_pre + 1 ) )) ”
  &&  emp
).

Definition build_aug_basis_gmp_entail_wit_2_split_goal_1 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (idx = (i * cols ))) (PreH20 : (0 <= idx)) (PreH21 : (idx <= (n_pre * cols ))) (PreH22 : (INT_MIN <= idx)) (PreH23 : (idx <= INT_MAX)) (PreH24 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH26 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (((i * n_pre ) + 0 ) < (n_pre * n_pre ))
.

Definition build_aug_basis_gmp_entail_wit_2_split_goal_2 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (i: Z) (cols: Z) (PreH1 : (i < n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (idx = (i * cols ))) (PreH20 : (0 <= idx)) (PreH21 : (idx <= (n_pre * cols ))) (PreH22 : (INT_MIN <= idx)) (PreH23 : (idx <= INT_MAX)) (PreH24 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH26 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((i * (n_pre + 1 ) ) < (n_pre * (n_pre + 1 ) ))
.

Definition build_aug_basis_gmp_entail_wit_3_1 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (1) (laug_cur_2)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((idx + 1 ) < (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((idx + 1 ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ ((j + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (0 <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
.

Definition build_aug_basis_gmp_entail_wit_3_2 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (1) (laug_cur_2)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((idx + 1 ) < (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((idx + 1 ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ ((j + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (0 <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
.

Definition build_aug_basis_gmp_entail_wit_3_3 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (0) (laug_cur_2)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((idx + 1 ) < (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((idx + 1 ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ ((j + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (0 <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
.

Definition build_aug_basis_gmp_entail_wit_3_4 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) (0) (laug_cur_2)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
|--
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((idx + 1 ) < (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((idx + 1 ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ ((j + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (0 <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
.

Definition build_aug_basis_gmp_entail_wit_3_5 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j <> n_pre)) (PreH2 : (j < cols)) (PreH3 : (a_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> aug_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (0 <= (n_pre * n_pre ))) (PreH13 : ((n_pre * n_pre ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= col_pre)) (PreH17 : (col_pre < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= j)) (PreH21 : (j <= cols)) (PreH22 : (idx = ((i * cols ) + j ))) (PreH23 : (0 <= idx)) (PreH24 : (idx <= (n_pre * cols ))) (PreH25 : (idx < (n_pre * cols ))) (PreH26 : (0 <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx) ((Znth (((i * n_pre ) + j )) (la_low_level_spec) (0))) (laug_cur_2)) )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((idx + 1 ) < (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
  ||
  (EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((idx + 1 ) = ((i * cols ) + (j + 1 ) )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * cols )) ” 
  &&  “ ((idx + 1 ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + (j + 1 ) )) ” 
  &&  “ (((i * n_pre ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols (idx + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur ))
.

Definition build_aug_basis_gmp_entail_wit_4_1 := 
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (idx < (n_pre * cols ))) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur_2 )
|--
  EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (idx = ((i + 1 ) * cols )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * cols )) ” 
  &&  “ (INT_MIN <= idx) ” 
  &&  “ (idx <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
) \/
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (idx < (n_pre * cols ))) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  TT && emp 
|--
  “ (((i * (n_pre + 1 ) ) + j ) = ((i + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition build_aug_basis_gmp_entail_wit_4_1_split_goal_1 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (idx < (n_pre * cols ))) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (((i * (n_pre + 1 ) ) + j ) = ((i + 1 ) * (n_pre + 1 ) ))
.

Definition build_aug_basis_gmp_entail_wit_4_2 := 
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (idx < (n_pre * cols ))) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur_2 )
|--
  EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (idx = ((i + 1 ) * cols )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * cols )) ” 
  &&  “ (INT_MIN <= idx) ” 
  &&  “ (idx <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
) \/
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (idx < (n_pre * cols ))) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  TT && emp 
|--
  “ (((i * (n_pre + 1 ) ) + j ) = ((i + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition build_aug_basis_gmp_entail_wit_4_2_split_goal_1 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (idx < (n_pre * cols ))) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (((i * (n_pre + 1 ) ) + j ) = ((i + 1 ) * (n_pre + 1 ) ))
.

Definition build_aug_basis_gmp_entail_wit_4_3 := 
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur_2 )
|--
  EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (idx = ((i + 1 ) * cols )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * cols )) ” 
  &&  “ (INT_MIN <= idx) ” 
  &&  “ (idx <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
) \/
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  TT && emp 
|--
  “ (((i * (n_pre + 1 ) ) + j ) = ((i + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition build_aug_basis_gmp_entail_wit_4_3_split_goal_1 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (j >= n_pre)) (PreH26 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH28 : (INT_MIN <= idx)) (PreH29 : (idx <= INT_MAX)) (PreH30 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH31 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (((i * (n_pre + 1 ) ) + j ) = ((i + 1 ) * (n_pre + 1 ) ))
.

Definition build_aug_basis_gmp_entail_wit_4_4 := 
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur_2 )
|--
  EX (laug_cur: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (idx = ((i + 1 ) * cols )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * cols )) ” 
  &&  “ (INT_MIN <= idx) ” 
  &&  “ (idx <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
) \/
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  TT && emp 
|--
  “ (((i * (n_pre + 1 ) ) + j ) = ((i + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition build_aug_basis_gmp_entail_wit_4_4_split_goal_1 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur_2: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j >= cols)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= cols)) (PreH21 : (idx = ((i * cols ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx <= (n_pre * cols ))) (PreH24 : (j >= cols)) (PreH25 : (0 <= ((i * n_pre ) + j ))) (PreH26 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH27 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH29 : (INT_MIN <= idx)) (PreH30 : (idx <= INT_MAX)) (PreH31 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH32 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (partial_rep_matrix laug_cur_2 n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (((i * (n_pre + 1 ) ) + j ) = ((i + 1 ) * (n_pre + 1 ) ))
.

Definition build_aug_basis_gmp_return_wit_1 := 
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (i: Z) (cols: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (idx = (i * cols ))) (PreH20 : (0 <= idx)) (PreH21 : (idx <= (n_pre * cols ))) (PreH22 : (INT_MIN <= idx)) (PreH23 : (idx <= INT_MAX)) (PreH24 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH26 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  EX (laug2: (@list Z)) ,
  “ (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
) \/
(
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (i: Z) (cols: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a_pre <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (a_pre <> aug_pre)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (2 <= zp_low_level_spec)) (PreH11 : (0 <= (n_pre * n_pre ))) (PreH12 : ((n_pre * n_pre ) <= INT_MAX)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= col_pre)) (PreH16 : (col_pre < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (idx = (i * cols ))) (PreH20 : (0 <= idx)) (PreH21 : (idx <= (n_pre * cols ))) (PreH22 : (INT_MIN <= idx)) (PreH23 : (idx <= INT_MAX)) (PreH24 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH26 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  EX (laug2: (@list Z)) ,
  “ (rep_matrix laug2 n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) laug2 )
).

Definition build_aug_basis_gmp_partial_solve_wit_1_pure := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (1 = 1) ” 
  &&  “ (0 <= 1) ”
.

Definition build_aug_basis_gmp_partial_solve_wit_1_aux := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (1 = 1) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (i = col_pre) ” 
  &&  “ (j = n_pre) ” 
  &&  “ (j < cols) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (idx = ((i * cols ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * cols )) ” 
  &&  “ (idx < (n_pre * cols )) ” 
  &&  “ (j >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + j )) ” 
  &&  “ (((i * n_pre ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= idx) ” 
  &&  “ (idx <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z (aug_pre + (idx * sizeof( "__mpz_struct" ))) (Znth (idx) (laug_cur) (0)) )
  **  (mpz_missing_i aug_pre idx 0 (n_pre * cols ) laug_cur )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
.

Definition build_aug_basis_gmp_partial_solve_wit_1 := build_aug_basis_gmp_partial_solve_wit_1_pure -> build_aug_basis_gmp_partial_solve_wit_1_aux.

Definition build_aug_basis_gmp_partial_solve_wit_2_pure := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (1 = 1) ” 
  &&  “ (0 <= 1) ”
.

Definition build_aug_basis_gmp_partial_solve_wit_2_aux := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i = col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (1 = 1) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (i = col_pre) ” 
  &&  “ (j = n_pre) ” 
  &&  “ (j < cols) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (idx = ((i * cols ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * cols )) ” 
  &&  “ (idx < (n_pre * cols )) ” 
  &&  “ (0 <= ((i * n_pre ) + j )) ” 
  &&  “ (((i * n_pre ) + j ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + j )) ” 
  &&  “ (((i * n_pre ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= idx) ” 
  &&  “ (idx <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z (aug_pre + (idx * sizeof( "__mpz_struct" ))) (Znth (idx) (laug_cur) (0)) )
  **  (mpz_missing_i aug_pre idx 0 (n_pre * cols ) laug_cur )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
.

Definition build_aug_basis_gmp_partial_solve_wit_2 := build_aug_basis_gmp_partial_solve_wit_2_pure -> build_aug_basis_gmp_partial_solve_wit_2_aux.

Definition build_aug_basis_gmp_partial_solve_wit_3_pure := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (0 = 0) ” 
  &&  “ (0 <= 0) ”
.

Definition build_aug_basis_gmp_partial_solve_wit_3_aux := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (j >= n_pre)) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (i <> col_pre) ” 
  &&  “ (j = n_pre) ” 
  &&  “ (j < cols) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (idx = ((i * cols ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * cols )) ” 
  &&  “ (idx < (n_pre * cols )) ” 
  &&  “ (j >= n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + j )) ” 
  &&  “ (((i * n_pre ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= idx) ” 
  &&  “ (idx <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z (aug_pre + (idx * sizeof( "__mpz_struct" ))) (Znth (idx) (laug_cur) (0)) )
  **  (mpz_missing_i aug_pre idx 0 (n_pre * cols ) laug_cur )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
.

Definition build_aug_basis_gmp_partial_solve_wit_3 := build_aug_basis_gmp_partial_solve_wit_3_pure -> build_aug_basis_gmp_partial_solve_wit_3_aux.

Definition build_aug_basis_gmp_partial_solve_wit_4_pure := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (0 = 0) ” 
  &&  “ (0 <= 0) ”
.

Definition build_aug_basis_gmp_partial_solve_wit_4_aux := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (i <> col_pre)) (PreH2 : (j = n_pre)) (PreH3 : (j < cols)) (PreH4 : (a_pre <> 0)) (PreH5 : (aug_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (a_pre <> aug_pre)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (2 <= zp_low_level_spec)) (PreH13 : (0 <= (n_pre * n_pre ))) (PreH14 : ((n_pre * n_pre ) <= INT_MAX)) (PreH15 : (0 <= (n_pre * cols ))) (PreH16 : ((n_pre * cols ) <= INT_MAX)) (PreH17 : (0 <= col_pre)) (PreH18 : (col_pre < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (idx = ((i * cols ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx <= (n_pre * cols ))) (PreH26 : (idx < (n_pre * cols ))) (PreH27 : (0 <= ((i * n_pre ) + j ))) (PreH28 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH29 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH30 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= idx)) (PreH32 : (idx <= INT_MAX)) (PreH33 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH35 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (i <> col_pre) ” 
  &&  “ (j = n_pre) ” 
  &&  “ (j < cols) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (idx = ((i * cols ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * cols )) ” 
  &&  “ (idx < (n_pre * cols )) ” 
  &&  “ (0 <= ((i * n_pre ) + j )) ” 
  &&  “ (((i * n_pre ) + j ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + j )) ” 
  &&  “ (((i * n_pre ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= idx) ” 
  &&  “ (idx <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z (aug_pre + (idx * sizeof( "__mpz_struct" ))) (Znth (idx) (laug_cur) (0)) )
  **  (mpz_missing_i aug_pre idx 0 (n_pre * cols ) laug_cur )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
.

Definition build_aug_basis_gmp_partial_solve_wit_4 := build_aug_basis_gmp_partial_solve_wit_4_pure -> build_aug_basis_gmp_partial_solve_wit_4_aux.

Definition build_aug_basis_gmp_partial_solve_wit_5 := 
forall (aug_pre: Z) (col_pre: Z) (a_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (la_low_level_spec: (@list Z)) (A_low_level_spec: matrix) (laug_cur: (@list Z)) (idx: Z) (j: Z) (i: Z) (cols: Z) (PreH1 : (j <> n_pre)) (PreH2 : (j < cols)) (PreH3 : (a_pre <> 0)) (PreH4 : (aug_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (a_pre <> aug_pre)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (2 <= zp_low_level_spec)) (PreH12 : (0 <= (n_pre * n_pre ))) (PreH13 : ((n_pre * n_pre ) <= INT_MAX)) (PreH14 : (0 <= (n_pre * cols ))) (PreH15 : ((n_pre * cols ) <= INT_MAX)) (PreH16 : (0 <= col_pre)) (PreH17 : (col_pre < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < n_pre)) (PreH20 : (0 <= j)) (PreH21 : (j <= cols)) (PreH22 : (idx = ((i * cols ) + j ))) (PreH23 : (0 <= idx)) (PreH24 : (idx <= (n_pre * cols ))) (PreH25 : (idx < (n_pre * cols ))) (PreH26 : (0 <= ((i * n_pre ) + j ))) (PreH27 : (((i * n_pre ) + j ) < (n_pre * n_pre ))) (PreH28 : (INT_MIN <= ((i * n_pre ) + j ))) (PreH29 : (((i * n_pre ) + j ) <= INT_MAX)) (PreH30 : (INT_MIN <= idx)) (PreH31 : (idx <= INT_MAX)) (PreH32 : (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec )) (PreH33 : (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec )) (PreH34 : (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array a_pre (n_pre * n_pre ) la_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) laug_cur )
|--
  “ (j <> n_pre) ” 
  &&  “ (j < cols) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (a_pre <> aug_pre) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (2 <= zp_low_level_spec) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (idx = ((i * cols ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * cols )) ” 
  &&  “ (idx < (n_pre * cols )) ” 
  &&  “ (0 <= ((i * n_pre ) + j )) ” 
  &&  “ (((i * n_pre ) + j ) < (n_pre * n_pre )) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + j )) ” 
  &&  “ (((i * n_pre ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= idx) ” 
  &&  “ (idx <= INT_MAX) ” 
  &&  “ (rep_matrix la_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre n_pre A_low_level_spec ) ” 
  &&  “ (partial_rep_matrix laug_cur n_pre cols idx (matrix_aug_basis (n_pre) (A_low_level_spec) (col_pre)) ) ”
  &&  (store_Z (aug_pre + (idx * sizeof( "__mpz_struct" ))) (Znth (idx) (laug_cur) (0)) )
  **  (store_Z (a_pre + (((i * n_pre ) + j ) * sizeof( "__mpz_struct" ))) (Znth (((i * n_pre ) + j )) (la_low_level_spec) (0)) )
  **  (mpz_missing_i aug_pre idx 0 (n_pre * cols ) laug_cur )
  **  (mpz_missing_i a_pre ((i * n_pre ) + j ) 0 (n_pre * n_pre ) la_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_build_aug_basis_gmp_safety_wit_1 : build_aug_basis_gmp_safety_wit_1.
Axiom proof_of_build_aug_basis_gmp_safety_wit_2 : build_aug_basis_gmp_safety_wit_2.
Axiom proof_of_build_aug_basis_gmp_safety_wit_3 : build_aug_basis_gmp_safety_wit_3.
Axiom proof_of_build_aug_basis_gmp_safety_wit_4 : build_aug_basis_gmp_safety_wit_4.
Axiom proof_of_build_aug_basis_gmp_safety_wit_5 : build_aug_basis_gmp_safety_wit_5.
Axiom proof_of_build_aug_basis_gmp_safety_wit_6 : build_aug_basis_gmp_safety_wit_6.
Axiom proof_of_build_aug_basis_gmp_safety_wit_7 : build_aug_basis_gmp_safety_wit_7.
Axiom proof_of_build_aug_basis_gmp_safety_wit_8 : build_aug_basis_gmp_safety_wit_8.
Axiom proof_of_build_aug_basis_gmp_safety_wit_9 : build_aug_basis_gmp_safety_wit_9.
Axiom proof_of_build_aug_basis_gmp_safety_wit_10 : build_aug_basis_gmp_safety_wit_10.
Axiom proof_of_build_aug_basis_gmp_safety_wit_11 : build_aug_basis_gmp_safety_wit_11.
Axiom proof_of_build_aug_basis_gmp_safety_wit_12 : build_aug_basis_gmp_safety_wit_12.
Axiom proof_of_build_aug_basis_gmp_safety_wit_13 : build_aug_basis_gmp_safety_wit_13.
Axiom proof_of_build_aug_basis_gmp_safety_wit_14 : build_aug_basis_gmp_safety_wit_14.
Axiom proof_of_build_aug_basis_gmp_safety_wit_15 : build_aug_basis_gmp_safety_wit_15.
Axiom proof_of_build_aug_basis_gmp_safety_wit_16 : build_aug_basis_gmp_safety_wit_16.
Axiom proof_of_build_aug_basis_gmp_safety_wit_17 : build_aug_basis_gmp_safety_wit_17.
Axiom proof_of_build_aug_basis_gmp_safety_wit_18 : build_aug_basis_gmp_safety_wit_18.
Axiom proof_of_build_aug_basis_gmp_safety_wit_19 : build_aug_basis_gmp_safety_wit_19.
Axiom proof_of_build_aug_basis_gmp_safety_wit_20 : build_aug_basis_gmp_safety_wit_20.
Axiom proof_of_build_aug_basis_gmp_safety_wit_21 : build_aug_basis_gmp_safety_wit_21.
Axiom proof_of_build_aug_basis_gmp_safety_wit_22 : build_aug_basis_gmp_safety_wit_22.
Axiom proof_of_build_aug_basis_gmp_safety_wit_23 : build_aug_basis_gmp_safety_wit_23.
Axiom proof_of_build_aug_basis_gmp_safety_wit_24 : build_aug_basis_gmp_safety_wit_24.
Axiom proof_of_build_aug_basis_gmp_safety_wit_25 : build_aug_basis_gmp_safety_wit_25.
Axiom proof_of_build_aug_basis_gmp_safety_wit_26 : build_aug_basis_gmp_safety_wit_26.
Axiom proof_of_build_aug_basis_gmp_safety_wit_27 : build_aug_basis_gmp_safety_wit_27.
Axiom proof_of_build_aug_basis_gmp_safety_wit_28 : build_aug_basis_gmp_safety_wit_28.
Axiom proof_of_build_aug_basis_gmp_safety_wit_29 : build_aug_basis_gmp_safety_wit_29.
Axiom proof_of_build_aug_basis_gmp_safety_wit_30 : build_aug_basis_gmp_safety_wit_30.
Axiom proof_of_build_aug_basis_gmp_safety_wit_31 : build_aug_basis_gmp_safety_wit_31.
Axiom proof_of_build_aug_basis_gmp_safety_wit_32 : build_aug_basis_gmp_safety_wit_32.
Axiom proof_of_build_aug_basis_gmp_safety_wit_33 : build_aug_basis_gmp_safety_wit_33.
Axiom proof_of_build_aug_basis_gmp_safety_wit_34 : build_aug_basis_gmp_safety_wit_34.
Axiom proof_of_build_aug_basis_gmp_safety_wit_35 : build_aug_basis_gmp_safety_wit_35.
Axiom proof_of_build_aug_basis_gmp_safety_wit_36 : build_aug_basis_gmp_safety_wit_36.
Axiom proof_of_build_aug_basis_gmp_safety_wit_37 : build_aug_basis_gmp_safety_wit_37.
Axiom proof_of_build_aug_basis_gmp_safety_wit_38 : build_aug_basis_gmp_safety_wit_38.
Axiom proof_of_build_aug_basis_gmp_safety_wit_39 : build_aug_basis_gmp_safety_wit_39.
Axiom proof_of_build_aug_basis_gmp_safety_wit_40 : build_aug_basis_gmp_safety_wit_40.
Axiom proof_of_build_aug_basis_gmp_safety_wit_41 : build_aug_basis_gmp_safety_wit_41.
Axiom proof_of_build_aug_basis_gmp_safety_wit_42 : build_aug_basis_gmp_safety_wit_42.
Axiom proof_of_build_aug_basis_gmp_entail_wit_1 : build_aug_basis_gmp_entail_wit_1.
Axiom proof_of_build_aug_basis_gmp_entail_wit_2 : build_aug_basis_gmp_entail_wit_2.
Axiom proof_of_build_aug_basis_gmp_entail_wit_3_1 : build_aug_basis_gmp_entail_wit_3_1.
Axiom proof_of_build_aug_basis_gmp_entail_wit_3_2 : build_aug_basis_gmp_entail_wit_3_2.
Axiom proof_of_build_aug_basis_gmp_entail_wit_3_3 : build_aug_basis_gmp_entail_wit_3_3.
Axiom proof_of_build_aug_basis_gmp_entail_wit_3_4 : build_aug_basis_gmp_entail_wit_3_4.
Axiom proof_of_build_aug_basis_gmp_entail_wit_3_5 : build_aug_basis_gmp_entail_wit_3_5.
Axiom proof_of_build_aug_basis_gmp_entail_wit_4_1 : build_aug_basis_gmp_entail_wit_4_1.
Axiom proof_of_build_aug_basis_gmp_entail_wit_4_2 : build_aug_basis_gmp_entail_wit_4_2.
Axiom proof_of_build_aug_basis_gmp_entail_wit_4_3 : build_aug_basis_gmp_entail_wit_4_3.
Axiom proof_of_build_aug_basis_gmp_entail_wit_4_4 : build_aug_basis_gmp_entail_wit_4_4.
Axiom proof_of_build_aug_basis_gmp_return_wit_1 : build_aug_basis_gmp_return_wit_1.
Axiom proof_of_build_aug_basis_gmp_partial_solve_wit_1_pure : build_aug_basis_gmp_partial_solve_wit_1_pure.
Axiom proof_of_build_aug_basis_gmp_partial_solve_wit_1 : build_aug_basis_gmp_partial_solve_wit_1.
Axiom proof_of_build_aug_basis_gmp_partial_solve_wit_2_pure : build_aug_basis_gmp_partial_solve_wit_2_pure.
Axiom proof_of_build_aug_basis_gmp_partial_solve_wit_2 : build_aug_basis_gmp_partial_solve_wit_2.
Axiom proof_of_build_aug_basis_gmp_partial_solve_wit_3_pure : build_aug_basis_gmp_partial_solve_wit_3_pure.
Axiom proof_of_build_aug_basis_gmp_partial_solve_wit_3 : build_aug_basis_gmp_partial_solve_wit_3.
Axiom proof_of_build_aug_basis_gmp_partial_solve_wit_4_pure : build_aug_basis_gmp_partial_solve_wit_4_pure.
Axiom proof_of_build_aug_basis_gmp_partial_solve_wit_4 : build_aug_basis_gmp_partial_solve_wit_4.
Axiom proof_of_build_aug_basis_gmp_partial_solve_wit_5 : build_aug_basis_gmp_partial_solve_wit_5.

End VC_Correct.
