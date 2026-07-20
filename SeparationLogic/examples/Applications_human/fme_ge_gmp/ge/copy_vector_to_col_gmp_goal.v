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

(*----- Function copy_vector_to_col_gmp -----*)

Definition copy_vector_to_col_gmp_safety_wit_1 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (PreH1 : (x_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (x_pre <> inv_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * n_pre ))) (PreH7 : ((n_pre * n_pre ) <= INT_MAX)) (PreH8 : (0 <= col_pre)) (PreH9 : (col_pre < n_pre)) (PreH10 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH11 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition copy_vector_to_col_gmp_safety_wit_2 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (i >= n_pre)) (PreH16 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH17 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH18 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH19 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_3 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (i >= n_pre)) (PreH16 : (i >= n_pre)) (PreH17 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH18 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_4 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH18 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH19 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH20 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_5 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH19 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_6 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH19 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_7 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (i >= n_pre)) (PreH15 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH16 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH17 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH18 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_8 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (i >= n_pre)) (PreH15 : (i >= n_pre)) (PreH16 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH17 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_9 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH17 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH18 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH19 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_10 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH17 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH18 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH19 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_11 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i >= n_pre)) (PreH17 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH18 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_12 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i >= n_pre)) (PreH17 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH18 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ False ”
.

Definition copy_vector_to_col_gmp_safety_wit_13 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH18 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH19 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH20 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ (((i * n_pre ) + col_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * n_pre ) + col_pre )) ”
.

Definition copy_vector_to_col_gmp_safety_wit_14 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH18 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH19 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH20 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ ((i * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * n_pre )) ”
.

Definition copy_vector_to_col_gmp_safety_wit_15 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH18 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH19 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH20 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (mpz_array inv_pre (n_pre * n_pre ) (replace_Znth (((i * n_pre ) + col_pre )) ((Znth (i) (lx_low_level_spec) (0))) (linv_cur)) )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition copy_vector_to_col_gmp_safety_wit_16 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH18 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH19 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH20 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (mpz_array inv_pre (n_pre * n_pre ) (replace_Znth (((i * n_pre ) + col_pre )) ((Znth (i) (lx_low_level_spec) (0))) (linv_cur)) )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "col" ) )) # Int  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition copy_vector_to_col_gmp_entail_wit_1 := 
(
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (PreH1 : (x_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (x_pre <> inv_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * n_pre ))) (PreH7 : ((n_pre * n_pre ) <= INT_MAX)) (PreH8 : (0 <= col_pre)) (PreH9 : (col_pre < n_pre)) (PreH10 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH11 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) ,
  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_low_level_spec )
|--
  EX (linv_cur: (@list Z)) ,
  “ (x_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (x_pre <> inv_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= ((0 * n_pre ) + col_pre )) ” 
  &&  “ (((0 * n_pre ) + col_pre ) < (n_pre * n_pre )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (INT_MIN <= ((0 * n_pre ) + col_pre )) ” 
  &&  “ (((0 * n_pre ) + col_pre ) <= INT_MAX) ” 
  &&  “ (rep_vector lx_low_level_spec n_pre X_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_col_copy linv_cur n_pre col_pre 0 B_low_level_spec X_low_level_spec ) ”
  &&  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
) \/
(
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (PreH1 : (x_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (x_pre <> inv_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * n_pre ))) (PreH7 : ((n_pre * n_pre ) <= INT_MAX)) (PreH8 : (0 <= col_pre)) (PreH9 : (col_pre < n_pre)) (PreH10 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH11 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) ,
  TT && emp 
|--
  “ (partial_rep_matrix_col_copy linv_low_level_spec n_pre col_pre 0 B_low_level_spec X_low_level_spec ) ”
  &&  emp
).

Definition copy_vector_to_col_gmp_entail_wit_1_split_goal_1 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (linv_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (PreH1 : (x_pre <> 0)) (PreH2 : (inv_pre <> 0)) (PreH3 : (x_pre <> inv_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * n_pre ))) (PreH7 : ((n_pre * n_pre ) <= INT_MAX)) (PreH8 : (0 <= col_pre)) (PreH9 : (col_pre < n_pre)) (PreH10 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH11 : (partial_rep_matrix_cols linv_low_level_spec n_pre col_pre B_low_level_spec )) ,
  (partial_rep_matrix_col_copy linv_low_level_spec n_pre col_pre 0 B_low_level_spec X_low_level_spec )
.

Definition copy_vector_to_col_gmp_entail_wit_2 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH18 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH19 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH20 : (partial_rep_matrix_col_copy linv_cur_2 n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (mpz_array inv_pre (n_pre * n_pre ) (replace_Znth (((i * n_pre ) + col_pre )) ((Znth (i) (lx_low_level_spec) (0))) (linv_cur_2)) )
  **  (mpz_array x_pre n_pre lx_low_level_spec )
|--
  (EX (linv_cur: (@list Z)) ,
  “ (x_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (x_pre <> inv_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((i + 1 ) * n_pre ) + col_pre )) ” 
  &&  “ ((((i + 1 ) * n_pre ) + col_pre ) < (n_pre * n_pre )) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * n_pre ) + col_pre )) ” 
  &&  “ ((((i + 1 ) * n_pre ) + col_pre ) <= INT_MAX) ” 
  &&  “ (rep_vector lx_low_level_spec n_pre X_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_col_copy linv_cur n_pre col_pre (i + 1 ) B_low_level_spec X_low_level_spec ) ”
  &&  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur ))
  ||
  (EX (linv_cur: (@list Z)) ,
  “ (x_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (x_pre <> inv_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((i + 1 ) * n_pre ) + col_pre )) ” 
  &&  “ ((((i + 1 ) * n_pre ) + col_pre ) < (n_pre * n_pre )) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (rep_vector lx_low_level_spec n_pre X_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_col_copy linv_cur n_pre col_pre (i + 1 ) B_low_level_spec X_low_level_spec ) ”
  &&  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur ))
  ||
  (EX (linv_cur: (@list Z)) ,
  “ (x_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (x_pre <> inv_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (((i + 1 ) * n_pre ) + col_pre )) ” 
  &&  “ ((((i + 1 ) * n_pre ) + col_pre ) < (n_pre * n_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * n_pre ) + col_pre )) ” 
  &&  “ ((((i + 1 ) * n_pre ) + col_pre ) <= INT_MAX) ” 
  &&  “ (rep_vector lx_low_level_spec n_pre X_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_col_copy linv_cur n_pre col_pre (i + 1 ) B_low_level_spec X_low_level_spec ) ”
  &&  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur ))
  ||
  (EX (linv_cur: (@list Z)) ,
  “ (x_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (x_pre <> inv_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (INT_MIN <= (((i + 1 ) * n_pre ) + col_pre )) ” 
  &&  “ ((((i + 1 ) * n_pre ) + col_pre ) <= INT_MAX) ” 
  &&  “ (rep_vector lx_low_level_spec n_pre X_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_col_copy linv_cur n_pre col_pre (i + 1 ) B_low_level_spec X_low_level_spec ) ”
  &&  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur ))
  ||
  (EX (linv_cur: (@list Z)) ,
  “ (x_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (x_pre <> inv_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (rep_vector lx_low_level_spec n_pre X_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_col_copy linv_cur n_pre col_pre (i + 1 ) B_low_level_spec X_low_level_spec ) ”
  &&  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur ))
.

Definition copy_vector_to_col_gmp_return_wit_1 := 
(
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (i >= n_pre)) (PreH16 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH17 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH18 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH19 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  EX (linv2: (@list Z)) ,
  “ (partial_rep_matrix_cols linv2 n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) ) ”
  &&  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
) \/
(
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (i >= n_pre)) (PreH16 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH17 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH18 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH19 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  TT && emp 
|--
  “ (partial_rep_matrix_cols linv_cur n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) ) ”
  &&  emp
).

Definition copy_vector_to_col_gmp_return_wit_1_split_goal_1 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (i >= n_pre)) (PreH16 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH17 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH18 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH19 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (partial_rep_matrix_cols linv_cur n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) )
.

Definition copy_vector_to_col_gmp_return_wit_2 := 
(
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (i >= n_pre)) (PreH16 : (i >= n_pre)) (PreH17 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH18 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  EX (linv2: (@list Z)) ,
  “ (partial_rep_matrix_cols linv2 n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) ) ”
  &&  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
) \/
(
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (i >= n_pre)) (PreH16 : (i >= n_pre)) (PreH17 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH18 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  TT && emp 
|--
  “ (partial_rep_matrix_cols linv_cur n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) ) ”
  &&  emp
).

Definition copy_vector_to_col_gmp_return_wit_2_split_goal_1 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (i >= n_pre)) (PreH16 : (i >= n_pre)) (PreH17 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH18 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (partial_rep_matrix_cols linv_cur n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) )
.

Definition copy_vector_to_col_gmp_return_wit_3 := 
(
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (i >= n_pre)) (PreH15 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH16 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH17 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH18 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  EX (linv2: (@list Z)) ,
  “ (partial_rep_matrix_cols linv2 n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) ) ”
  &&  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
) \/
(
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (i >= n_pre)) (PreH15 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH16 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH17 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH18 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  TT && emp 
|--
  “ (partial_rep_matrix_cols linv_cur n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) ) ”
  &&  emp
).

Definition copy_vector_to_col_gmp_return_wit_3_split_goal_1 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (i >= n_pre)) (PreH15 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH16 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH17 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH18 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (partial_rep_matrix_cols linv_cur n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) )
.

Definition copy_vector_to_col_gmp_return_wit_4 := 
(
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (i >= n_pre)) (PreH15 : (i >= n_pre)) (PreH16 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH17 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  EX (linv2: (@list Z)) ,
  “ (partial_rep_matrix_cols linv2 n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) ) ”
  &&  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv2 )
) \/
(
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (i >= n_pre)) (PreH15 : (i >= n_pre)) (PreH16 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH17 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  TT && emp 
|--
  “ (partial_rep_matrix_cols linv_cur n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) ) ”
  &&  emp
).

Definition copy_vector_to_col_gmp_return_wit_4_split_goal_1 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i >= n_pre)) (PreH14 : (i >= n_pre)) (PreH15 : (i >= n_pre)) (PreH16 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH17 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (partial_rep_matrix_cols linv_cur n_pre (col_pre + 1 ) (matrix_set_col (B_low_level_spec) (col_pre) (X_low_level_spec)) )
.

Definition copy_vector_to_col_gmp_partial_solve_wit_1 := 
forall (inv_pre: Z) (col_pre: Z) (x_pre: Z) (n_pre: Z) (lx_low_level_spec: (@list Z)) (X_low_level_spec: vector) (B_low_level_spec: matrix) (linv_cur: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (x_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (x_pre <> inv_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (0 <= (n_pre * n_pre ))) (PreH8 : ((n_pre * n_pre ) <= INT_MAX)) (PreH9 : (0 <= col_pre)) (PreH10 : (col_pre < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= ((i * n_pre ) + col_pre ))) (PreH14 : (((i * n_pre ) + col_pre ) < (n_pre * n_pre ))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (INT_MIN <= ((i * n_pre ) + col_pre ))) (PreH18 : (((i * n_pre ) + col_pre ) <= INT_MAX)) (PreH19 : (rep_vector lx_low_level_spec n_pre X_low_level_spec )) (PreH20 : (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec )) ,
  (mpz_array x_pre n_pre lx_low_level_spec )
  **  (mpz_array inv_pre (n_pre * n_pre ) linv_cur )
|--
  “ (i < n_pre) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (x_pre <> inv_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= col_pre) ” 
  &&  “ (col_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= ((i * n_pre ) + col_pre )) ” 
  &&  “ (((i * n_pre ) + col_pre ) < (n_pre * n_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (INT_MIN <= ((i * n_pre ) + col_pre )) ” 
  &&  “ (((i * n_pre ) + col_pre ) <= INT_MAX) ” 
  &&  “ (rep_vector lx_low_level_spec n_pre X_low_level_spec ) ” 
  &&  “ (partial_rep_matrix_col_copy linv_cur n_pre col_pre i B_low_level_spec X_low_level_spec ) ”
  &&  (store_Z (inv_pre + (((i * n_pre ) + col_pre ) * sizeof( "__mpz_struct" ))) (Znth (((i * n_pre ) + col_pre )) (linv_cur) (0)) )
  **  (store_Z (x_pre + (i * sizeof( "__mpz_struct" ))) (Znth (i) (lx_low_level_spec) (0)) )
  **  (mpz_missing_i inv_pre ((i * n_pre ) + col_pre ) 0 (n_pre * n_pre ) linv_cur )
  **  (mpz_missing_i x_pre i 0 n_pre lx_low_level_spec )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_copy_vector_to_col_gmp_safety_wit_1 : copy_vector_to_col_gmp_safety_wit_1.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_2 : copy_vector_to_col_gmp_safety_wit_2.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_3 : copy_vector_to_col_gmp_safety_wit_3.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_4 : copy_vector_to_col_gmp_safety_wit_4.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_5 : copy_vector_to_col_gmp_safety_wit_5.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_6 : copy_vector_to_col_gmp_safety_wit_6.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_7 : copy_vector_to_col_gmp_safety_wit_7.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_8 : copy_vector_to_col_gmp_safety_wit_8.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_9 : copy_vector_to_col_gmp_safety_wit_9.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_10 : copy_vector_to_col_gmp_safety_wit_10.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_11 : copy_vector_to_col_gmp_safety_wit_11.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_12 : copy_vector_to_col_gmp_safety_wit_12.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_13 : copy_vector_to_col_gmp_safety_wit_13.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_14 : copy_vector_to_col_gmp_safety_wit_14.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_15 : copy_vector_to_col_gmp_safety_wit_15.
Axiom proof_of_copy_vector_to_col_gmp_safety_wit_16 : copy_vector_to_col_gmp_safety_wit_16.
Axiom proof_of_copy_vector_to_col_gmp_entail_wit_1 : copy_vector_to_col_gmp_entail_wit_1.
Axiom proof_of_copy_vector_to_col_gmp_entail_wit_2 : copy_vector_to_col_gmp_entail_wit_2.
Axiom proof_of_copy_vector_to_col_gmp_return_wit_1 : copy_vector_to_col_gmp_return_wit_1.
Axiom proof_of_copy_vector_to_col_gmp_return_wit_2 : copy_vector_to_col_gmp_return_wit_2.
Axiom proof_of_copy_vector_to_col_gmp_return_wit_3 : copy_vector_to_col_gmp_return_wit_3.
Axiom proof_of_copy_vector_to_col_gmp_return_wit_4 : copy_vector_to_col_gmp_return_wit_4.
Axiom proof_of_copy_vector_to_col_gmp_partial_solve_wit_1 : copy_vector_to_col_gmp_partial_solve_wit_1.

End VC_Correct.
