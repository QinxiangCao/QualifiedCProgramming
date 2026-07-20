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

(*----- Function row_elim_mod_gmp -----*)

Definition row_elim_mod_gmp_safety_wit_1 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (factor_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (zp_low_level_spec > 0)) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (0 <= pivot_pre)) (PreH10 : (pivot_pre < n_pre)) (PreH11 : (0 <= target_pre)) (PreH12 : (target_pre < n_pre)) (PreH13 : (pivot_pre <> target_pre)) (PreH14 : (0 <= zfactor_low_level_spec)) (PreH15 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH16 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition row_elim_mod_gmp_safety_wit_2 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (factor_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (zp_low_level_spec > 0)) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (0 <= pivot_pre)) (PreH10 : (pivot_pre < n_pre)) (PreH11 : (0 <= target_pre)) (PreH12 : (target_pre < n_pre)) (PreH13 : (pivot_pre <> target_pre)) (PreH14 : (0 <= zfactor_low_level_spec)) (PreH15 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH16 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition row_elim_mod_gmp_safety_wit_3 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (factor_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (zp_low_level_spec > 0)) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (0 <= pivot_pre)) (PreH10 : (pivot_pre < n_pre)) (PreH11 : (0 <= target_pre)) (PreH12 : (target_pre < n_pre)) (PreH13 : (pivot_pre <> target_pre)) (PreH14 : (0 <= zfactor_low_level_spec)) (PreH15 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH16 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cols" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition row_elim_mod_gmp_safety_wit_4 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (0 <= ((pivot_pre * cols ) + j ))) (PreH25 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition row_elim_mod_gmp_safety_wit_5 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (j >= cols)) (PreH25 : (INT_MIN <= (target_pre * cols ))) (PreH26 : ((target_pre * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= (pivot_pre * cols ))) (PreH28 : ((pivot_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH30 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH32 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition row_elim_mod_gmp_safety_wit_6 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (j >= cols)) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition row_elim_mod_gmp_safety_wit_7 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((target_pre * cols ) + j )) ”
.

Definition row_elim_mod_gmp_safety_wit_8 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (target_pre * cols )) ”
.

Definition row_elim_mod_gmp_safety_wit_9 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((( &( "pidx" ) )) # Int  |->_)
  **  ((( &( "idx" ) )) # Int  |-> ((target_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((pivot_pre * cols ) + j )) ”
.

Definition row_elim_mod_gmp_safety_wit_10 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((( &( "pidx" ) )) # Int  |->_)
  **  ((( &( "idx" ) )) # Int  |-> ((target_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot_pre * cols )) ”
.

Definition row_elim_mod_gmp_safety_wit_11 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec ((Znth (((target_pre * cols ) + j )) (lcur) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) ) out )) (PreH2 : (j < cols)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (factor_pre <> 0)) (PreH6 : (prod <> 0)) (PreH7 : (v <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (zp_low_level_spec > 0)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= pivot_pre)) (PreH16 : (pivot_pre < n_pre)) (PreH17 : (0 <= target_pre)) (PreH18 : (target_pre < n_pre)) (PreH19 : (pivot_pre <> target_pre)) (PreH20 : (0 <= zfactor_low_level_spec)) (PreH21 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH22 : (0 <= j)) (PreH23 : (j <= cols)) (PreH24 : (0 <= ((target_pre * cols ) + j ))) (PreH25 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH26 : (0 <= ((pivot_pre * cols ) + j ))) (PreH27 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (target_pre * cols ))) (PreH29 : ((target_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= (pivot_pre * cols ))) (PreH31 : ((pivot_pre * cols ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH33 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH35 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH36 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH38 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (((target_pre * cols ) + j )) (out) (lcur)) )
  **  (store_Z v ((Znth (((target_pre * cols ) + j )) (lcur) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot_pre * cols ) + j ))
  **  ((( &( "idx" ) )) # Int  |-> ((target_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition row_elim_mod_gmp_safety_wit_12 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec ((Znth (((target_pre * cols ) + j )) (lcur) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) ) out )) (PreH2 : (j < cols)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (factor_pre <> 0)) (PreH6 : (prod <> 0)) (PreH7 : (v <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (zp_low_level_spec > 0)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= pivot_pre)) (PreH16 : (pivot_pre < n_pre)) (PreH17 : (0 <= target_pre)) (PreH18 : (target_pre < n_pre)) (PreH19 : (pivot_pre <> target_pre)) (PreH20 : (0 <= zfactor_low_level_spec)) (PreH21 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH22 : (0 <= j)) (PreH23 : (j <= cols)) (PreH24 : (0 <= ((target_pre * cols ) + j ))) (PreH25 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH26 : (0 <= ((pivot_pre * cols ) + j ))) (PreH27 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (target_pre * cols ))) (PreH29 : ((target_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= (pivot_pre * cols ))) (PreH31 : ((pivot_pre * cols ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH33 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH35 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH36 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH38 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (((target_pre * cols ) + j )) (out) (lcur)) )
  **  (store_Z v ((Znth (((target_pre * cols ) + j )) (lcur) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot_pre * cols ) + j ))
  **  ((( &( "idx" ) )) # Int  |-> ((target_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition row_elim_mod_gmp_entail_wit_1 := 
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (factor_pre <> 0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (zp_low_level_spec > 0)) (PreH9 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH10 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH11 : (0 <= pivot_pre)) (PreH12 : (pivot_pre < n_pre)) (PreH13 : (0 <= target_pre)) (PreH14 : (target_pre < n_pre)) (PreH15 : (pivot_pre <> target_pre)) (PreH16 : (0 <= zfactor_low_level_spec)) (PreH17 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH18 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  EX (zprod: Z)  (zv: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((target_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((target_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((pivot_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((pivot_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) )) ” 
  &&  “ (INT_MIN <= (target_pre * (n_pre + 1 ) )) ” 
  &&  “ ((target_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * (n_pre + 1 ) )) ” 
  &&  “ ((pivot_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((target_pre * (n_pre + 1 ) ) + 0 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((pivot_pre * (n_pre + 1 ) ) + 0 ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre (n_pre + 1 ) M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec 0 ) ”
  &&  (store_Z retval_2 zv )
  **  (store_Z retval zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
) \/
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (factor_pre <> 0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (zp_low_level_spec > 0)) (PreH9 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH10 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH11 : (0 <= pivot_pre)) (PreH12 : (pivot_pre < n_pre)) (PreH13 : (0 <= target_pre)) (PreH14 : (target_pre < n_pre)) (PreH15 : (pivot_pre <> target_pre)) (PreH16 : (0 <= zfactor_low_level_spec)) (PreH17 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH18 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
|--
  EX (zprod: Z)  (zv: Z) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((target_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((target_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((pivot_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((pivot_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) )) ” 
  &&  “ (INT_MIN <= (target_pre * (n_pre + 1 ) )) ” 
  &&  “ ((target_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * (n_pre + 1 ) )) ” 
  &&  “ ((pivot_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((target_pre * (n_pre + 1 ) ) + 0 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((pivot_pre * (n_pre + 1 ) ) + 0 ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (row_elim_prefix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec 0 ) ”
  &&  (store_Z retval_2 zv )
  **  (store_Z retval zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
).

Definition row_elim_mod_gmp_entail_wit_2 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur_2: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec ((Znth (((target_pre * cols ) + j )) (lcur_2) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur_2) (0)) ) ) out )) (PreH2 : (j < cols)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (factor_pre <> 0)) (PreH6 : (prod <> 0)) (PreH7 : (v <> 0)) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (cols = (n_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 256)) (PreH12 : (zp_low_level_spec > 0)) (PreH13 : (0 <= (n_pre * cols ))) (PreH14 : ((n_pre * cols ) <= INT_MAX)) (PreH15 : (0 <= pivot_pre)) (PreH16 : (pivot_pre < n_pre)) (PreH17 : (0 <= target_pre)) (PreH18 : (target_pre < n_pre)) (PreH19 : (pivot_pre <> target_pre)) (PreH20 : (0 <= zfactor_low_level_spec)) (PreH21 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH22 : (0 <= j)) (PreH23 : (j <= cols)) (PreH24 : (0 <= ((target_pre * cols ) + j ))) (PreH25 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH26 : (0 <= ((pivot_pre * cols ) + j ))) (PreH27 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH28 : (INT_MIN <= (target_pre * cols ))) (PreH29 : ((target_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= (pivot_pre * cols ))) (PreH31 : ((pivot_pre * cols ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH33 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH35 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH36 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH38 : (row_elim_prefix lcur_2 n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (((target_pre * cols ) + j )) (out) (lcur_2)) )
  **  (store_Z v ((Znth (((target_pre * cols ) + j )) (lcur_2) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur_2) (0)) ) ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur_2) (0)) ) )
  **  (store_Z factor_pre zfactor_low_level_spec )
|--
  (EX (zprod: Z)  (zv: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((pivot_pre * cols ) + (j + 1 ) ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((target_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((pivot_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec (j + 1 ) ) ”
  &&  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (EX (zprod: Z)  (zv: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((target_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((pivot_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec (j + 1 ) ) ”
  &&  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (EX (zprod: Z)  (zv: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((target_pre * cols ) + (j + 1 ) ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((pivot_pre * cols ) + (j + 1 ) ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((target_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((pivot_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec (j + 1 ) ) ”
  &&  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (EX (zprod: Z)  (zv: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((target_pre * cols ) + (j + 1 ) ) < (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((target_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((pivot_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec (j + 1 ) ) ”
  &&  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
.

Definition row_elim_mod_gmp_return_wit_1 := 
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (0 <= ((pivot_pre * cols ) + j ))) (PreH25 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (0 <= ((pivot_pre * cols ) + j ))) (PreH25 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition row_elim_mod_gmp_return_wit_2 := 
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (j >= cols)) (PreH25 : (INT_MIN <= (target_pre * cols ))) (PreH26 : ((target_pre * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= (pivot_pre * cols ))) (PreH28 : ((pivot_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH30 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH32 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (j >= cols)) (PreH25 : (INT_MIN <= (target_pre * cols ))) (PreH26 : ((target_pre * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= (pivot_pre * cols ))) (PreH28 : ((pivot_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH30 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH32 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition row_elim_mod_gmp_return_wit_3 := 
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition row_elim_mod_gmp_return_wit_4 := 
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (j >= cols)) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (j >= cols)) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_elim_mod (zp_low_level_spec) (M_low_level_spec) (pivot_pre) (target_pre) (zfactor_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition row_elim_mod_gmp_partial_solve_wit_1 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (factor_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (zp_low_level_spec > 0)) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (0 <= pivot_pre)) (PreH10 : (pivot_pre < n_pre)) (PreH11 : (0 <= target_pre)) (PreH12 : (target_pre < n_pre)) (PreH13 : (pivot_pre <> target_pre)) (PreH14 : (0 <= zfactor_low_level_spec)) (PreH15 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH16 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH17 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition row_elim_mod_gmp_partial_solve_wit_2 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (zp_low_level_spec > 0)) (PreH8 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH9 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH10 : (0 <= pivot_pre)) (PreH11 : (pivot_pre < n_pre)) (PreH12 : (0 <= target_pre)) (PreH13 : (target_pre < n_pre)) (PreH14 : (pivot_pre <> target_pre)) (PreH15 : (0 <= zfactor_low_level_spec)) (PreH16 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH17 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition row_elim_mod_gmp_partial_solve_wit_3 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (zp_low_level_spec > 0)) (PreH8 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH9 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH10 : (0 <= pivot_pre)) (PreH11 : (pivot_pre < n_pre)) (PreH12 : (0 <= target_pre)) (PreH13 : (target_pre < n_pre)) (PreH14 : (pivot_pre <> target_pre)) (PreH15 : (0 <= zfactor_low_level_spec)) (PreH16 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH17 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH18 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition row_elim_mod_gmp_partial_solve_wit_4 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (factor_pre <> 0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (zp_low_level_spec > 0)) (PreH9 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH10 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH11 : (0 <= pivot_pre)) (PreH12 : (pivot_pre < n_pre)) (PreH13 : (0 <= target_pre)) (PreH14 : (target_pre < n_pre)) (PreH15 : (pivot_pre <> target_pre)) (PreH16 : (0 <= zfactor_low_level_spec)) (PreH17 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH18 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH19 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition row_elim_mod_gmp_partial_solve_wit_5 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j < cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z prod zprod )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (store_Z (aug_pre + (((pivot_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre ((pivot_pre * cols ) + j ) 0 (n_pre * cols ) lcur )
  **  (store_Z v zv )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition row_elim_mod_gmp_partial_solve_wit_6 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (store_Z v zv )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (j < cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z v zv )
  **  (store_Z (aug_pre + (((target_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) (Znth (((target_pre * cols ) + j )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre ((target_pre * cols ) + j ) 0 (n_pre * cols ) lcur )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition row_elim_mod_gmp_partial_solve_wit_7_pure := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z v (Znth (((target_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot_pre * cols ) + j ))
  **  ((( &( "idx" ) )) # Int  |-> ((target_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (v = v) ”
.

Definition row_elim_mod_gmp_partial_solve_wit_7_aux := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z v (Znth (((target_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (v = v) ” 
  &&  “ (j < cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z v (Znth (((target_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition row_elim_mod_gmp_partial_solve_wit_7 := row_elim_mod_gmp_partial_solve_wit_7_pure -> row_elim_mod_gmp_partial_solve_wit_7_aux.

Definition row_elim_mod_gmp_partial_solve_wit_8_pure := 
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z v ((Znth (((target_pre * cols ) + j )) (lcur) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) ) )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot_pre * cols ) + j ))
  **  ((( &( "idx" ) )) # Int  |-> ((target_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((aug_pre + (((target_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ ((aug_pre + (((target_pre * (n_pre + 1 ) ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ”
) \/
(
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (cols <= INT_MAX)) (PreH3 : (target_pre <= INT_MAX)) (PreH4 : (pivot_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (cols >= INT_MIN)) (PreH8 : (target_pre >= INT_MIN)) (PreH9 : (pivot_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((target_pre * cols ) + j ) >= INT_MIN)) (PreH12 : (((pivot_pre * cols ) + j ) >= INT_MIN)) (PreH13 : (j < cols)) (PreH14 : (aug_pre <> 0)) (PreH15 : (p_pre <> 0)) (PreH16 : (factor_pre <> 0)) (PreH17 : (prod <> 0)) (PreH18 : (v <> 0)) (PreH19 : (cols = (n_pre + 1 ))) (PreH20 : (cols = (n_pre + 1 ))) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 256)) (PreH23 : (zp_low_level_spec > 0)) (PreH24 : (0 <= (n_pre * cols ))) (PreH25 : ((n_pre * cols ) <= INT_MAX)) (PreH26 : (0 <= pivot_pre)) (PreH27 : (pivot_pre < n_pre)) (PreH28 : (0 <= target_pre)) (PreH29 : (target_pre < n_pre)) (PreH30 : (pivot_pre <> target_pre)) (PreH31 : (0 <= zfactor_low_level_spec)) (PreH32 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH33 : (0 <= j)) (PreH34 : (j <= cols)) (PreH35 : (0 <= ((target_pre * cols ) + j ))) (PreH36 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH37 : (0 <= ((pivot_pre * cols ) + j ))) (PreH38 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH39 : (INT_MIN <= (target_pre * cols ))) (PreH40 : ((target_pre * cols ) <= INT_MAX)) (PreH41 : (INT_MIN <= (pivot_pre * cols ))) (PreH42 : ((pivot_pre * cols ) <= INT_MAX)) (PreH43 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH44 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH45 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH46 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH47 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH48 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH49 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z v ((Znth (((target_pre * cols ) + j )) (lcur) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) ) )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot_pre * cols ) + j ))
  **  ((( &( "idx" ) )) # Int  |-> ((target_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((aug_pre + (((target_pre * (n_pre + 1 ) ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ” 
  &&  “ ((aug_pre + (((target_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ”
).

Definition row_elim_mod_gmp_partial_solve_wit_8_pure_split_goal_1 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (cols <= INT_MAX)) (PreH3 : (target_pre <= INT_MAX)) (PreH4 : (pivot_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (cols >= INT_MIN)) (PreH8 : (target_pre >= INT_MIN)) (PreH9 : (pivot_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((target_pre * cols ) + j ) >= INT_MIN)) (PreH12 : (((pivot_pre * cols ) + j ) >= INT_MIN)) (PreH13 : (j < cols)) (PreH14 : (aug_pre <> 0)) (PreH15 : (p_pre <> 0)) (PreH16 : (factor_pre <> 0)) (PreH17 : (prod <> 0)) (PreH18 : (v <> 0)) (PreH19 : (cols = (n_pre + 1 ))) (PreH20 : (cols = (n_pre + 1 ))) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 256)) (PreH23 : (zp_low_level_spec > 0)) (PreH24 : (0 <= (n_pre * cols ))) (PreH25 : ((n_pre * cols ) <= INT_MAX)) (PreH26 : (0 <= pivot_pre)) (PreH27 : (pivot_pre < n_pre)) (PreH28 : (0 <= target_pre)) (PreH29 : (target_pre < n_pre)) (PreH30 : (pivot_pre <> target_pre)) (PreH31 : (0 <= zfactor_low_level_spec)) (PreH32 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH33 : (0 <= j)) (PreH34 : (j <= cols)) (PreH35 : (0 <= ((target_pre * cols ) + j ))) (PreH36 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH37 : (0 <= ((pivot_pre * cols ) + j ))) (PreH38 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH39 : (INT_MIN <= (target_pre * cols ))) (PreH40 : ((target_pre * cols ) <= INT_MAX)) (PreH41 : (INT_MIN <= (pivot_pre * cols ))) (PreH42 : ((pivot_pre * cols ) <= INT_MAX)) (PreH43 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH44 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH45 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH46 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH47 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH48 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH49 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z v ((Znth (((target_pre * cols ) + j )) (lcur) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) ) )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot_pre * cols ) + j ))
  **  ((( &( "idx" ) )) # Int  |-> ((target_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((aug_pre + (((target_pre * (n_pre + 1 ) ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ”
.

Definition row_elim_mod_gmp_partial_solve_wit_8_pure_split_goal_2 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (cols <= INT_MAX)) (PreH3 : (target_pre <= INT_MAX)) (PreH4 : (pivot_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (cols >= INT_MIN)) (PreH8 : (target_pre >= INT_MIN)) (PreH9 : (pivot_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((target_pre * cols ) + j ) >= INT_MIN)) (PreH12 : (((pivot_pre * cols ) + j ) >= INT_MIN)) (PreH13 : (j < cols)) (PreH14 : (aug_pre <> 0)) (PreH15 : (p_pre <> 0)) (PreH16 : (factor_pre <> 0)) (PreH17 : (prod <> 0)) (PreH18 : (v <> 0)) (PreH19 : (cols = (n_pre + 1 ))) (PreH20 : (cols = (n_pre + 1 ))) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 256)) (PreH23 : (zp_low_level_spec > 0)) (PreH24 : (0 <= (n_pre * cols ))) (PreH25 : ((n_pre * cols ) <= INT_MAX)) (PreH26 : (0 <= pivot_pre)) (PreH27 : (pivot_pre < n_pre)) (PreH28 : (0 <= target_pre)) (PreH29 : (target_pre < n_pre)) (PreH30 : (pivot_pre <> target_pre)) (PreH31 : (0 <= zfactor_low_level_spec)) (PreH32 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH33 : (0 <= j)) (PreH34 : (j <= cols)) (PreH35 : (0 <= ((target_pre * cols ) + j ))) (PreH36 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH37 : (0 <= ((pivot_pre * cols ) + j ))) (PreH38 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH39 : (INT_MIN <= (target_pre * cols ))) (PreH40 : ((target_pre * cols ) <= INT_MAX)) (PreH41 : (INT_MIN <= (pivot_pre * cols ))) (PreH42 : ((pivot_pre * cols ) <= INT_MAX)) (PreH43 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH44 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH45 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH46 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH47 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH48 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH49 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z v ((Znth (((target_pre * cols ) + j )) (lcur) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) ) )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  ((( &( "pidx" ) )) # Int  |-> ((pivot_pre * cols ) + j ))
  **  ((( &( "idx" ) )) # Int  |-> ((target_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "factor" ) )) # Ptr  |-> factor_pre)
  **  ((( &( "prod" ) )) # Ptr  |-> prod)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((aug_pre + (((target_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ”
.

Definition row_elim_mod_gmp_partial_solve_wit_8_aux := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z v ((Znth (((target_pre * cols ) + j )) (lcur) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) ) )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((aug_pre + (((target_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ ((aug_pre + (((target_pre * (n_pre + 1 ) ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ” 
  &&  “ (j < cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z (aug_pre + (((target_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) (Znth (((target_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z v ((Znth (((target_pre * cols ) + j )) (lcur) (0)) - (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_missing_i aug_pre ((target_pre * cols ) + j ) 0 (n_pre * cols ) lcur )
  **  (store_Z prod (zfactor_low_level_spec * (Znth (((pivot_pre * cols ) + j )) (lcur) (0)) ) )
  **  (store_Z factor_pre zfactor_low_level_spec )
.

Definition row_elim_mod_gmp_partial_solve_wit_8 := row_elim_mod_gmp_partial_solve_wit_8_pure -> row_elim_mod_gmp_partial_solve_wit_8_aux.

Definition row_elim_mod_gmp_partial_solve_wit_9 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (0 <= ((pivot_pre * cols ) + j ))) (PreH25 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_10 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (j >= cols)) (PreH25 : (INT_MIN <= (target_pre * cols ))) (PreH26 : ((target_pre * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= (pivot_pre * cols ))) (PreH28 : ((pivot_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH30 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH32 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_11 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_12 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (zv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (j >= cols)) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z v zv )
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_13 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (0 <= ((pivot_pre * cols ) + j ))) (PreH25 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_14 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (j >= cols)) (PreH25 : (INT_MIN <= (target_pre * cols ))) (PreH26 : ((target_pre * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= (pivot_pre * cols ))) (PreH28 : ((pivot_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH30 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH32 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_15 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_16 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (j >= cols)) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_17 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (0 <= ((pivot_pre * cols ) + j ))) (PreH25 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_18 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (j >= cols)) (PreH25 : (INT_MIN <= (target_pre * cols ))) (PreH26 : ((target_pre * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= (pivot_pre * cols ))) (PreH28 : ((pivot_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH30 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH32 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_19 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_20 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (zprod: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (j >= cols)) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  (store_Z prod zprod )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_21 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (0 <= ((pivot_pre * cols ) + j ))) (PreH25 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_22 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (j >= cols)) (PreH24 : (j >= cols)) (PreH25 : (INT_MIN <= (target_pre * cols ))) (PreH26 : ((target_pre * cols ) <= INT_MAX)) (PreH27 : (INT_MIN <= (pivot_pre * cols ))) (PreH28 : ((pivot_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH30 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH32 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH34 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_23 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (0 <= ((pivot_pre * cols ) + j ))) (PreH26 : (((pivot_pre * cols ) + j ) < (n_pre * cols ))) (PreH27 : (INT_MIN <= (target_pre * cols ))) (PreH28 : ((target_pre * cols ) <= INT_MAX)) (PreH29 : (INT_MIN <= (pivot_pre * cols ))) (PreH30 : ((pivot_pre * cols ) <= INT_MAX)) (PreH31 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH32 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH33 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH34 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH35 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH37 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_elim_mod_gmp_partial_solve_wit_24 := 
forall (factor_pre: Z) (target_pre: Z) (pivot_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zfactor_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (prod: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (factor_pre <> 0)) (PreH5 : (prod <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= pivot_pre)) (PreH15 : (pivot_pre < n_pre)) (PreH16 : (0 <= target_pre)) (PreH17 : (target_pre < n_pre)) (PreH18 : (pivot_pre <> target_pre)) (PreH19 : (0 <= zfactor_low_level_spec)) (PreH20 : (zfactor_low_level_spec < zp_low_level_spec)) (PreH21 : (0 <= j)) (PreH22 : (j <= cols)) (PreH23 : (0 <= ((target_pre * cols ) + j ))) (PreH24 : (((target_pre * cols ) + j ) < (n_pre * cols ))) (PreH25 : (j >= cols)) (PreH26 : (INT_MIN <= (target_pre * cols ))) (PreH27 : ((target_pre * cols ) <= INT_MAX)) (PreH28 : (INT_MIN <= (pivot_pre * cols ))) (PreH29 : ((pivot_pre * cols ) <= INT_MAX)) (PreH30 : (INT_MIN <= ((target_pre * cols ) + j ))) (PreH31 : (((target_pre * cols ) + j ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((pivot_pre * cols ) + j ))) (PreH33 : (((pivot_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j )) ,
  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (factor_pre <> 0) ” 
  &&  “ (prod <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= pivot_pre) ” 
  &&  “ (pivot_pre < n_pre) ” 
  &&  “ (0 <= target_pre) ” 
  &&  “ (target_pre < n_pre) ” 
  &&  “ (pivot_pre <> target_pre) ” 
  &&  “ (0 <= zfactor_low_level_spec) ” 
  &&  “ (zfactor_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (target_pre * cols )) ” 
  &&  “ ((target_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (pivot_pre * cols )) ” 
  &&  “ ((pivot_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((target_pre * cols ) + j )) ” 
  &&  “ (((target_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((pivot_pre * cols ) + j )) ” 
  &&  “ (((pivot_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_elim_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec pivot_pre target_pre zfactor_low_level_spec j ) ”
  &&  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((prod)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z factor_pre zfactor_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_row_elim_mod_gmp_safety_wit_1 : row_elim_mod_gmp_safety_wit_1.
Axiom proof_of_row_elim_mod_gmp_safety_wit_2 : row_elim_mod_gmp_safety_wit_2.
Axiom proof_of_row_elim_mod_gmp_safety_wit_3 : row_elim_mod_gmp_safety_wit_3.
Axiom proof_of_row_elim_mod_gmp_safety_wit_4 : row_elim_mod_gmp_safety_wit_4.
Axiom proof_of_row_elim_mod_gmp_safety_wit_5 : row_elim_mod_gmp_safety_wit_5.
Axiom proof_of_row_elim_mod_gmp_safety_wit_6 : row_elim_mod_gmp_safety_wit_6.
Axiom proof_of_row_elim_mod_gmp_safety_wit_7 : row_elim_mod_gmp_safety_wit_7.
Axiom proof_of_row_elim_mod_gmp_safety_wit_8 : row_elim_mod_gmp_safety_wit_8.
Axiom proof_of_row_elim_mod_gmp_safety_wit_9 : row_elim_mod_gmp_safety_wit_9.
Axiom proof_of_row_elim_mod_gmp_safety_wit_10 : row_elim_mod_gmp_safety_wit_10.
Axiom proof_of_row_elim_mod_gmp_safety_wit_11 : row_elim_mod_gmp_safety_wit_11.
Axiom proof_of_row_elim_mod_gmp_safety_wit_12 : row_elim_mod_gmp_safety_wit_12.
Axiom proof_of_row_elim_mod_gmp_entail_wit_1 : row_elim_mod_gmp_entail_wit_1.
Axiom proof_of_row_elim_mod_gmp_entail_wit_2 : row_elim_mod_gmp_entail_wit_2.
Axiom proof_of_row_elim_mod_gmp_return_wit_1 : row_elim_mod_gmp_return_wit_1.
Axiom proof_of_row_elim_mod_gmp_return_wit_2 : row_elim_mod_gmp_return_wit_2.
Axiom proof_of_row_elim_mod_gmp_return_wit_3 : row_elim_mod_gmp_return_wit_3.
Axiom proof_of_row_elim_mod_gmp_return_wit_4 : row_elim_mod_gmp_return_wit_4.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_1 : row_elim_mod_gmp_partial_solve_wit_1.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_2 : row_elim_mod_gmp_partial_solve_wit_2.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_3 : row_elim_mod_gmp_partial_solve_wit_3.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_4 : row_elim_mod_gmp_partial_solve_wit_4.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_5 : row_elim_mod_gmp_partial_solve_wit_5.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_6 : row_elim_mod_gmp_partial_solve_wit_6.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_7_pure : row_elim_mod_gmp_partial_solve_wit_7_pure.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_7 : row_elim_mod_gmp_partial_solve_wit_7.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_8_pure : row_elim_mod_gmp_partial_solve_wit_8_pure.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_8 : row_elim_mod_gmp_partial_solve_wit_8.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_9 : row_elim_mod_gmp_partial_solve_wit_9.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_10 : row_elim_mod_gmp_partial_solve_wit_10.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_11 : row_elim_mod_gmp_partial_solve_wit_11.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_12 : row_elim_mod_gmp_partial_solve_wit_12.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_13 : row_elim_mod_gmp_partial_solve_wit_13.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_14 : row_elim_mod_gmp_partial_solve_wit_14.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_15 : row_elim_mod_gmp_partial_solve_wit_15.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_16 : row_elim_mod_gmp_partial_solve_wit_16.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_17 : row_elim_mod_gmp_partial_solve_wit_17.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_18 : row_elim_mod_gmp_partial_solve_wit_18.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_19 : row_elim_mod_gmp_partial_solve_wit_19.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_20 : row_elim_mod_gmp_partial_solve_wit_20.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_21 : row_elim_mod_gmp_partial_solve_wit_21.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_22 : row_elim_mod_gmp_partial_solve_wit_22.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_23 : row_elim_mod_gmp_partial_solve_wit_23.
Axiom proof_of_row_elim_mod_gmp_partial_solve_wit_24 : row_elim_mod_gmp_partial_solve_wit_24.

End VC_Correct.
