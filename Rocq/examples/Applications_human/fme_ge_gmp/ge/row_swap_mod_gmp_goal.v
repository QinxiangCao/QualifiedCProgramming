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

(*----- Function row_swap_mod_gmp -----*)

Definition row_swap_mod_gmp_safety_wit_1 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 256)) (PreH4 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH5 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH6 : (0 <= r1_pre)) (PreH7 : (r1_pre < n_pre)) (PreH8 : (0 <= r2_pre)) (PreH9 : (r2_pre < n_pre)) (PreH10 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition row_swap_mod_gmp_safety_wit_2 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 256)) (PreH4 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH5 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH6 : (0 <= r1_pre)) (PreH7 : (r1_pre < n_pre)) (PreH8 : (0 <= r2_pre)) (PreH9 : (r2_pre < n_pre)) (PreH10 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition row_swap_mod_gmp_safety_wit_3 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 256)) (PreH4 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH5 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH6 : (0 <= r1_pre)) (PreH7 : (r1_pre < n_pre)) (PreH8 : (0 <= r2_pre)) (PreH9 : (r2_pre < n_pre)) (PreH10 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cols" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition row_swap_mod_gmp_safety_wit_4 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition row_swap_mod_gmp_safety_wit_5 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (j >= cols)) (PreH19 : (INT_MIN <= (r1_pre * cols ))) (PreH20 : ((r1_pre * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= (r2_pre * cols ))) (PreH22 : ((r2_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH24 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH26 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition row_swap_mod_gmp_safety_wit_6 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (0 <= ((r2_pre * cols ) + j ))) (PreH19 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition row_swap_mod_gmp_safety_wit_7 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((( &( "idx1" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((r1_pre * cols ) + j )) ”
.

Definition row_swap_mod_gmp_safety_wit_8 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((( &( "idx1" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r1_pre * cols )) ”
.

Definition row_swap_mod_gmp_safety_wit_9 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((( &( "idx2" ) )) # Int  |->_)
  **  ((( &( "idx1" ) )) # Int  |-> ((r1_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((r2_pre * cols ) + j )) ”
.

Definition row_swap_mod_gmp_safety_wit_10 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((( &( "idx2" ) )) # Int  |->_)
  **  ((( &( "idx1" ) )) # Int  |-> ((r1_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r2_pre * cols )) ”
.

Definition row_swap_mod_gmp_safety_wit_11 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (lmid: (@list Z)) (tmp1: Z) (tmp2: Z) (cols: Z) (j: Z) (idx1: Z) (idx2: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (tmp1 <> 0)) (PreH3 : (tmp2 <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (0 <= (n_pre * cols ))) (PreH9 : ((n_pre * cols ) <= INT_MAX)) (PreH10 : (0 <= r1_pre)) (PreH11 : (r1_pre < n_pre)) (PreH12 : (0 <= r2_pre)) (PreH13 : (r2_pre < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < cols)) (PreH16 : (idx1 = ((r1_pre * cols ) + j ))) (PreH17 : (idx2 = ((r2_pre * cols ) + j ))) (PreH18 : (0 <= idx1)) (PreH19 : (idx1 < (n_pre * cols ))) (PreH20 : (0 <= idx2)) (PreH21 : (idx2 < (n_pre * cols ))) (PreH22 : (INT_MIN <= (r1_pre * cols ))) (PreH23 : ((r1_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= (r2_pre * cols ))) (PreH25 : ((r2_pre * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= idx1)) (PreH27 : (idx1 <= INT_MAX)) (PreH28 : (INT_MIN <= idx2)) (PreH29 : (idx2 <= INT_MAX)) (PreH30 : (lmid = (replace_Znth (idx1) ((Znth (idx2) (lcur) (0))) (lcur)))) (PreH31 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH32 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx2) ((Znth (((r1_pre * cols ) + j )) (lcur) (0))) (lmid)) )
  **  (store_Z tmp1 (Znth (((r1_pre * cols ) + j )) (lcur) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx1" ) )) # Int  |-> idx1)
  **  ((( &( "idx2" ) )) # Int  |-> idx2)
  **  (store_Z tmp2 (Znth (idx2) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition row_swap_mod_gmp_safety_wit_12 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (lmid: (@list Z)) (tmp1: Z) (tmp2: Z) (cols: Z) (j: Z) (idx1: Z) (idx2: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (tmp1 <> 0)) (PreH3 : (tmp2 <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (0 <= (n_pre * cols ))) (PreH9 : ((n_pre * cols ) <= INT_MAX)) (PreH10 : (0 <= r1_pre)) (PreH11 : (r1_pre < n_pre)) (PreH12 : (0 <= r2_pre)) (PreH13 : (r2_pre < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < cols)) (PreH16 : (idx1 = ((r1_pre * cols ) + j ))) (PreH17 : (idx2 = ((r2_pre * cols ) + j ))) (PreH18 : (0 <= idx1)) (PreH19 : (idx1 < (n_pre * cols ))) (PreH20 : (0 <= idx2)) (PreH21 : (idx2 < (n_pre * cols ))) (PreH22 : (INT_MIN <= (r1_pre * cols ))) (PreH23 : ((r1_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= (r2_pre * cols ))) (PreH25 : ((r2_pre * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= idx1)) (PreH27 : (idx1 <= INT_MAX)) (PreH28 : (INT_MIN <= idx2)) (PreH29 : (idx2 <= INT_MAX)) (PreH30 : (lmid = (replace_Znth (idx1) ((Znth (idx2) (lcur) (0))) (lcur)))) (PreH31 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH32 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx2) ((Znth (((r1_pre * cols ) + j )) (lcur) (0))) (lmid)) )
  **  (store_Z tmp1 (Znth (((r1_pre * cols ) + j )) (lcur) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx1" ) )) # Int  |-> idx1)
  **  ((( &( "idx2" ) )) # Int  |-> idx2)
  **  (store_Z tmp2 (Znth (idx2) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition row_swap_mod_gmp_entail_wit_1 := 
(
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH8 : (0 <= r1_pre)) (PreH9 : (r1_pre < n_pre)) (PreH10 : (0 <= r2_pre)) (PreH11 : (r2_pre < n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  EX (ztmp2: Z)  (ztmp1: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((r1_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((r1_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((r2_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((r2_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) )) ” 
  &&  “ (INT_MIN <= (r1_pre * (n_pre + 1 ) )) ” 
  &&  “ ((r1_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * (n_pre + 1 ) )) ” 
  &&  “ ((r2_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((r1_pre * (n_pre + 1 ) ) + 0 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((r2_pre * (n_pre + 1 ) ) + 0 ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre (n_pre + 1 ) M_low_level_spec r1_pre r2_pre 0 ) ”
  &&  (store_Z retval ztmp1 )
  **  (store_Z retval_2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
) \/
(
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (n_pre: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH8 : (0 <= r1_pre)) (PreH9 : (r1_pre < n_pre)) (PreH10 : (0 <= r2_pre)) (PreH11 : (r2_pre < n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  TT && emp 
|--
  “ (row_swap_prefix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec r1_pre r2_pre 0 ) ” 
  &&  “ (((r2_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) )) ” 
  &&  “ (((r1_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) )) ”
  &&  emp
).

Definition row_swap_mod_gmp_entail_wit_1_split_goal_1 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (n_pre: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH8 : (0 <= r1_pre)) (PreH9 : (r1_pre < n_pre)) (PreH10 : (0 <= r2_pre)) (PreH11 : (r2_pre < n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (row_swap_prefix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec r1_pre r2_pre 0 )
.

Definition row_swap_mod_gmp_entail_wit_1_split_goal_2 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (n_pre: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH8 : (0 <= r1_pre)) (PreH9 : (r1_pre < n_pre)) (PreH10 : (0 <= r2_pre)) (PreH11 : (r2_pre < n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (((r2_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) ))
.

Definition row_swap_mod_gmp_entail_wit_1_split_goal_3 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (n_pre: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH8 : (0 <= r1_pre)) (PreH9 : (r1_pre < n_pre)) (PreH10 : (0 <= r2_pre)) (PreH11 : (r2_pre < n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (((r1_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) ))
.

Definition row_swap_mod_gmp_entail_wit_2 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur_2: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur_2 n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (((r1_pre * cols ) + j )) ((Znth (((r2_pre * (n_pre + 1 ) ) + j )) (lcur_2) (0))) (lcur_2)) )
  **  (store_Z tmp2 (Znth (((r2_pre * (n_pre + 1 ) ) + j )) (lcur_2) (0)) )
  **  (store_Z tmp1 (Znth (((r1_pre * cols ) + j )) (lcur_2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
|--
  EX (lcur: (@list Z))  (lmid: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < cols) ” 
  &&  “ (((r1_pre * cols ) + j ) = ((r1_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) = ((r2_pre * cols ) + j )) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (lmid = (replace_Znth (((r1_pre * cols ) + j )) ((Znth (((r2_pre * cols ) + j )) (lcur) (0))) (lcur))) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp1 (Znth (((r1_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z tmp2 (Znth (((r2_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lmid )
.

Definition row_swap_mod_gmp_entail_wit_3 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur_2: (@list Z)) (lmid: (@list Z)) (tmp1: Z) (tmp2: Z) (cols: Z) (j: Z) (idx1: Z) (idx2: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (tmp1 <> 0)) (PreH3 : (tmp2 <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (0 <= (n_pre * cols ))) (PreH9 : ((n_pre * cols ) <= INT_MAX)) (PreH10 : (0 <= r1_pre)) (PreH11 : (r1_pre < n_pre)) (PreH12 : (0 <= r2_pre)) (PreH13 : (r2_pre < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < cols)) (PreH16 : (idx1 = ((r1_pre * cols ) + j ))) (PreH17 : (idx2 = ((r2_pre * cols ) + j ))) (PreH18 : (0 <= idx1)) (PreH19 : (idx1 < (n_pre * cols ))) (PreH20 : (0 <= idx2)) (PreH21 : (idx2 < (n_pre * cols ))) (PreH22 : (INT_MIN <= (r1_pre * cols ))) (PreH23 : ((r1_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= (r2_pre * cols ))) (PreH25 : ((r2_pre * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= idx1)) (PreH27 : (idx1 <= INT_MAX)) (PreH28 : (INT_MIN <= idx2)) (PreH29 : (idx2 <= INT_MAX)) (PreH30 : (lmid = (replace_Znth (idx1) ((Znth (idx2) (lcur_2) (0))) (lcur_2)))) (PreH31 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH32 : (row_swap_prefix lcur_2 n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx2) ((Znth (((r1_pre * cols ) + j )) (lcur_2) (0))) (lmid)) )
  **  (store_Z tmp1 (Znth (((r1_pre * cols ) + j )) (lcur_2) (0)) )
  **  (store_Z tmp2 (Znth (idx2) (lcur_2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
|--
  (EX (ztmp2: Z)  (ztmp1: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r1_pre * cols ) + (j + 1 ) ) < (n_pre * cols )) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r1_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r2_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre (j + 1 ) ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (EX (ztmp2: Z)  (ztmp1: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r1_pre * cols ) + (j + 1 ) ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((r2_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r2_pre * cols ) + (j + 1 ) ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r1_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r2_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre (j + 1 ) ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (EX (ztmp2: Z)  (ztmp1: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r1_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r2_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre (j + 1 ) ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (EX (ztmp2: Z)  (ztmp1: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (0 <= ((r2_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r2_pre * cols ) + (j + 1 ) ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r1_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((r2_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre (j + 1 ) ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
.

Definition row_swap_mod_gmp_return_wit_1 := 
(
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M_low_level_spec) (r1_pre) (r2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M_low_level_spec) (r1_pre) (r2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition row_swap_mod_gmp_return_wit_2 := 
(
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M_low_level_spec) (r1_pre) (r2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M_low_level_spec) (r1_pre) (r2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition row_swap_mod_gmp_return_wit_3 := 
(
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (j >= cols)) (PreH19 : (INT_MIN <= (r1_pre * cols ))) (PreH20 : ((r1_pre * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= (r2_pre * cols ))) (PreH22 : ((r2_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH24 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH26 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M_low_level_spec) (r1_pre) (r2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (j >= cols)) (PreH19 : (INT_MIN <= (r1_pre * cols ))) (PreH20 : ((r1_pre * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= (r2_pre * cols ))) (PreH22 : ((r2_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH24 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH26 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M_low_level_spec) (r1_pre) (r2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition row_swap_mod_gmp_return_wit_4 := 
(
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (0 <= ((r2_pre * cols ) + j ))) (PreH19 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M_low_level_spec) (r1_pre) (r2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (0 <= ((r2_pre * cols ) + j ))) (PreH19 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_swap (M_low_level_spec) (r1_pre) (r2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition row_swap_mod_gmp_partial_solve_wit_1 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 256)) (PreH4 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH5 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH6 : (0 <= r1_pre)) (PreH7 : (r1_pre < n_pre)) (PreH8 : (0 <= r2_pre)) (PreH9 : (r2_pre < n_pre)) (PreH10 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition row_swap_mod_gmp_partial_solve_wit_2 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 256)) (PreH5 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH6 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH7 : (0 <= r1_pre)) (PreH8 : (r1_pre < n_pre)) (PreH9 : (0 <= r2_pre)) (PreH10 : (r2_pre < n_pre)) (PreH11 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition row_swap_mod_gmp_partial_solve_wit_3 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 256)) (PreH5 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH6 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH7 : (0 <= r1_pre)) (PreH8 : (r1_pre < n_pre)) (PreH9 : (0 <= r2_pre)) (PreH10 : (r2_pre < n_pre)) (PreH11 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition row_swap_mod_gmp_partial_solve_wit_4 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH8 : (0 <= r1_pre)) (PreH9 : (r1_pre < n_pre)) (PreH10 : (0 <= r2_pre)) (PreH11 : (r2_pre < n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition row_swap_mod_gmp_partial_solve_wit_5 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j < cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z (aug_pre + (((r1_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) (Znth (((r1_pre * cols ) + j )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre ((r1_pre * cols ) + j ) 0 (n_pre * cols ) lcur )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition row_swap_mod_gmp_partial_solve_wit_6 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z tmp1 (Znth (((r1_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (j < cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp2 ztmp2 )
  **  (store_Z (aug_pre + (((r2_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) (Znth (((r2_pre * cols ) + j )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre ((r2_pre * cols ) + j ) 0 (n_pre * cols ) lcur )
  **  (store_Z tmp1 (Znth (((r1_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition row_swap_mod_gmp_partial_solve_wit_7 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z tmp2 (Znth (((r2_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z tmp1 (Znth (((r1_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (j < cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z (aug_pre + (((r1_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) (Znth (((r1_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z tmp2 (Znth (((r2_pre * (n_pre + 1 ) ) + j )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre ((r1_pre * cols ) + j ) 0 (n_pre * cols ) lcur )
  **  (store_Z tmp1 (Znth (((r1_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition row_swap_mod_gmp_partial_solve_wit_8 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (lmid: (@list Z)) (tmp1: Z) (tmp2: Z) (cols: Z) (j: Z) (idx1: Z) (idx2: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (tmp1 <> 0)) (PreH3 : (tmp2 <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (0 <= (n_pre * cols ))) (PreH9 : ((n_pre * cols ) <= INT_MAX)) (PreH10 : (0 <= r1_pre)) (PreH11 : (r1_pre < n_pre)) (PreH12 : (0 <= r2_pre)) (PreH13 : (r2_pre < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j < cols)) (PreH16 : (idx1 = ((r1_pre * cols ) + j ))) (PreH17 : (idx2 = ((r2_pre * cols ) + j ))) (PreH18 : (0 <= idx1)) (PreH19 : (idx1 < (n_pre * cols ))) (PreH20 : (0 <= idx2)) (PreH21 : (idx2 < (n_pre * cols ))) (PreH22 : (INT_MIN <= (r1_pre * cols ))) (PreH23 : ((r1_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= (r2_pre * cols ))) (PreH25 : ((r2_pre * cols ) <= INT_MAX)) (PreH26 : (INT_MIN <= idx1)) (PreH27 : (idx1 <= INT_MAX)) (PreH28 : (INT_MIN <= idx2)) (PreH29 : (idx2 <= INT_MAX)) (PreH30 : (lmid = (replace_Znth (idx1) ((Znth (idx2) (lcur) (0))) (lcur)))) (PreH31 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH32 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z tmp1 (Znth (idx1) (lcur) (0)) )
  **  (store_Z tmp2 (Znth (idx2) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lmid )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < cols) ” 
  &&  “ (idx1 = ((r1_pre * cols ) + j )) ” 
  &&  “ (idx2 = ((r2_pre * cols ) + j )) ” 
  &&  “ (0 <= idx1) ” 
  &&  “ (idx1 < (n_pre * cols )) ” 
  &&  “ (0 <= idx2) ” 
  &&  “ (idx2 < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= idx1) ” 
  &&  “ (idx1 <= INT_MAX) ” 
  &&  “ (INT_MIN <= idx2) ” 
  &&  “ (idx2 <= INT_MAX) ” 
  &&  “ (lmid = (replace_Znth (idx1) ((Znth (idx2) (lcur) (0))) (lcur))) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z (aug_pre + (idx2 * sizeof( "__mpz_struct" ))) (Znth (idx2) (lmid) (0)) )
  **  (store_Z tmp1 (Znth (((r1_pre * cols ) + j )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre idx2 0 (n_pre * cols ) lmid )
  **  (store_Z tmp2 (Znth (idx2) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition row_swap_mod_gmp_partial_solve_wit_9 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp2 ztmp2 )
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_10 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp2 ztmp2 )
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_11 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (j >= cols)) (PreH19 : (INT_MIN <= (r1_pre * cols ))) (PreH20 : ((r1_pre * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= (r2_pre * cols ))) (PreH22 : ((r2_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH24 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH26 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp2 ztmp2 )
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_12 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (0 <= ((r2_pre * cols ) + j ))) (PreH19 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp2 ztmp2 )
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_13 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_14 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_15 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (j >= cols)) (PreH19 : (INT_MIN <= (r1_pre * cols ))) (PreH20 : ((r1_pre * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= (r2_pre * cols ))) (PreH22 : ((r2_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH24 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH26 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_16 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (0 <= ((r2_pre * cols ) + j ))) (PreH19 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_17 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_18 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_19 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (j >= cols)) (PreH19 : (INT_MIN <= (r1_pre * cols ))) (PreH20 : ((r1_pre * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= (r2_pre * cols ))) (PreH22 : ((r2_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH24 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH26 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_20 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (ztmp1: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (0 <= ((r2_pre * cols ) + j ))) (PreH19 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_21 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_22 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (0 <= ((r1_pre * cols ) + j ))) (PreH18 : (((r1_pre * cols ) + j ) < (n_pre * cols ))) (PreH19 : (0 <= ((r2_pre * cols ) + j ))) (PreH20 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (r1_pre * cols ))) (PreH22 : ((r1_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= (r2_pre * cols ))) (PreH24 : ((r2_pre * cols ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH26 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH28 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_23 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (j >= cols)) (PreH19 : (INT_MIN <= (r1_pre * cols ))) (PreH20 : ((r1_pre * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= (r2_pre * cols ))) (PreH22 : ((r2_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH24 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH26 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_swap_mod_gmp_partial_solve_wit_24 := 
forall (r2_pre: Z) (r1_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= r1_pre)) (PreH12 : (r1_pre < n_pre)) (PreH13 : (0 <= r2_pre)) (PreH14 : (r2_pre < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= cols)) (PreH17 : (j >= cols)) (PreH18 : (0 <= ((r2_pre * cols ) + j ))) (PreH19 : (((r2_pre * cols ) + j ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (r1_pre * cols ))) (PreH21 : ((r1_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= (r2_pre * cols ))) (PreH23 : ((r2_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((r1_pre * cols ) + j ))) (PreH25 : (((r1_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (INT_MIN <= ((r2_pre * cols ) + j ))) (PreH27 : (((r2_pre * cols ) + j ) <= INT_MAX)) (PreH28 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j )) ,
  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (tmp1 <> 0) ” 
  &&  “ (tmp2 <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre < n_pre) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (0 <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (r1_pre * cols )) ” 
  &&  “ ((r1_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (r2_pre * cols )) ” 
  &&  “ ((r2_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r1_pre * cols ) + j )) ” 
  &&  “ (((r1_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((r2_pre * cols ) + j )) ” 
  &&  “ (((r2_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_swap_prefix lcur n_pre cols M_low_level_spec r1_pre r2_pre j ) ”
  &&  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_row_swap_mod_gmp_safety_wit_1 : row_swap_mod_gmp_safety_wit_1.
Axiom proof_of_row_swap_mod_gmp_safety_wit_2 : row_swap_mod_gmp_safety_wit_2.
Axiom proof_of_row_swap_mod_gmp_safety_wit_3 : row_swap_mod_gmp_safety_wit_3.
Axiom proof_of_row_swap_mod_gmp_safety_wit_4 : row_swap_mod_gmp_safety_wit_4.
Axiom proof_of_row_swap_mod_gmp_safety_wit_5 : row_swap_mod_gmp_safety_wit_5.
Axiom proof_of_row_swap_mod_gmp_safety_wit_6 : row_swap_mod_gmp_safety_wit_6.
Axiom proof_of_row_swap_mod_gmp_safety_wit_7 : row_swap_mod_gmp_safety_wit_7.
Axiom proof_of_row_swap_mod_gmp_safety_wit_8 : row_swap_mod_gmp_safety_wit_8.
Axiom proof_of_row_swap_mod_gmp_safety_wit_9 : row_swap_mod_gmp_safety_wit_9.
Axiom proof_of_row_swap_mod_gmp_safety_wit_10 : row_swap_mod_gmp_safety_wit_10.
Axiom proof_of_row_swap_mod_gmp_safety_wit_11 : row_swap_mod_gmp_safety_wit_11.
Axiom proof_of_row_swap_mod_gmp_safety_wit_12 : row_swap_mod_gmp_safety_wit_12.
Axiom proof_of_row_swap_mod_gmp_entail_wit_1 : row_swap_mod_gmp_entail_wit_1.
Axiom proof_of_row_swap_mod_gmp_entail_wit_2 : row_swap_mod_gmp_entail_wit_2.
Axiom proof_of_row_swap_mod_gmp_entail_wit_3 : row_swap_mod_gmp_entail_wit_3.
Axiom proof_of_row_swap_mod_gmp_return_wit_1 : row_swap_mod_gmp_return_wit_1.
Axiom proof_of_row_swap_mod_gmp_return_wit_2 : row_swap_mod_gmp_return_wit_2.
Axiom proof_of_row_swap_mod_gmp_return_wit_3 : row_swap_mod_gmp_return_wit_3.
Axiom proof_of_row_swap_mod_gmp_return_wit_4 : row_swap_mod_gmp_return_wit_4.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_1 : row_swap_mod_gmp_partial_solve_wit_1.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_2 : row_swap_mod_gmp_partial_solve_wit_2.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_3 : row_swap_mod_gmp_partial_solve_wit_3.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_4 : row_swap_mod_gmp_partial_solve_wit_4.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_5 : row_swap_mod_gmp_partial_solve_wit_5.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_6 : row_swap_mod_gmp_partial_solve_wit_6.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_7 : row_swap_mod_gmp_partial_solve_wit_7.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_8 : row_swap_mod_gmp_partial_solve_wit_8.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_9 : row_swap_mod_gmp_partial_solve_wit_9.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_10 : row_swap_mod_gmp_partial_solve_wit_10.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_11 : row_swap_mod_gmp_partial_solve_wit_11.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_12 : row_swap_mod_gmp_partial_solve_wit_12.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_13 : row_swap_mod_gmp_partial_solve_wit_13.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_14 : row_swap_mod_gmp_partial_solve_wit_14.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_15 : row_swap_mod_gmp_partial_solve_wit_15.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_16 : row_swap_mod_gmp_partial_solve_wit_16.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_17 : row_swap_mod_gmp_partial_solve_wit_17.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_18 : row_swap_mod_gmp_partial_solve_wit_18.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_19 : row_swap_mod_gmp_partial_solve_wit_19.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_20 : row_swap_mod_gmp_partial_solve_wit_20.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_21 : row_swap_mod_gmp_partial_solve_wit_21.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_22 : row_swap_mod_gmp_partial_solve_wit_22.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_23 : row_swap_mod_gmp_partial_solve_wit_23.
Axiom proof_of_row_swap_mod_gmp_partial_solve_wit_24 : row_swap_mod_gmp_partial_solve_wit_24.

End VC_Correct.
