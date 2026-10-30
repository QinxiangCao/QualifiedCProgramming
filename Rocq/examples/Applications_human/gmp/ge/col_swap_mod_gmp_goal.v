From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.ge.ge_gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.gmp.ge Require Import ge_gmp_array_strategy_goal.
From SimpleC.EE.Applications_human.gmp.ge Require Import ge_gmp_array_strategy_proof.

(*----- Function col_swap_mod_gmp -----*)

Definition col_swap_mod_gmp_safety_wit_1 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 256)) (PreH4 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH5 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH6 : (0 <= c1_pre)) (PreH7 : (c1_pre < n_pre)) (PreH8 : (0 <= c2_pre)) (PreH9 : (c2_pre < n_pre)) (PreH10 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH11 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )),
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition col_swap_mod_gmp_safety_wit_2 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 256)) (PreH4 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH5 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH6 : (0 <= c1_pre)) (PreH7 : (c1_pre < n_pre)) (PreH8 : (0 <= c2_pre)) (PreH9 : (c2_pre < n_pre)) (PreH10 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH11 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )),
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition col_swap_mod_gmp_safety_wit_3 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 256)) (PreH4 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH5 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH6 : (0 <= c1_pre)) (PreH7 : (c1_pre < n_pre)) (PreH8 : (0 <= c2_pre)) (PreH9 : (c2_pre < n_pre)) (PreH10 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH11 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cols" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition col_swap_mod_gmp_safety_wit_4 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (0 <= ((i * cols ) + c2_pre ))) (PreH19 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition col_swap_mod_gmp_safety_wit_5 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (i >= n_pre)) (PreH19 : (INT_MIN <= (i * cols ))) (PreH20 : ((i * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH22 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH24 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition col_swap_mod_gmp_safety_wit_6 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (i >= n_pre)) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition col_swap_mod_gmp_safety_wit_7 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((( &( "idx1" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i * cols ) + c1_pre )) ”
.

Definition col_swap_mod_gmp_safety_wit_8 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((( &( "idx1" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ ((i * cols ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i * cols )) ”
.

Definition col_swap_mod_gmp_safety_wit_9 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((( &( "idx2" ) )) # Int  |->_)
  **  ((( &( "idx1" ) )) # Int  |-> ((i * cols ) + c1_pre ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i * cols ) + c2_pre )) ”
.

Definition col_swap_mod_gmp_safety_wit_10 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((( &( "idx2" ) )) # Int  |->_)
  **  ((( &( "idx1" ) )) # Int  |-> ((i * cols ) + c1_pre ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ ((i * cols ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i * cols )) ”
.

Definition col_swap_mod_gmp_safety_wit_11 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (lmid: (@list Z)) (tmp1: Z) (tmp2: Z) (cols: Z) (i: Z) (idx1: Z) (idx2: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (tmp1 <> 0)) (PreH3 : (tmp2 <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (0 <= (n_pre * cols ))) (PreH9 : ((n_pre * cols ) <= INT_MAX)) (PreH10 : (0 <= c1_pre)) (PreH11 : (c1_pre < n_pre)) (PreH12 : (0 <= c2_pre)) (PreH13 : (c2_pre < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (idx1 = ((i * cols ) + c1_pre ))) (PreH17 : (idx2 = ((i * cols ) + c2_pre ))) (PreH18 : (0 <= idx1)) (PreH19 : (idx1 < (n_pre * cols ))) (PreH20 : (0 <= idx2)) (PreH21 : (idx2 < (n_pre * cols ))) (PreH22 : (INT_MIN <= (i * cols ))) (PreH23 : ((i * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= idx1)) (PreH25 : (idx1 <= INT_MAX)) (PreH26 : (INT_MIN <= idx2)) (PreH27 : (idx2 <= INT_MAX)) (PreH28 : (lmid = (replace_Znth (idx1) ((Znth (idx2) (lcur) (0))) (lcur)))) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH31 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx2) ((Znth (((i * cols ) + c1_pre )) (lcur) (0))) (lmid)) )
  **  (store_Z tmp1 (Znth (((i * cols ) + c1_pre )) (lcur) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "idx1" ) )) # Int  |-> idx1)
  **  ((( &( "idx2" ) )) # Int  |-> idx2)
  **  (store_Z tmp2 (Znth (idx2) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition col_swap_mod_gmp_safety_wit_12 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (lmid: (@list Z)) (tmp1: Z) (tmp2: Z) (cols: Z) (i: Z) (idx1: Z) (idx2: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (tmp1 <> 0)) (PreH3 : (tmp2 <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (0 <= (n_pre * cols ))) (PreH9 : ((n_pre * cols ) <= INT_MAX)) (PreH10 : (0 <= c1_pre)) (PreH11 : (c1_pre < n_pre)) (PreH12 : (0 <= c2_pre)) (PreH13 : (c2_pre < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (idx1 = ((i * cols ) + c1_pre ))) (PreH17 : (idx2 = ((i * cols ) + c2_pre ))) (PreH18 : (0 <= idx1)) (PreH19 : (idx1 < (n_pre * cols ))) (PreH20 : (0 <= idx2)) (PreH21 : (idx2 < (n_pre * cols ))) (PreH22 : (INT_MIN <= (i * cols ))) (PreH23 : ((i * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= idx1)) (PreH25 : (idx1 <= INT_MAX)) (PreH26 : (INT_MIN <= idx2)) (PreH27 : (idx2 <= INT_MAX)) (PreH28 : (lmid = (replace_Znth (idx1) ((Znth (idx2) (lcur) (0))) (lcur)))) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH31 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx2) ((Znth (((i * cols ) + c1_pre )) (lcur) (0))) (lmid)) )
  **  (store_Z tmp1 (Znth (((i * cols ) + c1_pre )) (lcur) (0)) )
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "tmp1" ) )) # Ptr  |-> tmp1)
  **  ((( &( "tmp2" ) )) # Ptr  |-> tmp2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "idx1" ) )) # Int  |-> idx1)
  **  ((( &( "idx2" ) )) # Int  |-> idx2)
  **  (store_Z tmp2 (Znth (idx2) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition col_swap_mod_gmp_entail_wit_1 :=
(
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH8 : (0 <= c1_pre)) (PreH9 : (c1_pre < n_pre)) (PreH10 : (0 <= c2_pre)) (PreH11 : (c2_pre < n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH13 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )),
  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  EX (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)),
  “ (aug_pre <> 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ”
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ”
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= ((0 * (n_pre + 1 ) ) + c1_pre )) ”
  &&  “ (((0 * (n_pre + 1 ) ) + c1_pre ) < (n_pre * (n_pre + 1 ) )) ”
  &&  “ (0 <= ((0 * (n_pre + 1 ) ) + c2_pre )) ”
  &&  “ (((0 * (n_pre + 1 ) ) + c2_pre ) < (n_pre * (n_pre + 1 ) )) ”
  &&  “ (INT_MIN <= (0 * (n_pre + 1 ) )) ”
  &&  “ ((0 * (n_pre + 1 ) ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((0 * (n_pre + 1 ) ) + c1_pre )) ”
  &&  “ (((0 * (n_pre + 1 ) ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((0 * (n_pre + 1 ) ) + c2_pre )) ”
  &&  “ (((0 * (n_pre + 1 ) ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre (n_pre + 1 ) M_low_level_spec c1_pre c2_pre 0 ) ”
  &&  (store_Z retval ztmp1 )
  **  (store_Z retval_2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
) \/
(
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH8 : (0 <= c1_pre)) (PreH9 : (c1_pre < n_pre)) (PreH10 : (0 <= c2_pre)) (PreH11 : (c2_pre < n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH13 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )),
  TT && emp 
|--
  “ (col_swap_prefix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec c1_pre c2_pre 0 ) ”
  &&  emp
).

Definition col_swap_mod_gmp_entail_wit_1_split_goal_1 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH8 : (0 <= c1_pre)) (PreH9 : (c1_pre < n_pre)) (PreH10 : (0 <= c2_pre)) (PreH11 : (c2_pre < n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH13 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )),
  (col_swap_prefix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec c1_pre c2_pre 0 )
.

Definition col_swap_mod_gmp_entail_wit_2 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur_2: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur_2 n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (((i * cols ) + c1_pre )) ((Znth (((i * (n_pre + 1 ) ) + c2_pre )) (lcur_2) (0))) (lcur_2)) )
  **  (store_Z tmp2 (Znth (((i * (n_pre + 1 ) ) + c2_pre )) (lcur_2) (0)) )
  **  (store_Z tmp1 (Znth (((i * cols ) + c1_pre )) (lcur_2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
|--
  EX (lcur: (@list Z)) (lmid: (@list Z)),
  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (((i * cols ) + c1_pre ) = ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) = ((i * cols ) + c2_pre )) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (lmid = (replace_Znth (((i * cols ) + c1_pre )) ((Znth (((i * cols ) + c2_pre )) (lcur) (0))) (lcur))) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp1 (Znth (((i * cols ) + c1_pre )) (lcur) (0)) )
  **  (store_Z tmp2 (Znth (((i * cols ) + c2_pre )) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lmid )
.

Definition col_swap_mod_gmp_entail_wit_3 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur_2: (@list Z)) (lmid: (@list Z)) (tmp1: Z) (tmp2: Z) (cols: Z) (i: Z) (idx1: Z) (idx2: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (tmp1 <> 0)) (PreH3 : (tmp2 <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (0 <= (n_pre * cols ))) (PreH9 : ((n_pre * cols ) <= INT_MAX)) (PreH10 : (0 <= c1_pre)) (PreH11 : (c1_pre < n_pre)) (PreH12 : (0 <= c2_pre)) (PreH13 : (c2_pre < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (idx1 = ((i * cols ) + c1_pre ))) (PreH17 : (idx2 = ((i * cols ) + c2_pre ))) (PreH18 : (0 <= idx1)) (PreH19 : (idx1 < (n_pre * cols ))) (PreH20 : (0 <= idx2)) (PreH21 : (idx2 < (n_pre * cols ))) (PreH22 : (INT_MIN <= (i * cols ))) (PreH23 : ((i * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= idx1)) (PreH25 : (idx1 <= INT_MAX)) (PreH26 : (INT_MIN <= idx2)) (PreH27 : (idx2 <= INT_MAX)) (PreH28 : (lmid = (replace_Znth (idx1) ((Znth (idx2) (lcur_2) (0))) (lcur_2)))) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH31 : (col_swap_prefix lcur_2 n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (idx2) ((Znth (((i * cols ) + c1_pre )) (lcur_2) (0))) (lmid)) )
  **  (store_Z tmp1 (Znth (((i * cols ) + c1_pre )) (lcur_2) (0)) )
  **  (store_Z tmp2 (Znth (idx2) (lcur_2) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
|--
  (EX (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)),
  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((i + 1 ) >= n_pre) ”
  &&  “ (0 <= (((i + 1 ) * cols ) + c2_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ”
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + c1_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + c2_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre (i + 1 ) ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (EX (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)),
  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((i + 1 ) >= n_pre) ”
  &&  “ ((i + 1 ) >= n_pre) ”
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ”
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + c1_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + c2_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre (i + 1 ) ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (EX (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)),
  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (((i + 1 ) * cols ) + c1_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (0 <= (((i + 1 ) * cols ) + c2_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ”
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + c1_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + c2_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre (i + 1 ) ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (EX (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)),
  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (((i + 1 ) * cols ) + c1_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ ((i + 1 ) >= n_pre) ”
  &&  “ (INT_MIN <= ((i + 1 ) * cols )) ”
  &&  “ (((i + 1 ) * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + c1_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= (((i + 1 ) * cols ) + c2_pre )) ”
  &&  “ ((((i + 1 ) * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre (i + 1 ) ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
.

Definition col_swap_mod_gmp_return_wit_1 :=
(
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (0 <= ((i * cols ) + c2_pre ))) (PreH19 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)),
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (0 <= ((i * cols ) + c2_pre ))) (PreH19 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)),
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition col_swap_mod_gmp_return_wit_2 :=
(
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (i >= n_pre)) (PreH19 : (INT_MIN <= (i * cols ))) (PreH20 : ((i * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH22 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH24 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)),
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (i >= n_pre)) (PreH19 : (INT_MIN <= (i * cols ))) (PreH20 : ((i * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH22 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH24 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)),
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition col_swap_mod_gmp_return_wit_3 :=
(
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)),
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)),
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition col_swap_mod_gmp_return_wit_4 :=
(
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (i >= n_pre)) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)),
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (i >= n_pre)) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)),
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_col_swap (M_low_level_spec) (c1_pre) (c2_pre)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition col_swap_mod_gmp_partial_solve_wit_1 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 256)) (PreH4 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH5 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH6 : (0 <= c1_pre)) (PreH7 : (c1_pre < n_pre)) (PreH8 : (0 <= c2_pre)) (PreH9 : (c2_pre < n_pre)) (PreH10 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH11 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )),
  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (aug_pre <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ”
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition col_swap_mod_gmp_partial_solve_wit_2 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 256)) (PreH5 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH6 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH7 : (0 <= c1_pre)) (PreH8 : (c1_pre < n_pre)) (PreH9 : (0 <= c2_pre)) (PreH10 : (c2_pre < n_pre)) (PreH11 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH12 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )),
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
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition col_swap_mod_gmp_partial_solve_wit_3 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 256)) (PreH5 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH6 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH7 : (0 <= c1_pre)) (PreH8 : (c1_pre < n_pre)) (PreH9 : (0 <= c2_pre)) (PreH10 : (c2_pre < n_pre)) (PreH11 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH12 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )),
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
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition col_swap_mod_gmp_partial_solve_wit_4 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (aug_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH7 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH8 : (0 <= c1_pre)) (PreH9 : (c1_pre < n_pre)) (PreH10 : (0 <= c2_pre)) (PreH11 : (c2_pre < n_pre)) (PreH12 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH13 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )),
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
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition col_swap_mod_gmp_partial_solve_wit_5 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i < n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z (aug_pre + (((i * cols ) + c1_pre ) * sizeof( "__mpz_struct" ))) (Znth (((i * cols ) + c1_pre )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre ((i * cols ) + c1_pre ) 0 (n_pre * cols ) lcur )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition col_swap_mod_gmp_partial_solve_wit_6 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z tmp1 (Znth (((i * cols ) + c1_pre )) (lcur) (0)) )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (i < n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp2 ztmp2 )
  **  (store_Z (aug_pre + (((i * cols ) + c2_pre ) * sizeof( "__mpz_struct" ))) (Znth (((i * cols ) + c2_pre )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre ((i * cols ) + c2_pre ) 0 (n_pre * cols ) lcur )
  **  (store_Z tmp1 (Znth (((i * cols ) + c1_pre )) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition col_swap_mod_gmp_partial_solve_wit_7 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i < n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z tmp2 (Znth (((i * cols ) + c2_pre )) (lcur) (0)) )
  **  (store_Z tmp1 (Znth (((i * cols ) + c1_pre )) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (i < n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z (aug_pre + (((i * cols ) + c1_pre ) * sizeof( "__mpz_struct" ))) (Znth (((i * cols ) + c1_pre )) (lcur) (0)) )
  **  (store_Z tmp2 (Znth (((i * (n_pre + 1 ) ) + c2_pre )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre ((i * cols ) + c1_pre ) 0 (n_pre * cols ) lcur )
  **  (store_Z tmp1 (Znth (((i * cols ) + c1_pre )) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition col_swap_mod_gmp_partial_solve_wit_8 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (lmid: (@list Z)) (tmp1: Z) (tmp2: Z) (cols: Z) (i: Z) (idx1: Z) (idx2: Z) (PreH1 : (aug_pre <> 0)) (PreH2 : (tmp1 <> 0)) (PreH3 : (tmp2 <> 0)) (PreH4 : (cols = (n_pre + 1 ))) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 256)) (PreH8 : (0 <= (n_pre * cols ))) (PreH9 : ((n_pre * cols ) <= INT_MAX)) (PreH10 : (0 <= c1_pre)) (PreH11 : (c1_pre < n_pre)) (PreH12 : (0 <= c2_pre)) (PreH13 : (c2_pre < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (idx1 = ((i * cols ) + c1_pre ))) (PreH17 : (idx2 = ((i * cols ) + c2_pre ))) (PreH18 : (0 <= idx1)) (PreH19 : (idx1 < (n_pre * cols ))) (PreH20 : (0 <= idx2)) (PreH21 : (idx2 < (n_pre * cols ))) (PreH22 : (INT_MIN <= (i * cols ))) (PreH23 : ((i * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= idx1)) (PreH25 : (idx1 <= INT_MAX)) (PreH26 : (INT_MIN <= idx2)) (PreH27 : (idx2 <= INT_MAX)) (PreH28 : (lmid = (replace_Znth (idx1) ((Znth (idx2) (lcur) (0))) (lcur)))) (PreH29 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH30 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH31 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
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
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (idx1 = ((i * cols ) + c1_pre )) ”
  &&  “ (idx2 = ((i * cols ) + c2_pre )) ”
  &&  “ (0 <= idx1) ”
  &&  “ (idx1 < (n_pre * cols )) ”
  &&  “ (0 <= idx2) ”
  &&  “ (idx2 < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= idx1) ”
  &&  “ (idx1 <= INT_MAX) ”
  &&  “ (INT_MIN <= idx2) ”
  &&  “ (idx2 <= INT_MAX) ”
  &&  “ (lmid = (replace_Znth (idx1) ((Znth (idx2) (lcur) (0))) (lcur))) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z (aug_pre + (idx2 * sizeof( "__mpz_struct" ))) (Znth (idx2) (lmid) (0)) )
  **  (store_Z tmp1 (Znth (((i * cols ) + c1_pre )) (lcur) (0)) )
  **  (mpz_missing_i aug_pre idx2 0 (n_pre * cols ) lmid )
  **  (store_Z tmp2 (Znth (idx2) (lcur) (0)) )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition col_swap_mod_gmp_partial_solve_wit_9 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (0 <= ((i * cols ) + c2_pre ))) (PreH19 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp2 ztmp2 )
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_10 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (i >= n_pre)) (PreH19 : (INT_MIN <= (i * cols ))) (PreH20 : ((i * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH22 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH24 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp2 ztmp2 )
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_11 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp2 ztmp2 )
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_12 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp2: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (i >= n_pre)) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z tmp1 ztmp1 )
  **  (store_Z tmp2 ztmp2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (i >= n_pre) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp2 ztmp2 )
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_13 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (0 <= ((i * cols ) + c2_pre ))) (PreH19 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_14 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (i >= n_pre)) (PreH19 : (INT_MIN <= (i * cols ))) (PreH20 : ((i * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH22 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH24 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_15 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_16 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (i >= n_pre)) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (i >= n_pre) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_17 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (0 <= ((i * cols ) + c2_pre ))) (PreH19 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_18 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (i >= n_pre)) (PreH19 : (INT_MIN <= (i * cols ))) (PreH20 : ((i * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH22 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH24 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_19 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_20 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (ztmp1: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (i >= n_pre)) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (i >= n_pre) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  (store_Z tmp1 ztmp1 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_21 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (0 <= ((i * cols ) + c2_pre ))) (PreH19 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_22 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (i >= n_pre)) (PreH18 : (i >= n_pre)) (PreH19 : (INT_MIN <= (i * cols ))) (PreH20 : ((i * cols ) <= INT_MAX)) (PreH21 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH22 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH24 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (i >= n_pre) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_23 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (0 <= ((i * cols ) + c2_pre ))) (PreH20 : (((i * cols ) + c2_pre ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (i * cols ))) (PreH22 : ((i * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH24 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH25 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH26 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH27 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH29 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (0 <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) < (n_pre * cols )) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
  &&  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition col_swap_mod_gmp_partial_solve_wit_24 :=
forall (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (n_pre: Z) (p_pre: Z) (aug_pre: Z) (c1_pre: Z) (c2_pre: Z) (lcur: (@list Z)) (i: Z) (cols: Z) (tmp2: Z) (tmp1: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i >= n_pre)) (PreH2 : (aug_pre <> 0)) (PreH3 : (tmp1 <> 0)) (PreH4 : (tmp2 <> 0)) (PreH5 : (cols = (n_pre + 1 ))) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 256)) (PreH9 : (0 <= (n_pre * cols ))) (PreH10 : ((n_pre * cols ) <= INT_MAX)) (PreH11 : (0 <= c1_pre)) (PreH12 : (c1_pre < n_pre)) (PreH13 : (0 <= c2_pre)) (PreH14 : (c2_pre < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= ((i * cols ) + c1_pre ))) (PreH18 : (((i * cols ) + c1_pre ) < (n_pre * cols ))) (PreH19 : (i >= n_pre)) (PreH20 : (INT_MIN <= (i * cols ))) (PreH21 : ((i * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((i * cols ) + c1_pre ))) (PreH23 : (((i * cols ) + c1_pre ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((i * cols ) + c2_pre ))) (PreH25 : (((i * cols ) + c2_pre ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i )),
  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (i >= n_pre) ”
  &&  “ (aug_pre <> 0) ”
  &&  “ (tmp1 <> 0) ”
  &&  “ (tmp2 <> 0) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (cols = (n_pre + 1 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 256) ”
  &&  “ (0 <= (n_pre * cols )) ”
  &&  “ ((n_pre * cols ) <= INT_MAX) ”
  &&  “ (0 <= c1_pre) ”
  &&  “ (c1_pre < n_pre) ”
  &&  “ (0 <= c2_pre) ”
  &&  “ (c2_pre < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) < (n_pre * cols )) ”
  &&  “ (i >= n_pre) ”
  &&  “ (INT_MIN <= (i * cols )) ”
  &&  “ ((i * cols ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c1_pre )) ”
  &&  “ (((i * cols ) + c1_pre ) <= INT_MAX) ”
  &&  “ (INT_MIN <= ((i * cols ) + c2_pre )) ”
  &&  “ (((i * cols ) + c2_pre ) <= INT_MAX) ”
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ”
  &&  “ (col_swap_prefix lcur n_pre cols M_low_level_spec c1_pre c2_pre i ) ”
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

Axiom proof_of_col_swap_mod_gmp_safety_wit_1 : col_swap_mod_gmp_safety_wit_1.
Axiom proof_of_col_swap_mod_gmp_safety_wit_2 : col_swap_mod_gmp_safety_wit_2.
Axiom proof_of_col_swap_mod_gmp_safety_wit_3 : col_swap_mod_gmp_safety_wit_3.
Axiom proof_of_col_swap_mod_gmp_safety_wit_4 : col_swap_mod_gmp_safety_wit_4.
Axiom proof_of_col_swap_mod_gmp_safety_wit_5 : col_swap_mod_gmp_safety_wit_5.
Axiom proof_of_col_swap_mod_gmp_safety_wit_6 : col_swap_mod_gmp_safety_wit_6.
Axiom proof_of_col_swap_mod_gmp_safety_wit_7 : col_swap_mod_gmp_safety_wit_7.
Axiom proof_of_col_swap_mod_gmp_safety_wit_8 : col_swap_mod_gmp_safety_wit_8.
Axiom proof_of_col_swap_mod_gmp_safety_wit_9 : col_swap_mod_gmp_safety_wit_9.
Axiom proof_of_col_swap_mod_gmp_safety_wit_10 : col_swap_mod_gmp_safety_wit_10.
Axiom proof_of_col_swap_mod_gmp_safety_wit_11 : col_swap_mod_gmp_safety_wit_11.
Axiom proof_of_col_swap_mod_gmp_safety_wit_12 : col_swap_mod_gmp_safety_wit_12.
Axiom proof_of_col_swap_mod_gmp_entail_wit_1 : col_swap_mod_gmp_entail_wit_1.
Axiom proof_of_col_swap_mod_gmp_entail_wit_2 : col_swap_mod_gmp_entail_wit_2.
Axiom proof_of_col_swap_mod_gmp_entail_wit_3 : col_swap_mod_gmp_entail_wit_3.
Axiom proof_of_col_swap_mod_gmp_return_wit_1 : col_swap_mod_gmp_return_wit_1.
Axiom proof_of_col_swap_mod_gmp_return_wit_2 : col_swap_mod_gmp_return_wit_2.
Axiom proof_of_col_swap_mod_gmp_return_wit_3 : col_swap_mod_gmp_return_wit_3.
Axiom proof_of_col_swap_mod_gmp_return_wit_4 : col_swap_mod_gmp_return_wit_4.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_1 : col_swap_mod_gmp_partial_solve_wit_1.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_2 : col_swap_mod_gmp_partial_solve_wit_2.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_3 : col_swap_mod_gmp_partial_solve_wit_3.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_4 : col_swap_mod_gmp_partial_solve_wit_4.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_5 : col_swap_mod_gmp_partial_solve_wit_5.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_6 : col_swap_mod_gmp_partial_solve_wit_6.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_7 : col_swap_mod_gmp_partial_solve_wit_7.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_8 : col_swap_mod_gmp_partial_solve_wit_8.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_9 : col_swap_mod_gmp_partial_solve_wit_9.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_10 : col_swap_mod_gmp_partial_solve_wit_10.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_11 : col_swap_mod_gmp_partial_solve_wit_11.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_12 : col_swap_mod_gmp_partial_solve_wit_12.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_13 : col_swap_mod_gmp_partial_solve_wit_13.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_14 : col_swap_mod_gmp_partial_solve_wit_14.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_15 : col_swap_mod_gmp_partial_solve_wit_15.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_16 : col_swap_mod_gmp_partial_solve_wit_16.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_17 : col_swap_mod_gmp_partial_solve_wit_17.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_18 : col_swap_mod_gmp_partial_solve_wit_18.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_19 : col_swap_mod_gmp_partial_solve_wit_19.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_20 : col_swap_mod_gmp_partial_solve_wit_20.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_21 : col_swap_mod_gmp_partial_solve_wit_21.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_22 : col_swap_mod_gmp_partial_solve_wit_22.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_23 : col_swap_mod_gmp_partial_solve_wit_23.
Axiom proof_of_col_swap_mod_gmp_partial_solve_wit_24 : col_swap_mod_gmp_partial_solve_wit_24.

End VC_Correct.
