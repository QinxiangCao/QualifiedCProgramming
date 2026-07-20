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

(*----- Function row_scale_mod_gmp -----*)

Definition row_scale_mod_gmp_safety_wit_1 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (zp_low_level_spec > 0)) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (0 <= row_pre)) (PreH10 : (row_pre < n_pre)) (PreH11 : (0 <= zinv_low_level_spec)) (PreH12 : (zinv_low_level_spec < zp_low_level_spec)) (PreH13 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH14 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition row_scale_mod_gmp_safety_wit_2 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (zp_low_level_spec > 0)) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (0 <= row_pre)) (PreH10 : (row_pre < n_pre)) (PreH11 : (0 <= zinv_low_level_spec)) (PreH12 : (zinv_low_level_spec < zp_low_level_spec)) (PreH13 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH14 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((( &( "cols" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition row_scale_mod_gmp_safety_wit_3 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (zp_low_level_spec > 0)) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (0 <= row_pre)) (PreH10 : (row_pre < n_pre)) (PreH11 : (0 <= zinv_low_level_spec)) (PreH12 : (zinv_low_level_spec < zp_low_level_spec)) (PreH13 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH14 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cols" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition row_scale_mod_gmp_safety_wit_4 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (tv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (row_pre * cols ))) (PreH21 : ((row_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH23 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z v tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ False ”
.

Definition row_scale_mod_gmp_safety_wit_5 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (tv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (0 <= ((row_pre * cols ) + j ))) (PreH20 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (row_pre * cols ))) (PreH22 : ((row_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH24 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z v tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (((row_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((row_pre * cols ) + j )) ”
.

Definition row_scale_mod_gmp_safety_wit_6 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (tv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (0 <= ((row_pre * cols ) + j ))) (PreH20 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (row_pre * cols ))) (PreH22 : ((row_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH24 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z v tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ ((row_pre * cols ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (row_pre * cols )) ”
.

Definition row_scale_mod_gmp_safety_wit_7 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec ((Znth (((row_pre * cols ) + j )) (lcur) (0)) * zinv_low_level_spec ) out )) (PreH2 : (j < cols)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (inv_pre <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= row_pre)) (PreH15 : (row_pre < n_pre)) (PreH16 : (0 <= zinv_low_level_spec)) (PreH17 : (zinv_low_level_spec < zp_low_level_spec)) (PreH18 : (0 <= j)) (PreH19 : (j <= cols)) (PreH20 : (0 <= ((row_pre * cols ) + j ))) (PreH21 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH22 : (INT_MIN <= (row_pre * cols ))) (PreH23 : ((row_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH25 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (((row_pre * cols ) + j )) (out) (lcur)) )
  **  (store_Z v ((Znth (((row_pre * cols ) + j )) (lcur) (0)) * zinv_low_level_spec ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  ((( &( "cell" ) )) # Ptr  |-> (aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))))
  **  ((( &( "idx" ) )) # Int  |-> ((row_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition row_scale_mod_gmp_safety_wit_8 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec ((Znth (((row_pre * cols ) + j )) (lcur) (0)) * zinv_low_level_spec ) out )) (PreH2 : (j < cols)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (inv_pre <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= row_pre)) (PreH15 : (row_pre < n_pre)) (PreH16 : (0 <= zinv_low_level_spec)) (PreH17 : (zinv_low_level_spec < zp_low_level_spec)) (PreH18 : (0 <= j)) (PreH19 : (j <= cols)) (PreH20 : (0 <= ((row_pre * cols ) + j ))) (PreH21 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH22 : (INT_MIN <= (row_pre * cols ))) (PreH23 : ((row_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH25 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (((row_pre * cols ) + j )) (out) (lcur)) )
  **  (store_Z v ((Znth (((row_pre * cols ) + j )) (lcur) (0)) * zinv_low_level_spec ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  ((( &( "cell" ) )) # Ptr  |-> (aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))))
  **  ((( &( "idx" ) )) # Int  |-> ((row_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition row_scale_mod_gmp_entail_wit_1 := 
(
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (zp_low_level_spec > 0)) (PreH8 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH9 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH10 : (0 <= row_pre)) (PreH11 : (row_pre < n_pre)) (PreH12 : (0 <= zinv_low_level_spec)) (PreH13 : (zinv_low_level_spec < zp_low_level_spec)) (PreH14 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  EX (tv: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((row_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((row_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) )) ” 
  &&  “ (INT_MIN <= (row_pre * (n_pre + 1 ) )) ” 
  &&  “ ((row_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((row_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((row_pre * (n_pre + 1 ) ) + 0 ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (row_scale_prefix lcur n_pre (n_pre + 1 ) M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec 0 ) ”
  &&  (store_Z retval tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) lcur )
) \/
(
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (zp_low_level_spec > 0)) (PreH8 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH9 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH10 : (0 <= row_pre)) (PreH11 : (row_pre < n_pre)) (PreH12 : (0 <= zinv_low_level_spec)) (PreH13 : (zinv_low_level_spec < zp_low_level_spec)) (PreH14 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (store_Z retval 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
|--
  EX (tv: Z) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((row_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((row_pre * (n_pre + 1 ) ) + 0 ) < (n_pre * (n_pre + 1 ) )) ” 
  &&  “ (INT_MIN <= (row_pre * (n_pre + 1 ) )) ” 
  &&  “ ((row_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((row_pre * (n_pre + 1 ) ) + 0 )) ” 
  &&  “ (((row_pre * (n_pre + 1 ) ) + 0 ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (row_scale_prefix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec 0 ) ”
  &&  (store_Z retval tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
).

Definition row_scale_mod_gmp_entail_wit_2 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur_2: (@list Z)) (j: Z) (cols: Z) (v: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec ((Znth (((row_pre * cols ) + j )) (lcur_2) (0)) * zinv_low_level_spec ) out )) (PreH2 : (j < cols)) (PreH3 : (aug_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (inv_pre <> 0)) (PreH6 : (v <> 0)) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (cols = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 256)) (PreH11 : (zp_low_level_spec > 0)) (PreH12 : (0 <= (n_pre * cols ))) (PreH13 : ((n_pre * cols ) <= INT_MAX)) (PreH14 : (0 <= row_pre)) (PreH15 : (row_pre < n_pre)) (PreH16 : (0 <= zinv_low_level_spec)) (PreH17 : (zinv_low_level_spec < zp_low_level_spec)) (PreH18 : (0 <= j)) (PreH19 : (j <= cols)) (PreH20 : (0 <= ((row_pre * cols ) + j ))) (PreH21 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH22 : (INT_MIN <= (row_pre * cols ))) (PreH23 : ((row_pre * cols ) <= INT_MAX)) (PreH24 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH25 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH26 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH28 : (row_scale_prefix lcur_2 n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) (replace_Znth (((row_pre * cols ) + j )) (out) (lcur_2)) )
  **  (store_Z v ((Znth (((row_pre * cols ) + j )) (lcur_2) (0)) * zinv_low_level_spec ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
|--
  (EX (tv: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ (0 <= ((row_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((row_pre * cols ) + (j + 1 ) ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (row_pre * cols )) ” 
  &&  “ ((row_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((row_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((row_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec (j + 1 ) ) ”
  &&  (store_Z v tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
  ||
  (EX (tv: Z)  (lcur: (@list Z)) ,
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cols) ” 
  &&  “ ((j + 1 ) >= cols) ” 
  &&  “ (INT_MIN <= (row_pre * cols )) ” 
  &&  “ ((row_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((row_pre * cols ) + (j + 1 ) )) ” 
  &&  “ (((row_pre * cols ) + (j + 1 ) ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec (j + 1 ) ) ”
  &&  (store_Z v tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur ))
.

Definition row_scale_mod_gmp_return_wit_1 := 
(
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (0 <= ((row_pre * cols ) + j ))) (PreH20 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (row_pre * cols ))) (PreH22 : ((row_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH24 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M_low_level_spec) (row_pre) (zinv_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M_low_level_spec) (row_pre) (zinv_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (0 <= ((row_pre * cols ) + j ))) (PreH20 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (row_pre * cols ))) (PreH22 : ((row_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH24 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M_low_level_spec) (row_pre) (zinv_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M_low_level_spec) (row_pre) (zinv_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition row_scale_mod_gmp_return_wit_2 := 
(
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (row_pre * cols ))) (PreH21 : ((row_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH23 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M_low_level_spec) (row_pre) (zinv_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M_low_level_spec) (row_pre) (zinv_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
) \/
(
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (row_pre * cols ))) (PreH21 : ((row_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH23 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  EX (l2: (@list Z)) ,
  “ (rep_matrix l2 n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M_low_level_spec) (row_pre) (zinv_low_level_spec)) ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) (matrix_row_scale_mod (zp_low_level_spec) (M_low_level_spec) (row_pre) (zinv_low_level_spec)) ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l2 )
).

Definition row_scale_mod_gmp_partial_solve_wit_1 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (PreH1 : (aug_pre <> 0)) (PreH2 : (p_pre <> 0)) (PreH3 : (inv_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 256)) (PreH6 : (zp_low_level_spec > 0)) (PreH7 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH8 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH9 : (0 <= row_pre)) (PreH10 : (row_pre < n_pre)) (PreH11 : (0 <= zinv_low_level_spec)) (PreH12 : (zinv_low_level_spec < zp_low_level_spec)) (PreH13 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH14 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition row_scale_mod_gmp_partial_solve_wit_2 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 256)) (PreH7 : (zp_low_level_spec > 0)) (PreH8 : (0 <= (n_pre * (n_pre + 1 ) ))) (PreH9 : ((n_pre * (n_pre + 1 ) ) <= INT_MAX)) (PreH10 : (0 <= row_pre)) (PreH11 : (row_pre < n_pre)) (PreH12 : (0 <= zinv_low_level_spec)) (PreH13 : (zinv_low_level_spec < zp_low_level_spec)) (PreH14 : (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) (PreH15 : (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec )) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * (n_pre + 1 ) )) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre (n_pre + 1 ) M_low_level_spec ) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * (n_pre + 1 ) ) l_low_level_spec )
.

Definition row_scale_mod_gmp_partial_solve_wit_3 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (tv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (0 <= ((row_pre * cols ) + j ))) (PreH20 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (row_pre * cols ))) (PreH22 : ((row_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH24 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (store_Z v tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j < cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((row_pre * cols ) + j )) ” 
  &&  “ (((row_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (row_pre * cols )) ” 
  &&  “ ((row_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((row_pre * cols ) + j )) ” 
  &&  “ (((row_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j ) ”
  &&  (store_Z v tv )
  **  (store_Z (aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) (Znth (((row_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_missing_i aug_pre ((row_pre * cols ) + j ) 0 (n_pre * cols ) lcur )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition row_scale_mod_gmp_partial_solve_wit_4_pure := 
(
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (0 <= ((row_pre * cols ) + j ))) (PreH20 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (row_pre * cols ))) (PreH22 : ((row_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH24 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z v ((Znth (((row_pre * cols ) + j )) (lcur) (0)) * zinv_low_level_spec ) )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  ((( &( "cell" ) )) # Ptr  |-> (aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))))
  **  ((( &( "idx" ) )) # Int  |-> ((row_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ ((aug_pre + (((row_pre * (n_pre + 1 ) ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ”
) \/
(
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (cols <= INT_MAX)) (PreH3 : (row_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (cols >= INT_MIN)) (PreH7 : (row_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (((row_pre * cols ) + j ) >= INT_MIN)) (PreH10 : (j < cols)) (PreH11 : (aug_pre <> 0)) (PreH12 : (p_pre <> 0)) (PreH13 : (inv_pre <> 0)) (PreH14 : (v <> 0)) (PreH15 : (cols = (n_pre + 1 ))) (PreH16 : (cols = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (zp_low_level_spec > 0)) (PreH20 : (0 <= (n_pre * cols ))) (PreH21 : ((n_pre * cols ) <= INT_MAX)) (PreH22 : (0 <= row_pre)) (PreH23 : (row_pre < n_pre)) (PreH24 : (0 <= zinv_low_level_spec)) (PreH25 : (zinv_low_level_spec < zp_low_level_spec)) (PreH26 : (0 <= j)) (PreH27 : (j <= cols)) (PreH28 : (0 <= ((row_pre * cols ) + j ))) (PreH29 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH30 : (INT_MIN <= (row_pre * cols ))) (PreH31 : ((row_pre * cols ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH33 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z v ((Znth (((row_pre * cols ) + j )) (lcur) (0)) * zinv_low_level_spec ) )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  ((( &( "cell" ) )) # Ptr  |-> (aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))))
  **  ((( &( "idx" ) )) # Int  |-> ((row_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((aug_pre + (((row_pre * (n_pre + 1 ) ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ” 
  &&  “ ((aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ”
).

Definition row_scale_mod_gmp_partial_solve_wit_4_pure_split_goal_1 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (cols <= INT_MAX)) (PreH3 : (row_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (cols >= INT_MIN)) (PreH7 : (row_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (((row_pre * cols ) + j ) >= INT_MIN)) (PreH10 : (j < cols)) (PreH11 : (aug_pre <> 0)) (PreH12 : (p_pre <> 0)) (PreH13 : (inv_pre <> 0)) (PreH14 : (v <> 0)) (PreH15 : (cols = (n_pre + 1 ))) (PreH16 : (cols = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (zp_low_level_spec > 0)) (PreH20 : (0 <= (n_pre * cols ))) (PreH21 : ((n_pre * cols ) <= INT_MAX)) (PreH22 : (0 <= row_pre)) (PreH23 : (row_pre < n_pre)) (PreH24 : (0 <= zinv_low_level_spec)) (PreH25 : (zinv_low_level_spec < zp_low_level_spec)) (PreH26 : (0 <= j)) (PreH27 : (j <= cols)) (PreH28 : (0 <= ((row_pre * cols ) + j ))) (PreH29 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH30 : (INT_MIN <= (row_pre * cols ))) (PreH31 : ((row_pre * cols ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH33 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z v ((Znth (((row_pre * cols ) + j )) (lcur) (0)) * zinv_low_level_spec ) )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  ((( &( "cell" ) )) # Ptr  |-> (aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))))
  **  ((( &( "idx" ) )) # Int  |-> ((row_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((aug_pre + (((row_pre * (n_pre + 1 ) ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ”
.

Definition row_scale_mod_gmp_partial_solve_wit_4_pure_split_goal_2 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (cols <= INT_MAX)) (PreH3 : (row_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (cols >= INT_MIN)) (PreH7 : (row_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (((row_pre * cols ) + j ) >= INT_MIN)) (PreH10 : (j < cols)) (PreH11 : (aug_pre <> 0)) (PreH12 : (p_pre <> 0)) (PreH13 : (inv_pre <> 0)) (PreH14 : (v <> 0)) (PreH15 : (cols = (n_pre + 1 ))) (PreH16 : (cols = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 256)) (PreH19 : (zp_low_level_spec > 0)) (PreH20 : (0 <= (n_pre * cols ))) (PreH21 : ((n_pre * cols ) <= INT_MAX)) (PreH22 : (0 <= row_pre)) (PreH23 : (row_pre < n_pre)) (PreH24 : (0 <= zinv_low_level_spec)) (PreH25 : (zinv_low_level_spec < zp_low_level_spec)) (PreH26 : (0 <= j)) (PreH27 : (j <= cols)) (PreH28 : (0 <= ((row_pre * cols ) + j ))) (PreH29 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH30 : (INT_MIN <= (row_pre * cols ))) (PreH31 : ((row_pre * cols ) <= INT_MAX)) (PreH32 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH33 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH34 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH35 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH36 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z v ((Znth (((row_pre * cols ) + j )) (lcur) (0)) * zinv_low_level_spec ) )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  ((( &( "cell" ) )) # Ptr  |-> (aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))))
  **  ((( &( "idx" ) )) # Int  |-> ((row_pre * cols ) + j ))
  **  ((( &( "aug" ) )) # Ptr  |-> aug_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "inv" ) )) # Ptr  |-> inv_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row_pre)
  **  ((( &( "cols" ) )) # Int  |-> cols)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ”
.

Definition row_scale_mod_gmp_partial_solve_wit_4_aux := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j < cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (0 <= ((row_pre * cols ) + j ))) (PreH20 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (row_pre * cols ))) (PreH22 : ((row_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH24 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (mpz_array aug_pre (n_pre * cols ) lcur )
  **  (store_Z v ((Znth (((row_pre * cols ) + j )) (lcur) (0)) * zinv_low_level_spec ) )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ ((aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ ((aug_pre + (((row_pre * (n_pre + 1 ) ) + j ) * sizeof( "__mpz_struct" ))) <> 0) ” 
  &&  “ (j < cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((row_pre * cols ) + j )) ” 
  &&  “ (((row_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (row_pre * cols )) ” 
  &&  “ ((row_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((row_pre * cols ) + j )) ” 
  &&  “ (((row_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j ) ”
  &&  (store_Z (aug_pre + (((row_pre * cols ) + j ) * sizeof( "__mpz_struct" ))) (Znth (((row_pre * cols ) + j )) (lcur) (0)) )
  **  (store_Z v ((Znth (((row_pre * cols ) + j )) (lcur) (0)) * zinv_low_level_spec ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (mpz_missing_i aug_pre ((row_pre * cols ) + j ) 0 (n_pre * cols ) lcur )
  **  (store_Z inv_pre zinv_low_level_spec )
.

Definition row_scale_mod_gmp_partial_solve_wit_4 := row_scale_mod_gmp_partial_solve_wit_4_pure -> row_scale_mod_gmp_partial_solve_wit_4_aux.

Definition row_scale_mod_gmp_partial_solve_wit_5 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (tv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (0 <= ((row_pre * cols ) + j ))) (PreH20 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (row_pre * cols ))) (PreH22 : ((row_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH24 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (store_Z v tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((row_pre * cols ) + j )) ” 
  &&  “ (((row_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (row_pre * cols )) ” 
  &&  “ ((row_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((row_pre * cols ) + j )) ” 
  &&  “ (((row_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j ) ”
  &&  (store_Z v tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_scale_mod_gmp_partial_solve_wit_6 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (tv: Z) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (row_pre * cols ))) (PreH21 : ((row_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH23 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  (store_Z v tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (row_pre * cols )) ” 
  &&  “ ((row_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((row_pre * cols ) + j )) ” 
  &&  “ (((row_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j ) ”
  &&  (store_Z v tv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_scale_mod_gmp_partial_solve_wit_7 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (0 <= ((row_pre * cols ) + j ))) (PreH20 : (((row_pre * cols ) + j ) < (n_pre * cols ))) (PreH21 : (INT_MIN <= (row_pre * cols ))) (PreH22 : ((row_pre * cols ) <= INT_MAX)) (PreH23 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH24 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH25 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH27 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (0 <= ((row_pre * cols ) + j )) ” 
  &&  “ (((row_pre * cols ) + j ) < (n_pre * cols )) ” 
  &&  “ (INT_MIN <= (row_pre * cols )) ” 
  &&  “ ((row_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((row_pre * cols ) + j )) ” 
  &&  “ (((row_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j ) ”
  &&  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Definition row_scale_mod_gmp_partial_solve_wit_8 := 
forall (inv_pre: Z) (row_pre: Z) (aug_pre: Z) (p_pre: Z) (n_pre: Z) (zinv_low_level_spec: Z) (zp_low_level_spec: Z) (l_low_level_spec: (@list Z)) (M_low_level_spec: matrix) (lcur: (@list Z)) (j: Z) (cols: Z) (v: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (j >= cols)) (PreH2 : (aug_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (inv_pre <> 0)) (PreH5 : (v <> 0)) (PreH6 : (cols = (n_pre + 1 ))) (PreH7 : (cols = (n_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 256)) (PreH10 : (zp_low_level_spec > 0)) (PreH11 : (0 <= (n_pre * cols ))) (PreH12 : ((n_pre * cols ) <= INT_MAX)) (PreH13 : (0 <= row_pre)) (PreH14 : (row_pre < n_pre)) (PreH15 : (0 <= zinv_low_level_spec)) (PreH16 : (zinv_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= j)) (PreH18 : (j <= cols)) (PreH19 : (j >= cols)) (PreH20 : (INT_MIN <= (row_pre * cols ))) (PreH21 : ((row_pre * cols ) <= INT_MAX)) (PreH22 : (INT_MIN <= ((row_pre * cols ) + j ))) (PreH23 : (((row_pre * cols ) + j ) <= INT_MAX)) (PreH24 : (rep_matrix l_low_level_spec n_pre cols M_low_level_spec )) (PreH25 : (mat_mod zp_low_level_spec n_pre cols M_low_level_spec )) (PreH26 : (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j )) ,
  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
|--
  “ (j >= cols) ” 
  &&  “ (aug_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (inv_pre <> 0) ” 
  &&  “ (v <> 0) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (cols = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 256) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= (n_pre * cols )) ” 
  &&  “ ((n_pre * cols ) <= INT_MAX) ” 
  &&  “ (0 <= row_pre) ” 
  &&  “ (row_pre < n_pre) ” 
  &&  “ (0 <= zinv_low_level_spec) ” 
  &&  “ (zinv_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cols) ” 
  &&  “ (j >= cols) ” 
  &&  “ (INT_MIN <= (row_pre * cols )) ” 
  &&  “ ((row_pre * cols ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((row_pre * cols ) + j )) ” 
  &&  “ (((row_pre * cols ) + j ) <= INT_MAX) ” 
  &&  “ (rep_matrix l_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (mat_mod zp_low_level_spec n_pre cols M_low_level_spec ) ” 
  &&  “ (row_scale_prefix lcur n_pre cols M_low_level_spec zp_low_level_spec row_pre zinv_low_level_spec j ) ”
  &&  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z inv_pre zinv_low_level_spec )
  **  (mpz_array aug_pre (n_pre * cols ) lcur )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_row_scale_mod_gmp_safety_wit_1 : row_scale_mod_gmp_safety_wit_1.
Axiom proof_of_row_scale_mod_gmp_safety_wit_2 : row_scale_mod_gmp_safety_wit_2.
Axiom proof_of_row_scale_mod_gmp_safety_wit_3 : row_scale_mod_gmp_safety_wit_3.
Axiom proof_of_row_scale_mod_gmp_safety_wit_4 : row_scale_mod_gmp_safety_wit_4.
Axiom proof_of_row_scale_mod_gmp_safety_wit_5 : row_scale_mod_gmp_safety_wit_5.
Axiom proof_of_row_scale_mod_gmp_safety_wit_6 : row_scale_mod_gmp_safety_wit_6.
Axiom proof_of_row_scale_mod_gmp_safety_wit_7 : row_scale_mod_gmp_safety_wit_7.
Axiom proof_of_row_scale_mod_gmp_safety_wit_8 : row_scale_mod_gmp_safety_wit_8.
Axiom proof_of_row_scale_mod_gmp_entail_wit_1 : row_scale_mod_gmp_entail_wit_1.
Axiom proof_of_row_scale_mod_gmp_entail_wit_2 : row_scale_mod_gmp_entail_wit_2.
Axiom proof_of_row_scale_mod_gmp_return_wit_1 : row_scale_mod_gmp_return_wit_1.
Axiom proof_of_row_scale_mod_gmp_return_wit_2 : row_scale_mod_gmp_return_wit_2.
Axiom proof_of_row_scale_mod_gmp_partial_solve_wit_1 : row_scale_mod_gmp_partial_solve_wit_1.
Axiom proof_of_row_scale_mod_gmp_partial_solve_wit_2 : row_scale_mod_gmp_partial_solve_wit_2.
Axiom proof_of_row_scale_mod_gmp_partial_solve_wit_3 : row_scale_mod_gmp_partial_solve_wit_3.
Axiom proof_of_row_scale_mod_gmp_partial_solve_wit_4_pure : row_scale_mod_gmp_partial_solve_wit_4_pure.
Axiom proof_of_row_scale_mod_gmp_partial_solve_wit_4 : row_scale_mod_gmp_partial_solve_wit_4.
Axiom proof_of_row_scale_mod_gmp_partial_solve_wit_5 : row_scale_mod_gmp_partial_solve_wit_5.
Axiom proof_of_row_scale_mod_gmp_partial_solve_wit_6 : row_scale_mod_gmp_partial_solve_wit_6.
Axiom proof_of_row_scale_mod_gmp_partial_solve_wit_7 : row_scale_mod_gmp_partial_solve_wit_7.
Axiom proof_of_row_scale_mod_gmp_partial_solve_wit_8 : row_scale_mod_gmp_partial_solve_wit_8.

End VC_Correct.
