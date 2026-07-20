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
Local Open Scope sac.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_proof.

(*----- Function mpn_common_scan -----*)

Definition mpn_common_scan_safety_wit_1 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : ((Zlength (l_found)) = n_found)) (PreH2 : (n_found >= 0)) (PreH3 : (n_found <= INT_MAX)) (PreH4 : (list_within_bound UINT_MOD l_found )) (PreH5 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "limb" ) )) # UInt  |-> limb_pre)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_common_scan_safety_wit_2 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : ((Zlength (l_found)) = n_found)) (PreH2 : (n_found >= 0)) (PreH3 : (n_found <= INT_MAX)) (PreH4 : (list_within_bound UINT_MOD l_found )) (PreH5 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH6 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH7 : (i_pre < i)) (PreH8 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "limb" ) )) # UInt  |-> limb)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_common_scan_safety_wit_3 := 
(
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "limb" ) )) # UInt  |-> limb_pre)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ ((i_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i_pre + 1 )) ”
) \/
(
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "limb" ) )) # UInt  |-> limb_pre)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ ((i_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i_pre + 1 )) ”
).

Definition mpn_common_scan_safety_wit_3_split_goal_1 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "limb" ) )) # UInt  |-> limb_pre)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ ((i_pre + 1 ) <= INT_MAX) ”
.

Definition mpn_common_scan_safety_wit_3_split_goal_2 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "limb" ) )) # UInt  |-> limb_pre)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ ((INT_MIN) <= (i_pre + 1 )) ”
.

Definition mpn_common_scan_safety_wit_4 := 
(
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "limb" ) )) # UInt  |-> limb)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "limb" ) )) # UInt  |-> limb)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition mpn_common_scan_safety_wit_4_split_goal_1 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "limb" ) )) # UInt  |-> limb)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition mpn_common_scan_safety_wit_4_split_goal_2 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "limb" ) )) # UInt  |-> limb)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_common_scan_safety_wit_5 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (i = un_pre)) (PreH2 : (limb = 0)) (PreH3 : (i <> un_pre)) (PreH4 : (i_pre < i)) (PreH5 : (0 <= i)) (PreH6 : (i < n_found)) (PreH7 : ((Zlength (l_found)) = n_found)) (PreH8 : (n_found >= 0)) (PreH9 : (n_found <= INT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH12 : (mpn_common_scan_target l_found limb (i - 1 ) un_pre ux_pre pos_found )) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "limb" ) )) # UInt  |-> limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ False ”
.

Definition mpn_common_scan_safety_wit_6 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (odd: Z) (cnt: Z) (PreH1 : (0 <= cnt)) (PreH2 : (cnt < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (limb_pre = (odd * (Z.pow (2) (cnt)) ))) (PreH6 : ((Zlength (l_found)) = n_found)) (PreH7 : (n_found >= 0)) (PreH8 : (n_found <= INT_MAX)) (PreH9 : (list_within_bound UINT_MOD l_found )) (PreH10 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt)
  **  ((( &( "limb" ) )) # UInt  |-> limb_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_common_scan_safety_wit_7 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (odd: Z) (cnt: Z) (limb: Z) (i: Z) (PreH1 : (0 <= cnt)) (PreH2 : (cnt < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (limb = (odd * (Z.pow (2) (cnt)) ))) (PreH6 : ((Zlength (l_found)) = n_found)) (PreH7 : (n_found >= 0)) (PreH8 : (n_found <= INT_MAX)) (PreH9 : (list_within_bound UINT_MOD l_found )) (PreH10 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH11 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH12 : (i_pre < i)) (PreH13 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt)
  **  ((( &( "limb" ) )) # UInt  |-> limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_common_scan_entail_wit_1 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (n_found >= 0)) (PreH2 : (n_found <= INT_MAX)) (PreH3 : ((Zlength (l_found)) = n_found)) (PreH4 : (list_within_bound UINT_MOD l_found )) (PreH5 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  (UIntArray.full up_pre n_found l_found )
|--
  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ”
  &&  (UIntArray.full up_pre n_found l_found )
.

Definition mpn_common_scan_entail_wit_2_1 := 
(
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  (UIntArray.full up_pre n_found l_found )
|--
  “ (limb_pre = 0) ” 
  &&  “ ((i_pre + 1 ) <> un_pre) ” 
  &&  “ (i_pre < (i_pre + 1 )) ” 
  &&  “ (0 <= (i_pre + 1 )) ” 
  &&  “ ((i_pre + 1 ) < n_found) ” 
  &&  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre ((i_pre + 1 ) - 1 ) un_pre ux_pre pos_found ) ”
  &&  (UIntArray.full up_pre n_found l_found )
) \/
(
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  TT && emp 
|--
  “ (mpn_common_scan_target l_found limb_pre ((i_pre + 1 ) - 1 ) un_pre ux_pre pos_found ) ” 
  &&  “ ((i_pre + 1 ) < n_found) ” 
  &&  “ (0 <= (i_pre + 1 )) ” 
  &&  “ ((i_pre + 1 ) <> un_pre) ”
  &&  emp
).

Definition mpn_common_scan_entail_wit_2_1_split_goal_1 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  (mpn_common_scan_target l_found limb_pre ((i_pre + 1 ) - 1 ) un_pre ux_pre pos_found )
.

Definition mpn_common_scan_entail_wit_2_1_split_goal_2 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  ((i_pre + 1 ) < n_found)
.

Definition mpn_common_scan_entail_wit_2_1_split_goal_3 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  (0 <= (i_pre + 1 ))
.

Definition mpn_common_scan_entail_wit_2_1_split_goal_4 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  ((i_pre + 1 ) <> un_pre)
.

Definition mpn_common_scan_entail_wit_2_2 := 
(
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  (UIntArray.full up_pre n_found l_found )
|--
  “ (limb = 0) ” 
  &&  “ ((i + 1 ) <> un_pre) ” 
  &&  “ (i_pre < (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_found) ” 
  &&  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb ((i + 1 ) - 1 ) un_pre ux_pre pos_found ) ”
  &&  (UIntArray.full up_pre n_found l_found )
) \/
(
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  TT && emp 
|--
  “ (mpn_common_scan_target l_found limb ((i + 1 ) - 1 ) un_pre ux_pre pos_found ) ” 
  &&  “ ((i + 1 ) < n_found) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <> un_pre) ”
  &&  emp
).

Definition mpn_common_scan_entail_wit_2_2_split_goal_1 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  (mpn_common_scan_target l_found limb ((i + 1 ) - 1 ) un_pre ux_pre pos_found )
.

Definition mpn_common_scan_entail_wit_2_2_split_goal_2 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  ((i + 1 ) < n_found)
.

Definition mpn_common_scan_entail_wit_2_2_split_goal_3 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  (0 <= (i + 1 ))
.

Definition mpn_common_scan_entail_wit_2_2_split_goal_4 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb = 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  ((i + 1 ) <> un_pre)
.

Definition mpn_common_scan_entail_wit_3 := 
(
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (i <> un_pre)) (PreH2 : (limb = 0)) (PreH3 : (i <> un_pre)) (PreH4 : (i_pre < i)) (PreH5 : (0 <= i)) (PreH6 : (i < n_found)) (PreH7 : ((Zlength (l_found)) = n_found)) (PreH8 : (n_found >= 0)) (PreH9 : (n_found <= INT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH12 : (mpn_common_scan_target l_found limb (i - 1 ) un_pre ux_pre pos_found )) ,
  (UIntArray.full up_pre n_found l_found )
|--
  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found (Z.lxor ux_pre (Znth i l_found 0)) i un_pre ux_pre pos_found ) ” 
  &&  “ (i_pre < i) ” 
  &&  “ ((Z.lxor ux_pre (Znth i l_found 0)) = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0))))) ”
  &&  (UIntArray.full up_pre n_found l_found )
) \/
(
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (i <> un_pre)) (PreH2 : (limb = 0)) (PreH3 : (i <> un_pre)) (PreH4 : (i_pre < i)) (PreH5 : (0 <= i)) (PreH6 : (i < n_found)) (PreH7 : ((Zlength (l_found)) = n_found)) (PreH8 : (n_found >= 0)) (PreH9 : (n_found <= INT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH12 : (mpn_common_scan_target l_found limb (i - 1 ) un_pre ux_pre pos_found )) ,
  TT && emp 
|--
  “ ((Z.lxor ux_pre (Znth i l_found 0)) = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0))))) ” 
  &&  “ (mpn_common_scan_target l_found (Z.lxor ux_pre (Znth i l_found 0)) i un_pre ux_pre pos_found ) ”
  &&  emp
).

Definition mpn_common_scan_entail_wit_3_split_goal_1 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (i <> un_pre)) (PreH2 : (limb = 0)) (PreH3 : (i <> un_pre)) (PreH4 : (i_pre < i)) (PreH5 : (0 <= i)) (PreH6 : (i < n_found)) (PreH7 : ((Zlength (l_found)) = n_found)) (PreH8 : (n_found >= 0)) (PreH9 : (n_found <= INT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH12 : (mpn_common_scan_target l_found limb (i - 1 ) un_pre ux_pre pos_found )) ,
  ((Z.lxor ux_pre (Znth i l_found 0)) = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))
.

Definition mpn_common_scan_entail_wit_3_split_goal_2 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (i <> un_pre)) (PreH2 : (limb = 0)) (PreH3 : (i <> un_pre)) (PreH4 : (i_pre < i)) (PreH5 : (0 <= i)) (PreH6 : (i < n_found)) (PreH7 : ((Zlength (l_found)) = n_found)) (PreH8 : (n_found >= 0)) (PreH9 : (n_found <= INT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH12 : (mpn_common_scan_target l_found limb (i - 1 ) un_pre ux_pre pos_found )) ,
  (mpn_common_scan_target l_found (Z.lxor ux_pre (Znth i l_found 0)) i un_pre ux_pre pos_found )
.

Definition mpn_common_scan_entail_wit_4 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (i_2: Z) (limb_2: Z) (PreH1 : ((Zlength (l_found)) = n_found)) (PreH2 : (n_found >= 0)) (PreH3 : (n_found <= INT_MAX)) (PreH4 : (list_within_bound UINT_MOD l_found )) (PreH5 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH6 : (mpn_common_scan_target l_found limb_2 i_2 un_pre ux_pre pos_found )) (PreH7 : (i_pre < i_2)) (PreH8 : (limb_2 = (gmp_scan_limb (ux_pre) ((Znth (i_2) (l_found) (0)))))) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "limb" ) )) # UInt  |-> limb_2)
  **  (UIntArray.full up_pre n_found l_found )
|--
  (“ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ”
  &&  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "limb" ) )) # UInt  |-> limb_pre)
  **  (UIntArray.full up_pre n_found l_found ))
  ||
  (EX (limb: Z)  (i: Z) ,
  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found ) ” 
  &&  “ (i_pre < i) ” 
  &&  “ (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0))))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "limb" ) )) # UInt  |-> limb)
  **  (UIntArray.full up_pre n_found l_found ))
.

Definition mpn_common_scan_entail_wit_5_1 := 
(
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (odd_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : (odd_2 > 0)) (PreH4 : ((odd_2 % ( 2 ) ) = 1)) (PreH5 : (limb_pre = (odd_2 * (Z.pow (2) (retval)) ))) (PreH6 : (limb_pre <> 0)) (PreH7 : ((Zlength (l_found)) = n_found)) (PreH8 : (n_found >= 0)) (PreH9 : (n_found <= INT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH12 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  (UIntArray.full up_pre n_found l_found )
|--
  EX (odd: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (limb_pre = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ”
  &&  (UIntArray.full up_pre n_found l_found )
) \/
(
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (odd_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : (odd_2 > 0)) (PreH4 : ((odd_2 % ( 2 ) ) = 1)) (PreH5 : (limb_pre = (odd_2 * (Z.pow (2) (retval)) ))) (PreH6 : (limb_pre <> 0)) (PreH7 : ((Zlength (l_found)) = n_found)) (PreH8 : (n_found >= 0)) (PreH9 : (n_found <= INT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH12 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  TT && emp 
|--
  EX (odd: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (limb_pre = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ”
  &&  emp
).

Definition mpn_common_scan_entail_wit_5_2 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb_2: Z) (i_2: Z) (odd_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : (odd_2 > 0)) (PreH4 : ((odd_2 % ( 2 ) ) = 1)) (PreH5 : (limb_2 = (odd_2 * (Z.pow (2) (retval)) ))) (PreH6 : (limb_2 <> 0)) (PreH7 : ((Zlength (l_found)) = n_found)) (PreH8 : (n_found >= 0)) (PreH9 : (n_found <= INT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH12 : (mpn_common_scan_target l_found limb_2 i_2 un_pre ux_pre pos_found )) (PreH13 : (i_pre < i_2)) (PreH14 : (limb_2 = (gmp_scan_limb (ux_pre) ((Znth (i_2) (l_found) (0)))))) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "limb" ) )) # UInt  |-> limb_2)
  **  (UIntArray.full up_pre n_found l_found )
|--
  (EX (odd: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (limb_pre = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ”
  &&  ((( &( "limb" ) )) # UInt  |-> limb_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  (UIntArray.full up_pre n_found l_found ))
  ||
  (EX (i: Z)  (limb: Z)  (odd: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (limb = (odd * (Z.pow (2) (retval)) )) ” 
  &&  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found ) ” 
  &&  “ (i_pre < i) ” 
  &&  “ (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0))))) ”
  &&  ((( &( "limb" ) )) # UInt  |-> limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full up_pre n_found l_found ))
.

Definition mpn_common_scan_return_wit_1 := 
(
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (odd: Z) (cnt: Z) (PreH1 : (0 <= cnt)) (PreH2 : (cnt < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (limb_pre = (odd * (Z.pow (2) (cnt)) ))) (PreH6 : ((Zlength (l_found)) = n_found)) (PreH7 : (n_found >= 0)) (PreH8 : (n_found <= INT_MAX)) (PreH9 : (list_within_bound UINT_MOD l_found )) (PreH10 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  (UIntArray.full up_pre n_found l_found )
|--
  “ (mpn_common_scan_result l_found limb_pre i_pre un_pre ux_pre pos_found (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (i_pre) (64)) * 32 )) (64)) + cnt )) (64)) ) ”
  &&  (UIntArray.full up_pre n_found l_found )
) \/
(
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (odd: Z) (cnt: Z) (PreH1 : (0 <= cnt)) (PreH2 : (cnt < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (limb_pre = (odd * (Z.pow (2) (cnt)) ))) (PreH6 : ((Zlength (l_found)) = n_found)) (PreH7 : (n_found >= 0)) (PreH8 : (n_found <= INT_MAX)) (PreH9 : (list_within_bound UINT_MOD l_found )) (PreH10 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  TT && emp 
|--
  “ (mpn_common_scan_result l_found limb_pre i_pre un_pre ux_pre pos_found (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (i_pre) (64)) * 32 )) (64)) + cnt )) (64)) ) ”
  &&  emp
).

Definition mpn_common_scan_return_wit_1_split_goal_1 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (odd: Z) (cnt: Z) (PreH1 : (0 <= cnt)) (PreH2 : (cnt < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (limb_pre = (odd * (Z.pow (2) (cnt)) ))) (PreH6 : ((Zlength (l_found)) = n_found)) (PreH7 : (n_found >= 0)) (PreH8 : (n_found <= INT_MAX)) (PreH9 : (list_within_bound UINT_MOD l_found )) (PreH10 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  (mpn_common_scan_result l_found limb_pre i_pre un_pre ux_pre pos_found (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (i_pre) (64)) * 32 )) (64)) + cnt )) (64)) )
.

Definition mpn_common_scan_return_wit_2 := 
(
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (odd: Z) (cnt: Z) (limb: Z) (i: Z) (PreH1 : (0 <= cnt)) (PreH2 : (cnt < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (limb = (odd * (Z.pow (2) (cnt)) ))) (PreH6 : ((Zlength (l_found)) = n_found)) (PreH7 : (n_found >= 0)) (PreH8 : (n_found <= INT_MAX)) (PreH9 : (list_within_bound UINT_MOD l_found )) (PreH10 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH11 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH12 : (i_pre < i)) (PreH13 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  (UIntArray.full up_pre n_found l_found )
|--
  “ (mpn_common_scan_result l_found limb_pre i_pre un_pre ux_pre pos_found (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (i) (64)) * 32 )) (64)) + cnt )) (64)) ) ”
  &&  (UIntArray.full up_pre n_found l_found )
) \/
(
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (odd: Z) (cnt: Z) (limb: Z) (i: Z) (PreH1 : (0 <= cnt)) (PreH2 : (cnt < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (limb = (odd * (Z.pow (2) (cnt)) ))) (PreH6 : ((Zlength (l_found)) = n_found)) (PreH7 : (n_found >= 0)) (PreH8 : (n_found <= INT_MAX)) (PreH9 : (list_within_bound UINT_MOD l_found )) (PreH10 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH11 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH12 : (i_pre < i)) (PreH13 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  TT && emp 
|--
  “ (mpn_common_scan_result l_found limb_pre i_pre un_pre ux_pre pos_found (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (i) (64)) * 32 )) (64)) + cnt )) (64)) ) ”
  &&  emp
).

Definition mpn_common_scan_return_wit_2_split_goal_1 := 
forall (ux_pre: Z) (un_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (odd: Z) (cnt: Z) (limb: Z) (i: Z) (PreH1 : (0 <= cnt)) (PreH2 : (cnt < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (limb = (odd * (Z.pow (2) (cnt)) ))) (PreH6 : ((Zlength (l_found)) = n_found)) (PreH7 : (n_found >= 0)) (PreH8 : (n_found <= INT_MAX)) (PreH9 : (list_within_bound UINT_MOD l_found )) (PreH10 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH11 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH12 : (i_pre < i)) (PreH13 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  (mpn_common_scan_result l_found limb_pre i_pre un_pre ux_pre pos_found (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (i) (64)) * 32 )) (64)) + cnt )) (64)) )
.

Definition mpn_common_scan_partial_solve_wit_1 := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (i <> un_pre)) (PreH2 : (limb = 0)) (PreH3 : (i <> un_pre)) (PreH4 : (i_pre < i)) (PreH5 : (0 <= i)) (PreH6 : (i < n_found)) (PreH7 : ((Zlength (l_found)) = n_found)) (PreH8 : (n_found >= 0)) (PreH9 : (n_found <= INT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_found )) (PreH11 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH12 : (mpn_common_scan_target l_found limb (i - 1 ) un_pre ux_pre pos_found )) ,
  (UIntArray.full up_pre n_found l_found )
|--
  “ (i <> un_pre) ” 
  &&  “ (limb = 0) ” 
  &&  “ (i <> un_pre) ” 
  &&  “ (i_pre < i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_found) ” 
  &&  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb (i - 1 ) un_pre ux_pre pos_found ) ”
  &&  (((up_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_found 0))
  **  (UIntArray.missing_i up_pre i 0 n_found l_found )
.

Definition mpn_common_scan_partial_solve_wit_2_pure := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre <> 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "limb" ) )) # UInt  |-> limb_pre)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ (limb_pre <= UINT_MAX) ” 
  &&  “ (0 < limb_pre) ”
.

Definition mpn_common_scan_partial_solve_wit_2_aux := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (PreH1 : (limb_pre <> 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) ,
  (UIntArray.full up_pre n_found l_found )
|--
  “ (limb_pre <= UINT_MAX) ” 
  &&  “ (0 < limb_pre) ” 
  &&  “ (limb_pre <> 0) ” 
  &&  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ”
  &&  (UIntArray.full up_pre n_found l_found )
.

Definition mpn_common_scan_partial_solve_wit_2 := mpn_common_scan_partial_solve_wit_2_pure -> mpn_common_scan_partial_solve_wit_2_aux.

Definition mpn_common_scan_partial_solve_wit_3_pure := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb <> 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "ux" ) )) # UInt  |-> ux_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "limb" ) )) # UInt  |-> limb)
  **  ((( &( "cnt" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_found l_found )
|--
  “ (limb <= UINT_MAX) ” 
  &&  “ (0 < limb) ”
.

Definition mpn_common_scan_partial_solve_wit_3_aux := 
forall (ux_pre: Z) (un_pre: Z) (up_pre: Z) (i_pre: Z) (limb_pre: Z) (pos_found: Z) (n_found: Z) (l_found: (@list Z)) (limb: Z) (i: Z) (PreH1 : (limb <> 0)) (PreH2 : ((Zlength (l_found)) = n_found)) (PreH3 : (n_found >= 0)) (PreH4 : (n_found <= INT_MAX)) (PreH5 : (list_within_bound UINT_MOD l_found )) (PreH6 : (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found )) (PreH7 : (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found )) (PreH8 : (i_pre < i)) (PreH9 : (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0)))))) ,
  (UIntArray.full up_pre n_found l_found )
|--
  “ (limb <= UINT_MAX) ” 
  &&  “ (0 < limb) ” 
  &&  “ (limb <> 0) ” 
  &&  “ ((Zlength (l_found)) = n_found) ” 
  &&  “ (n_found >= 0) ” 
  &&  “ (n_found <= INT_MAX) ” 
  &&  “ (list_within_bound UINT_MOD l_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb_pre i_pre un_pre ux_pre pos_found ) ” 
  &&  “ (mpn_common_scan_target l_found limb i un_pre ux_pre pos_found ) ” 
  &&  “ (i_pre < i) ” 
  &&  “ (limb = (gmp_scan_limb (ux_pre) ((Znth (i) (l_found) (0))))) ”
  &&  (UIntArray.full up_pre n_found l_found )
.

Definition mpn_common_scan_partial_solve_wit_3 := mpn_common_scan_partial_solve_wit_3_pure -> mpn_common_scan_partial_solve_wit_3_aux.

(*----- Function mpn_scan1 -----*)

Definition mpn_scan1_safety_wit_1 := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : (n > 0)) (PreH2 : (n <= INT_MAX)) (PreH3 : (bit_pre >= 0)) (PreH4 : ((bit_pre ÷ 32 ) < n)) (PreH5 : ((Zlength (l)) = n)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : (mpn_scan1_target l bit_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  (UIntArray.full ptr_pre n l )
|--
  “ (32 <> 0) ”
.

Definition mpn_scan1_safety_wit_2 := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : (n > 0)) (PreH2 : (n <= INT_MAX)) (PreH3 : (bit_pre >= 0)) (PreH4 : ((bit_pre ÷ 32 ) < n)) (PreH5 : ((Zlength (l)) = n)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : (mpn_scan1_target l bit_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  (UIntArray.full ptr_pre n l )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_scan1_safety_wit_3 := 
(
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((bit_pre % ( 32 ) ) <= 31) ” 
  &&  “ (0 <= (bit_pre % ( 32 ) )) ”
) \/
(
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((bit_pre % ( 32 ) ) <= 31) ” 
  &&  “ (0 <= (bit_pre % ( 32 ) )) ”
).

Definition mpn_scan1_safety_wit_3_split_goal_1 := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((bit_pre % ( 32 ) ) <= 31) ”
.

Definition mpn_scan1_safety_wit_3_split_goal_2 := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= (bit_pre % ( 32 ) )) ”
.

Definition mpn_scan1_safety_wit_4 := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (32 <> 0) ”
.

Definition mpn_scan1_safety_wit_5 := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (4294967295 <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= 4294967295) ”
.

Definition mpn_scan1_safety_wit_6 := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_scan1_safety_wit_7 := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_scan1_entail_wit_1 := 
(
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : (n > 0)) (PreH2 : (n <= INT_MAX)) (PreH3 : (bit_pre >= 0)) (PreH4 : ((bit_pre ÷ 32 ) < n)) (PreH5 : ((Zlength (l)) = n)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : (mpn_scan1_target l bit_pre )) ,
  (UIntArray.full ptr_pre n l )
|--
  EX (pos: Z) ,
  “ ((signed_last_nbits ((bit_pre ÷ 32 )) (32)) = (bit_pre ÷ 32 )) ” 
  &&  “ (0 <= (signed_last_nbits ((bit_pre ÷ 32 )) (32))) ” 
  &&  “ ((signed_last_nbits ((bit_pre ÷ 32 )) (32)) < n) ” 
  &&  “ (n > 0) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (bit_pre >= 0) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (mpn_common_scan_target l (Z.land (Znth ((signed_last_nbits ((bit_pre ÷ 32 )) (32))) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) (signed_last_nbits ((bit_pre ÷ 32 )) (32)) (signed_last_nbits ((bit_pre ÷ 32 )) (32)) 0 pos ) ”
  &&  (UIntArray.full ptr_pre n l )
) \/
(
forall (bit_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : (n > 0)) (PreH2 : (n <= INT_MAX)) (PreH3 : (bit_pre >= 0)) (PreH4 : ((bit_pre ÷ 32 ) < n)) (PreH5 : ((Zlength (l)) = n)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : (mpn_scan1_target l bit_pre )) ,
  TT && emp 
|--
  EX (pos: Z) ,
  “ ((signed_last_nbits ((bit_pre ÷ 32 )) (32)) = (bit_pre ÷ 32 )) ” 
  &&  “ (0 <= (signed_last_nbits ((bit_pre ÷ 32 )) (32))) ” 
  &&  “ ((signed_last_nbits ((bit_pre ÷ 32 )) (32)) < n) ” 
  &&  “ (n > 0) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (bit_pre >= 0) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (mpn_common_scan_target l (Z.land (Znth ((signed_last_nbits ((bit_pre ÷ 32 )) (32))) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) (signed_last_nbits ((bit_pre ÷ 32 )) (32)) (signed_last_nbits ((bit_pre ÷ 32 )) (32)) 0 pos ) ”
  &&  emp
).

Definition mpn_scan1_return_wit_1 := 
(
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (retval: Z) (PreH1 : (mpn_common_scan_result l (Z.land (Znth i l 0) (unsigned_last_nbits ((Z.shiftl 4294967295 (bit_pre % ( 32 ) ))) (32))) i i 0 pos retval )) (PreH2 : (i = (bit_pre ÷ 32 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n > 0)) (PreH6 : (n <= INT_MAX)) (PreH7 : (bit_pre >= 0)) (PreH8 : ((Zlength (l)) = n)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
|--
  “ (mpn_scan1_result l bit_pre retval ) ”
  &&  (UIntArray.full ptr_pre n l )
) \/
(
forall (bit_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (retval: Z) (PreH1 : (mpn_common_scan_result l (Z.land (Znth i l 0) (unsigned_last_nbits ((Z.shiftl 4294967295 (bit_pre % ( 32 ) ))) (32))) i i 0 pos retval )) (PreH2 : (i = (bit_pre ÷ 32 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n > 0)) (PreH6 : (n <= INT_MAX)) (PreH7 : (bit_pre >= 0)) (PreH8 : ((Zlength (l)) = n)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  TT && emp 
|--
  “ (mpn_scan1_result l bit_pre retval ) ”
  &&  emp
).

Definition mpn_scan1_return_wit_1_split_goal_1 := 
forall (bit_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (retval: Z) (PreH1 : (mpn_common_scan_result l (Z.land (Znth i l 0) (unsigned_last_nbits ((Z.shiftl 4294967295 (bit_pre % ( 32 ) ))) (32))) i i 0 pos retval )) (PreH2 : (i = (bit_pre ÷ 32 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n > 0)) (PreH6 : (n <= INT_MAX)) (PreH7 : (bit_pre >= 0)) (PreH8 : ((Zlength (l)) = n)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (mpn_scan1_result l bit_pre retval )
.

Definition mpn_scan1_partial_solve_wit_1 := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
|--
  “ (i = (bit_pre ÷ 32 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n > 0) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (bit_pre >= 0) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos ) ”
  &&  (((ptr_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i ptr_pre i 0 n l )
.

Definition mpn_scan1_partial_solve_wit_2_pure := 
(
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (n >= 0) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (mpn_common_scan_target l (Z.land (Znth i l 0) (unsigned_last_nbits ((Z.shiftl 4294967295 (bit_pre % ( 32 ) ))) (32))) i i 0 pos ) ”
) \/
(
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (i = (bit_pre ÷ 32 ))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n > 0)) (PreH7 : (n <= INT_MAX)) (PreH8 : (bit_pre >= 0)) (PreH9 : ((Zlength (l)) = n)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (mpn_common_scan_target l (Z.land (Znth i l 0) (unsigned_last_nbits ((Z.shiftl 4294967295 (bit_pre % ( 32 ) ))) (32))) i i 0 pos ) ”
).

Definition mpn_scan1_partial_solve_wit_2_pure_split_goal_1 := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (i = (bit_pre ÷ 32 ))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n > 0)) (PreH7 : (n <= INT_MAX)) (PreH8 : (bit_pre >= 0)) (PreH9 : ((Zlength (l)) = n)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((( &( "bit" ) )) # UInt64  |-> bit_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (mpn_common_scan_target l (Z.land (Znth i l 0) (unsigned_last_nbits ((Z.shiftl 4294967295 (bit_pre % ( 32 ) ))) (32))) i i 0 pos ) ”
.

Definition mpn_scan1_partial_solve_wit_2_aux := 
forall (bit_pre: Z) (ptr_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (pos: Z) (PreH1 : (i = (bit_pre ÷ 32 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n > 0)) (PreH5 : (n <= INT_MAX)) (PreH6 : (bit_pre >= 0)) (PreH7 : ((Zlength (l)) = n)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos )) ,
  (UIntArray.full ptr_pre n l )
|--
  “ (n >= 0) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (mpn_common_scan_target l (Z.land (Znth i l 0) (unsigned_last_nbits ((Z.shiftl 4294967295 (bit_pre % ( 32 ) ))) (32))) i i 0 pos ) ” 
  &&  “ (i = (bit_pre ÷ 32 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n > 0) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (bit_pre >= 0) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (mpn_common_scan_target l (Z.land (Znth (i) (l) (0)) (unsigned_last_nbits ((4294967295 * (Z.pow (2) ((bit_pre % ( 32 ) ))) )) (32))) i i 0 pos ) ”
  &&  (UIntArray.full ptr_pre n l )
.

Definition mpn_scan1_partial_solve_wit_2 := mpn_scan1_partial_solve_wit_2_pure -> mpn_scan1_partial_solve_wit_2_aux.

(*----- Function mpz_make_odd -----*)

Definition mpz_make_odd_safety_wit_1 := 
forall (r_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (l: (@list Z)) (PreH1 : (z > 0)) (PreH2 : (size > 0)) (PreH3 : (size <= cap)) (PreH4 : (cap >= 0)) (PreH5 : ((Zlength (l)) = size)) (PreH6 : ((list_to_Z (UINT_MOD) (l)) = z)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((last (l) (1)) >= 1)) (PreH9 : (same_sign z size )) (PreH10 : (mpn_scan1_target l 0 )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((( &( "shift" ) )) # UInt64  |->_)
  **  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_make_odd_entail_wit_1 := 
(
forall (r_pre: Z) (z: Z) (PreH1 : (z > 0)) ,
  (store_Z r_pre z )
|--
  EX (ptr: Z)  (l: (@list Z))  (cap: Z)  (size: Z) ,
  “ (z > 0) ” 
  &&  “ (size > 0) ” 
  &&  “ (size <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ ((Zlength (l)) = size) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = z) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (same_sign z size ) ” 
  &&  “ (mpn_scan1_target l 0 ) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
) \/
(
forall (z: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign z size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (z > 0)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (z)) (Zabs (size_2)) )
|--
  EX (l: (@list Z)) ,
  “ (size_2 = (Zlength (l))) ” 
  &&  “ (z > 0) ” 
  &&  “ ((Zlength (l)) > 0) ” 
  &&  “ ((Zlength (l)) <= cap_2) ” 
  &&  “ (cap_2 >= 0) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = z) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (same_sign z (Zlength (l)) ) ” 
  &&  “ (mpn_scan1_target l 0 ) ”
  &&  (UIntArray.full ptr_2 (Zlength (l)) l )
  **  (UIntArray.undef_seg ptr_2 (Zlength (l)) cap_2 )
).

Definition mpz_make_odd_entail_wit_2 := 
(
forall (r_pre: Z) (z: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (l_2: (@list Z)) (retval: Z) (PreH1 : (mpn_scan1_result l_2 0 retval )) (PreH2 : (z > 0)) (PreH3 : (size_2 > 0)) (PreH4 : (size_2 <= cap_2)) (PreH5 : (cap_2 >= 0)) (PreH6 : ((Zlength (l_2)) = size_2)) (PreH7 : ((list_to_Z (UINT_MOD) (l_2)) = z)) (PreH8 : (list_within_bound UINT_MOD l_2 )) (PreH9 : ((last (l_2) (1)) >= 1)) (PreH10 : (same_sign z size_2 )) (PreH11 : (mpn_scan1_target l_2 0 )) ,
  (UIntArray.full ptr_2 size_2 l_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  (UIntArray.undef_seg ptr_2 size_2 cap_2 )
|--
  EX (ptr: Z)  (l: (@list Z))  (cap: Z)  (size: Z) ,
  “ (z > 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (size > 0) ” 
  &&  “ (size <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ ((Zlength (l)) = size) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = z) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (same_sign z size ) ” 
  &&  “ (mpn_scan1_result l 0 retval ) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
) \/
(
forall (z: Z) (size_2: Z) (cap_2: Z) (l_2: (@list Z)) (retval: Z) (PreH1 : (mpn_scan1_result l_2 0 retval )) (PreH2 : (z > 0)) (PreH3 : (size_2 > 0)) (PreH4 : (size_2 <= cap_2)) (PreH5 : (cap_2 >= 0)) (PreH6 : ((Zlength (l_2)) = size_2)) (PreH7 : ((list_to_Z (UINT_MOD) (l_2)) = z)) (PreH8 : (list_within_bound UINT_MOD l_2 )) (PreH9 : ((last (l_2) (1)) >= 1)) (PreH10 : (same_sign z size_2 )) (PreH11 : (mpn_scan1_target l_2 0 )) ,
  TT && emp 
|--
  “ (retval >= 0) ”
  &&  emp
).

Definition mpz_make_odd_entail_wit_2_split_goal_1 := 
forall (z: Z) (size_2: Z) (cap_2: Z) (l_2: (@list Z)) (retval: Z) (PreH1 : (mpn_scan1_result l_2 0 retval )) (PreH2 : (z > 0)) (PreH3 : (size_2 > 0)) (PreH4 : (size_2 <= cap_2)) (PreH5 : (cap_2 >= 0)) (PreH6 : ((Zlength (l_2)) = size_2)) (PreH7 : ((list_to_Z (UINT_MOD) (l_2)) = z)) (PreH8 : (list_within_bound UINT_MOD l_2 )) (PreH9 : ((last (l_2) (1)) >= 1)) (PreH10 : (same_sign z size_2 )) (PreH11 : (mpn_scan1_target l_2 0 )) ,
  (retval >= 0)
.

Definition mpz_make_odd_entail_wit_3 := 
(
forall (r_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (l: (@list Z)) (shift: Z) (PreH1 : (z > 0)) (PreH2 : (shift >= 0)) (PreH3 : (size > 0)) (PreH4 : (size <= cap)) (PreH5 : (cap >= 0)) (PreH6 : ((Zlength (l)) = size)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = z)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((last (l) (1)) >= 1)) (PreH10 : (same_sign z size )) (PreH11 : (mpn_scan1_result l 0 shift )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
|--
  EX (odd: Z) ,
  “ (odd = (Z.quot (z) ((Z.pow (2) (shift))))) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (z = (odd * (Z.pow (2) (shift)) )) ”
  &&  (store_Z r_pre z )
) \/
(
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (l: (@list Z)) (shift: Z) (PreH1 : (z > 0)) (PreH2 : (shift >= 0)) (PreH3 : (size > 0)) (PreH4 : (size <= cap)) (PreH5 : (cap >= 0)) (PreH6 : ((Zlength (l)) = size)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = z)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((last (l) (1)) >= 1)) (PreH10 : (same_sign z size )) (PreH11 : (mpn_scan1_result l 0 shift )) ,
  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
|--
  “ (z = ((Z.quot (z) ((Z.pow (2) (shift)))) * (Z.pow (2) (shift)) )) ” 
  &&  “ (((Z.quot (z) ((Z.pow (2) (shift)))) % ( 2 ) ) = 1) ” 
  &&  “ ((Z.quot (z) ((Z.pow (2) (shift)))) > 0) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z)) (Zabs (size)) )
).

Definition mpz_make_odd_entail_wit_3_split_goal_1 := 
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (l: (@list Z)) (shift: Z) (PreH1 : (z > 0)) (PreH2 : (shift >= 0)) (PreH3 : (size > 0)) (PreH4 : (size <= cap)) (PreH5 : (cap >= 0)) (PreH6 : ((Zlength (l)) = size)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = z)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((last (l) (1)) >= 1)) (PreH10 : (same_sign z size )) (PreH11 : (mpn_scan1_result l 0 shift )) ,
  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
|--
  “ (z = ((Z.quot (z) ((Z.pow (2) (shift)))) * (Z.pow (2) (shift)) )) ”
.

Definition mpz_make_odd_entail_wit_3_split_goal_2 := 
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (l: (@list Z)) (shift: Z) (PreH1 : (z > 0)) (PreH2 : (shift >= 0)) (PreH3 : (size > 0)) (PreH4 : (size <= cap)) (PreH5 : (cap >= 0)) (PreH6 : ((Zlength (l)) = size)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = z)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((last (l) (1)) >= 1)) (PreH10 : (same_sign z size )) (PreH11 : (mpn_scan1_result l 0 shift )) ,
  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
|--
  “ (((Z.quot (z) ((Z.pow (2) (shift)))) % ( 2 ) ) = 1) ”
.

Definition mpz_make_odd_entail_wit_3_split_goal_3 := 
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (l: (@list Z)) (shift: Z) (PreH1 : (z > 0)) (PreH2 : (shift >= 0)) (PreH3 : (size > 0)) (PreH4 : (size <= cap)) (PreH5 : (cap >= 0)) (PreH6 : ((Zlength (l)) = size)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = z)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((last (l) (1)) >= 1)) (PreH10 : (same_sign z size )) (PreH11 : (mpn_scan1_result l 0 shift )) ,
  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
|--
  “ ((Z.quot (z) ((Z.pow (2) (shift)))) > 0) ”
.

Definition mpz_make_odd_entail_wit_3_split_goal_4 := 
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (l: (@list Z)) (shift: Z) (PreH1 : (z > 0)) (PreH2 : (shift >= 0)) (PreH3 : (size > 0)) (PreH4 : (size <= cap)) (PreH5 : (cap >= 0)) (PreH6 : ((Zlength (l)) = size)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = z)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((last (l) (1)) >= 1)) (PreH10 : (same_sign z size )) (PreH11 : (mpn_scan1_result l 0 shift )) ,
  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
|--
  “ ((Zabs (size)) <= cap) ”
.

Definition mpz_make_odd_entail_wit_3_split_goal_spatial := 
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (l: (@list Z)) (shift: Z) (PreH1 : (z > 0)) (PreH2 : (shift >= 0)) (PreH3 : (size > 0)) (PreH4 : (size <= cap)) (PreH5 : (cap >= 0)) (PreH6 : ((Zlength (l)) = size)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = z)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((last (l) (1)) >= 1)) (PreH10 : (same_sign z size )) (PreH11 : (mpn_scan1_result l 0 shift )) ,
  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
|--
  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z)) (Zabs (size)) )
.

Definition mpz_make_odd_entail_wit_4 := 
forall (r_pre: Z) (z: Z) (shift: Z) (odd: Z) (PreH1 : (r_pre = r_pre)) (PreH2 : (odd = (Z.quot (z) ((Z.pow (2) (shift)))))) (PreH3 : (0 <= shift)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : (z = (odd * (Z.pow (2) (shift)) ))) ,
  (store_Z r_pre (Z.quot (z) ((Z.pow (2) (shift)))) )
|--
  “ (odd = (Z.quot (z) ((Z.pow (2) (shift))))) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (z = (odd * (Z.pow (2) (shift)) )) ”
  &&  (store_Z r_pre odd )
.

Definition mpz_make_odd_return_wit_1 := 
forall (r_pre: Z) (z: Z) (odd_2: Z) (shift: Z) (PreH1 : (odd_2 = (Z.quot (z) ((Z.pow (2) (shift)))))) (PreH2 : (0 <= shift)) (PreH3 : (odd_2 > 0)) (PreH4 : ((odd_2 % ( 2 ) ) = 1)) (PreH5 : (z = (odd_2 * (Z.pow (2) (shift)) ))) ,
  (store_Z r_pre odd_2 )
|--
  EX (odd: Z) ,
  “ (0 <= shift) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (z = (odd * (Z.pow (2) (shift)) )) ”
  &&  (store_Z r_pre odd )
.

Definition mpz_make_odd_partial_solve_wit_1_pure := 
forall (r_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (l: (@list Z)) (PreH1 : (z > 0)) (PreH2 : (size > 0)) (PreH3 : (size <= cap)) (PreH4 : (cap >= 0)) (PreH5 : ((Zlength (l)) = size)) (PreH6 : ((list_to_Z (UINT_MOD) (l)) = z)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((last (l) (1)) >= 1)) (PreH9 : (same_sign z size )) (PreH10 : (mpn_scan1_target l 0 )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((( &( "shift" ) )) # UInt64  |->_)
  **  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
|--
  “ (size > 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ ((0 ÷ 32 ) < size) ” 
  &&  “ ((Zlength (l)) = size) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (mpn_scan1_target l 0 ) ” 
  &&  “ (size <= INT_MAX) ”
.

Definition mpz_make_odd_partial_solve_wit_1_aux := 
forall (r_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (l: (@list Z)) (PreH1 : (z > 0)) (PreH2 : (size > 0)) (PreH3 : (size <= cap)) (PreH4 : (cap >= 0)) (PreH5 : ((Zlength (l)) = size)) (PreH6 : ((list_to_Z (UINT_MOD) (l)) = z)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((last (l) (1)) >= 1)) (PreH9 : (same_sign z size )) (PreH10 : (mpn_scan1_target l 0 )) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.full ptr size l )
  **  (UIntArray.undef_seg ptr size cap )
|--
  “ (size > 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ ((0 ÷ 32 ) < size) ” 
  &&  “ ((Zlength (l)) = size) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (mpn_scan1_target l 0 ) ” 
  &&  “ (size <= INT_MAX) ” 
  &&  “ (z > 0) ” 
  &&  “ (size > 0) ” 
  &&  “ (size <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ ((Zlength (l)) = size) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = z) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (same_sign z size ) ” 
  &&  “ (mpn_scan1_target l 0 ) ”
  &&  (UIntArray.full ptr size l )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr size cap )
.

Definition mpz_make_odd_partial_solve_wit_1 := mpz_make_odd_partial_solve_wit_1_pure -> mpz_make_odd_partial_solve_wit_1_aux.

Definition mpz_make_odd_partial_solve_wit_2_pure := 
(
forall (r_pre: Z) (z: Z) (shift: Z) (odd: Z) (PreH1 : (odd = (Z.quot (z) ((Z.pow (2) (shift)))))) (PreH2 : (0 <= shift)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (z = (odd * (Z.pow (2) (shift)) ))) ,
  ((( &( "shift" ) )) # UInt64  |-> shift)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre z )
|--
  “ (r_pre = r_pre) ” 
  &&  “ (shift >= 0) ” 
  &&  “ ((shift ÷ 32 ) <= INT_MAX) ”
) \/
(
forall (r_pre: Z) (z: Z) (shift: Z) (odd: Z) (PreH1 : (odd = (Z.quot (z) ((Z.pow (2) (shift)))))) (PreH2 : (0 <= shift)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (z = (odd * (Z.pow (2) (shift)) ))) ,
  ((( &( "shift" ) )) # UInt64  |-> shift)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre z )
|--
  “ ((shift ÷ 32 ) <= INT_MAX) ”
).

Definition mpz_make_odd_partial_solve_wit_2_pure_split_goal_1 := 
forall (r_pre: Z) (z: Z) (shift: Z) (odd: Z) (PreH1 : (odd = (Z.quot (z) ((Z.pow (2) (shift)))))) (PreH2 : (0 <= shift)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (z = (odd * (Z.pow (2) (shift)) ))) ,
  ((( &( "shift" ) )) # UInt64  |-> shift)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre z )
|--
  “ ((shift ÷ 32 ) <= INT_MAX) ”
.

Definition mpz_make_odd_partial_solve_wit_2_aux := 
forall (r_pre: Z) (z: Z) (shift: Z) (odd: Z) (PreH1 : (odd = (Z.quot (z) ((Z.pow (2) (shift)))))) (PreH2 : (0 <= shift)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : (z = (odd * (Z.pow (2) (shift)) ))) ,
  (store_Z r_pre z )
|--
  “ (r_pre = r_pre) ” 
  &&  “ (shift >= 0) ” 
  &&  “ ((shift ÷ 32 ) <= INT_MAX) ” 
  &&  “ (odd = (Z.quot (z) ((Z.pow (2) (shift))))) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (z = (odd * (Z.pow (2) (shift)) )) ”
  &&  (store_Z r_pre z )
.

Definition mpz_make_odd_partial_solve_wit_2 := mpz_make_odd_partial_solve_wit_2_pure -> mpz_make_odd_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_common_scan_safety_wit_1 : mpn_common_scan_safety_wit_1.
Axiom proof_of_mpn_common_scan_safety_wit_2 : mpn_common_scan_safety_wit_2.
Axiom proof_of_mpn_common_scan_safety_wit_3 : mpn_common_scan_safety_wit_3.
Axiom proof_of_mpn_common_scan_safety_wit_4 : mpn_common_scan_safety_wit_4.
Axiom proof_of_mpn_common_scan_safety_wit_5 : mpn_common_scan_safety_wit_5.
Axiom proof_of_mpn_common_scan_safety_wit_6 : mpn_common_scan_safety_wit_6.
Axiom proof_of_mpn_common_scan_safety_wit_7 : mpn_common_scan_safety_wit_7.
Axiom proof_of_mpn_common_scan_entail_wit_1 : mpn_common_scan_entail_wit_1.
Axiom proof_of_mpn_common_scan_entail_wit_2_1 : mpn_common_scan_entail_wit_2_1.
Axiom proof_of_mpn_common_scan_entail_wit_2_2 : mpn_common_scan_entail_wit_2_2.
Axiom proof_of_mpn_common_scan_entail_wit_3 : mpn_common_scan_entail_wit_3.
Axiom proof_of_mpn_common_scan_entail_wit_4 : mpn_common_scan_entail_wit_4.
Axiom proof_of_mpn_common_scan_entail_wit_5_1 : mpn_common_scan_entail_wit_5_1.
Axiom proof_of_mpn_common_scan_entail_wit_5_2 : mpn_common_scan_entail_wit_5_2.
Axiom proof_of_mpn_common_scan_return_wit_1 : mpn_common_scan_return_wit_1.
Axiom proof_of_mpn_common_scan_return_wit_2 : mpn_common_scan_return_wit_2.
Axiom proof_of_mpn_common_scan_partial_solve_wit_1 : mpn_common_scan_partial_solve_wit_1.
Axiom proof_of_mpn_common_scan_partial_solve_wit_2_pure : mpn_common_scan_partial_solve_wit_2_pure.
Axiom proof_of_mpn_common_scan_partial_solve_wit_2 : mpn_common_scan_partial_solve_wit_2.
Axiom proof_of_mpn_common_scan_partial_solve_wit_3_pure : mpn_common_scan_partial_solve_wit_3_pure.
Axiom proof_of_mpn_common_scan_partial_solve_wit_3 : mpn_common_scan_partial_solve_wit_3.
Axiom proof_of_mpn_scan1_safety_wit_1 : mpn_scan1_safety_wit_1.
Axiom proof_of_mpn_scan1_safety_wit_2 : mpn_scan1_safety_wit_2.
Axiom proof_of_mpn_scan1_safety_wit_3 : mpn_scan1_safety_wit_3.
Axiom proof_of_mpn_scan1_safety_wit_4 : mpn_scan1_safety_wit_4.
Axiom proof_of_mpn_scan1_safety_wit_5 : mpn_scan1_safety_wit_5.
Axiom proof_of_mpn_scan1_safety_wit_6 : mpn_scan1_safety_wit_6.
Axiom proof_of_mpn_scan1_safety_wit_7 : mpn_scan1_safety_wit_7.
Axiom proof_of_mpn_scan1_entail_wit_1 : mpn_scan1_entail_wit_1.
Axiom proof_of_mpn_scan1_return_wit_1 : mpn_scan1_return_wit_1.
Axiom proof_of_mpn_scan1_partial_solve_wit_1 : mpn_scan1_partial_solve_wit_1.
Axiom proof_of_mpn_scan1_partial_solve_wit_2_pure : mpn_scan1_partial_solve_wit_2_pure.
Axiom proof_of_mpn_scan1_partial_solve_wit_2 : mpn_scan1_partial_solve_wit_2.
Axiom proof_of_mpz_make_odd_safety_wit_1 : mpz_make_odd_safety_wit_1.
Axiom proof_of_mpz_make_odd_entail_wit_1 : mpz_make_odd_entail_wit_1.
Axiom proof_of_mpz_make_odd_entail_wit_2 : mpz_make_odd_entail_wit_2.
Axiom proof_of_mpz_make_odd_entail_wit_3 : mpz_make_odd_entail_wit_3.
Axiom proof_of_mpz_make_odd_entail_wit_4 : mpz_make_odd_entail_wit_4.
Axiom proof_of_mpz_make_odd_return_wit_1 : mpz_make_odd_return_wit_1.
Axiom proof_of_mpz_make_odd_partial_solve_wit_1_pure : mpz_make_odd_partial_solve_wit_1_pure.
Axiom proof_of_mpz_make_odd_partial_solve_wit_1 : mpz_make_odd_partial_solve_wit_1.
Axiom proof_of_mpz_make_odd_partial_solve_wit_2_pure : mpz_make_odd_partial_solve_wit_2_pure.
Axiom proof_of_mpz_make_odd_partial_solve_wit_2 : mpz_make_odd_partial_solve_wit_2.

End VC_Correct.
