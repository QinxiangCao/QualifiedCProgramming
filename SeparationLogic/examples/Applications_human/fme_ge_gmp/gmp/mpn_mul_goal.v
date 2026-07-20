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

(*----- Function mpn_mul -----*)

Definition mpn_mul_safety_wit_1 := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH5 : ((Zlength (l_src)) = un_pre)) (PreH6 : ((Zlength (l_vp)) = vn_pre)) (PreH7 : (list_within_bound UINT_MOD l_src )) (PreH8 : (list_within_bound UINT_MOD l_vp )) (PreH9 : (0 <= (Znth 0 l_vp 0))) (PreH10 : ((Znth 0 l_vp 0) <= UINT_MAX)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "vp" ) )) # Ptr  |-> vp_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "vn" ) )) # Int  |-> vn_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "vl" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "rp_i" ) )) # Ptr  |->_)
  **  (UIntArray.undef_full rp_pre un_pre )
  **  (UIntArray.undef_seg rp_pre un_pre (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_mul_safety_wit_2 := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (val': Z) (l': (@list Z)) (retval: Z) (PreH1 : ((Zlength (l')) = un_pre)) (PreH2 : (list_within_bound UINT_MOD l' )) (PreH3 : ((list_to_Z (UINT_MOD) (l')) = val')) (PreH4 : ((val' + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_src)) * (Znth 0 l_vp 0) ))) (PreH5 : (un_pre > 0)) (PreH6 : (vn_pre > 0)) (PreH7 : (vn_pre <= un_pre)) (PreH8 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH9 : ((Zlength (l_src)) = un_pre)) (PreH10 : ((Zlength (l_vp)) = vn_pre)) (PreH11 : (list_within_bound UINT_MOD l_src )) (PreH12 : (list_within_bound UINT_MOD l_vp )) (PreH13 : (0 <= (Znth 0 l_vp 0))) (PreH14 : ((Znth 0 l_vp 0) <= UINT_MAX)) ,
  (UIntArray.full rp_pre (un_pre + 1 ) (app (l') ((cons (retval) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (un_pre + 1 ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "vp" ) )) # Ptr  |-> vp_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "vn" ) )) # Int  |-> vn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "vl" ) )) # UInt  |-> (Znth 0 l_vp 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "rp_i" ) )) # Ptr  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_mul_safety_wit_3 := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (i: Z) (cy: Z) (vl: Z) (rp_i: Z) (l_done: (@list Z)) (l_low: (@list Z)) (l_mid: (@list Z)) (val_out: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = un_pre)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : ((val_out + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_mid)) + ((list_to_Z (UINT_MOD) (l_src)) * vl ) ))) (PreH5 : (un_pre > 0)) (PreH6 : (vn_pre > 0)) (PreH7 : (vn_pre <= un_pre)) (PreH8 : (un_pre <= INT_MAX)) (PreH9 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH10 : (1 <= i)) (PreH11 : (i < vn_pre)) (PreH12 : (0 <= cy)) (PreH13 : (cy <= UINT_MAX)) (PreH14 : (0 <= vl)) (PreH15 : (vl <= UINT_MAX)) (PreH16 : ((Zlength (l_low)) = i)) (PreH17 : ((Zlength (l_mid)) = un_pre)) (PreH18 : (l_done = (app (l_low) (l_mid)))) (PreH19 : ((Zlength (l_done)) = (un_pre + i ))) (PreH20 : ((Zlength (l_src)) = un_pre)) (PreH21 : ((Zlength (l_vp)) = vn_pre)) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : (list_within_bound UINT_MOD l_low )) (PreH24 : (list_within_bound UINT_MOD l_mid )) (PreH25 : (list_within_bound UINT_MOD l_src )) (PreH26 : (list_within_bound UINT_MOD l_vp )) (PreH27 : ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) (PreH28 : (rp_i = (rp_pre + (i * sizeof(UINT))))) (PreH29 : (vl = (Znth i l_vp 0))) ,
  (UIntArray.full rp_i un_pre l_out )
  **  (UIntArray.full up_pre un_pre l_src )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "vp" ) )) # Ptr  |-> vp_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "vn" ) )) # Int  |-> vn_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "vl" ) )) # UInt  |-> vl)
  **  ((( &( "rp_i" ) )) # Ptr  |-> rp_i)
  **  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.undef_seg rp_pre (i + un_pre ) (un_pre + vn_pre ) )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  “ ((i + un_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + un_pre )) ”
.

Definition mpn_mul_safety_wit_4 := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (i: Z) (cy: Z) (vl: Z) (rp_i: Z) (l_done: (@list Z)) (l_low: (@list Z)) (l_mid: (@list Z)) (val_out: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = un_pre)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : ((val_out + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_mid)) + ((list_to_Z (UINT_MOD) (l_src)) * vl ) ))) (PreH5 : (un_pre > 0)) (PreH6 : (vn_pre > 0)) (PreH7 : (vn_pre <= un_pre)) (PreH8 : (un_pre <= INT_MAX)) (PreH9 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH10 : (1 <= i)) (PreH11 : (i < vn_pre)) (PreH12 : (0 <= cy)) (PreH13 : (cy <= UINT_MAX)) (PreH14 : (0 <= vl)) (PreH15 : (vl <= UINT_MAX)) (PreH16 : ((Zlength (l_low)) = i)) (PreH17 : ((Zlength (l_mid)) = un_pre)) (PreH18 : (l_done = (app (l_low) (l_mid)))) (PreH19 : ((Zlength (l_done)) = (un_pre + i ))) (PreH20 : ((Zlength (l_src)) = un_pre)) (PreH21 : ((Zlength (l_vp)) = vn_pre)) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : (list_within_bound UINT_MOD l_low )) (PreH24 : (list_within_bound UINT_MOD l_mid )) (PreH25 : (list_within_bound UINT_MOD l_src )) (PreH26 : (list_within_bound UINT_MOD l_vp )) (PreH27 : ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) (PreH28 : (rp_i = (rp_pre + (i * sizeof(UINT))))) (PreH29 : (vl = (Znth i l_vp 0))) ,
  (((rp_pre + ((i + un_pre ) * sizeof(UINT)))) # UInt  |-> retval)
  **  (UIntArray.undef_seg rp_pre ((i + un_pre ) + 1 ) (un_pre + vn_pre ) )
  **  (UIntArray.full rp_i un_pre l_out )
  **  (UIntArray.full up_pre un_pre l_src )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "vp" ) )) # Ptr  |-> vp_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "vn" ) )) # Int  |-> vn_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "vl" ) )) # UInt  |-> vl)
  **  ((( &( "rp_i" ) )) # Ptr  |-> rp_i)
  **  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_mul_safety_wit_5 := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (i: Z) (cy: Z) (vl: Z) (rp_i: Z) (l_done: (@list Z)) (l_low: (@list Z)) (l_mid: (@list Z)) (val_out: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = un_pre)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : ((val_out + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_mid)) + ((list_to_Z (UINT_MOD) (l_src)) * vl ) ))) (PreH5 : (un_pre > 0)) (PreH6 : (vn_pre > 0)) (PreH7 : (vn_pre <= un_pre)) (PreH8 : (un_pre <= INT_MAX)) (PreH9 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH10 : (1 <= i)) (PreH11 : (i < vn_pre)) (PreH12 : (0 <= cy)) (PreH13 : (cy <= UINT_MAX)) (PreH14 : (0 <= vl)) (PreH15 : (vl <= UINT_MAX)) (PreH16 : ((Zlength (l_low)) = i)) (PreH17 : ((Zlength (l_mid)) = un_pre)) (PreH18 : (l_done = (app (l_low) (l_mid)))) (PreH19 : ((Zlength (l_done)) = (un_pre + i ))) (PreH20 : ((Zlength (l_src)) = un_pre)) (PreH21 : ((Zlength (l_vp)) = vn_pre)) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : (list_within_bound UINT_MOD l_low )) (PreH24 : (list_within_bound UINT_MOD l_mid )) (PreH25 : (list_within_bound UINT_MOD l_src )) (PreH26 : (list_within_bound UINT_MOD l_vp )) (PreH27 : ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) (PreH28 : (rp_i = (rp_pre + (i * sizeof(UINT))))) (PreH29 : (vl = (Znth i l_vp 0))) ,
  (((rp_pre + ((i + un_pre ) * sizeof(UINT)))) # UInt  |-> retval)
  **  (UIntArray.undef_seg rp_pre ((i + un_pre ) + 1 ) (un_pre + vn_pre ) )
  **  (UIntArray.full rp_i un_pre l_out )
  **  (UIntArray.full up_pre un_pre l_src )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "vp" ) )) # Ptr  |-> vp_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "vn" ) )) # Int  |-> vn_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "vl" ) )) # UInt  |-> vl)
  **  ((( &( "rp_i" ) )) # Ptr  |-> rp_i)
  **  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_mul_entail_wit_1 := 
(
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : ((Zlength (l_src)) = un_pre)) (PreH5 : ((Zlength (l_vp)) = vn_pre)) (PreH6 : (list_within_bound UINT_MOD l_src )) (PreH7 : (list_within_bound UINT_MOD l_vp )) ,
  (UIntArray.undef_full rp_pre (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ (0 <= (Znth 0 l_vp 0)) ” 
  &&  “ ((Znth 0 l_vp 0) <= UINT_MAX) ”
  &&  (UIntArray.undef_full rp_pre un_pre )
  **  (UIntArray.undef_seg rp_pre un_pre (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
) \/
(
forall (vn_pre: Z) (un_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : ((Zlength (l_src)) = un_pre)) (PreH5 : ((Zlength (l_vp)) = vn_pre)) (PreH6 : (list_within_bound UINT_MOD l_src )) (PreH7 : (list_within_bound UINT_MOD l_vp )) ,
  (UIntArray.undef_full rp_pre (un_pre + vn_pre ) )
|--
  “ ((Znth 0 l_vp 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth 0 l_vp 0)) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ”
  &&  (UIntArray.undef_full rp_pre un_pre )
  **  (UIntArray.undef_seg rp_pre un_pre (un_pre + vn_pre ) )
).

Definition mpn_mul_entail_wit_1_split_goal_1 := 
forall (vn_pre: Z) (un_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : ((Zlength (l_src)) = un_pre)) (PreH5 : ((Zlength (l_vp)) = vn_pre)) (PreH6 : (list_within_bound UINT_MOD l_src )) (PreH7 : (list_within_bound UINT_MOD l_vp )) ,
  (UIntArray.undef_full rp_pre (un_pre + vn_pre ) )
|--
  “ ((Znth 0 l_vp 0) <= UINT_MAX) ”
.

Definition mpn_mul_entail_wit_1_split_goal_2 := 
forall (vn_pre: Z) (un_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : ((Zlength (l_src)) = un_pre)) (PreH5 : ((Zlength (l_vp)) = vn_pre)) (PreH6 : (list_within_bound UINT_MOD l_src )) (PreH7 : (list_within_bound UINT_MOD l_vp )) ,
  (UIntArray.undef_full rp_pre (un_pre + vn_pre ) )
|--
  “ (0 <= (Znth 0 l_vp 0)) ”
.

Definition mpn_mul_entail_wit_1_split_goal_3 := 
forall (vn_pre: Z) (un_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : ((Zlength (l_src)) = un_pre)) (PreH5 : ((Zlength (l_vp)) = vn_pre)) (PreH6 : (list_within_bound UINT_MOD l_src )) (PreH7 : (list_within_bound UINT_MOD l_vp )) ,
  (UIntArray.undef_full rp_pre (un_pre + vn_pre ) )
|--
  “ ((un_pre + vn_pre ) <= INT_MAX) ”
.

Definition mpn_mul_entail_wit_1_split_goal_spatial := 
forall (vn_pre: Z) (un_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : ((Zlength (l_src)) = un_pre)) (PreH5 : ((Zlength (l_vp)) = vn_pre)) (PreH6 : (list_within_bound UINT_MOD l_src )) (PreH7 : (list_within_bound UINT_MOD l_vp )) ,
  (UIntArray.undef_full rp_pre (un_pre + vn_pre ) )
|--
  (UIntArray.undef_full rp_pre un_pre )
  **  (UIntArray.undef_seg rp_pre un_pre (un_pre + vn_pre ) )
.

Definition mpn_mul_entail_wit_2 := 
(
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (val': Z) (l': (@list Z)) (retval: Z) (PreH1 : ((Zlength (l')) = un_pre)) (PreH2 : (list_within_bound UINT_MOD l' )) (PreH3 : ((list_to_Z (UINT_MOD) (l')) = val')) (PreH4 : ((val' + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_src)) * (Znth 0 l_vp 0) ))) (PreH5 : (un_pre > 0)) (PreH6 : (vn_pre > 0)) (PreH7 : (vn_pre <= un_pre)) (PreH8 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH9 : ((Zlength (l_src)) = un_pre)) (PreH10 : ((Zlength (l_vp)) = vn_pre)) (PreH11 : (list_within_bound UINT_MOD l_src )) (PreH12 : (list_within_bound UINT_MOD l_vp )) (PreH13 : (0 <= (Znth 0 l_vp 0))) (PreH14 : ((Znth 0 l_vp 0) <= UINT_MAX)) ,
  (UIntArray.full rp_pre (un_pre + 1 ) (app (l') ((cons (retval) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (un_pre + 1 ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
  **  ((( &( "vl" ) )) # UInt  |-> (Znth 0 l_vp 0))
|--
  EX (l_done: (@list Z)) ,
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= vn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (un_pre + 1 )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (1) (l_vp)))) )) ”
  &&  ((( &( "vl" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 (un_pre + 1 ) l_done )
  **  (UIntArray.undef_seg rp_pre (un_pre + 1 ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
) \/
(
forall (vn_pre: Z) (un_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (val': Z) (l': (@list Z)) (retval: Z) (PreH1 : ((Zlength (l')) = un_pre)) (PreH2 : (list_within_bound UINT_MOD l' )) (PreH3 : ((list_to_Z (UINT_MOD) (l')) = val')) (PreH4 : ((val' + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_src)) * (Znth 0 l_vp 0) ))) (PreH5 : (un_pre > 0)) (PreH6 : (vn_pre > 0)) (PreH7 : (vn_pre <= un_pre)) (PreH8 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH9 : ((Zlength (l_src)) = un_pre)) (PreH10 : ((Zlength (l_vp)) = vn_pre)) (PreH11 : (list_within_bound UINT_MOD l_src )) (PreH12 : (list_within_bound UINT_MOD l_vp )) (PreH13 : (0 <= (Znth 0 l_vp 0))) (PreH14 : ((Znth 0 l_vp 0) <= UINT_MAX)) ,
  (UIntArray.full rp_pre (un_pre + 1 ) (app (l') ((cons (retval) ((@nil Z))))) )
|--
  EX (l_done: (@list Z)) ,
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= vn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (un_pre + 1 )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (1) (l_vp)))) )) ”
  &&  (UIntArray.seg rp_pre 0 (un_pre + 1 ) l_done )
).

Definition mpn_mul_entail_wit_3 := 
(
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (l_done_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : (i < vn_pre)) (PreH2 : (un_pre > 0)) (PreH3 : (vn_pre > 0)) (PreH4 : (vn_pre <= un_pre)) (PreH5 : (un_pre <= INT_MAX)) (PreH6 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH7 : (1 <= i)) (PreH8 : (i <= vn_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= UINT_MAX)) (PreH11 : ((Zlength (l_done_2)) = (un_pre + i ))) (PreH12 : ((Zlength (l_src)) = un_pre)) (PreH13 : ((Zlength (l_vp)) = vn_pre)) (PreH14 : (list_within_bound UINT_MOD l_done_2 )) (PreH15 : (list_within_bound UINT_MOD l_src )) (PreH16 : (list_within_bound UINT_MOD l_vp )) (PreH17 : ((list_to_Z (UINT_MOD) (l_done_2)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) ,
  (UIntArray.seg rp_pre 0 (un_pre + i ) l_done_2 )
  **  (UIntArray.undef_seg rp_pre (un_pre + i ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  EX (l_done: (@list Z))  (l_mid: (@list Z))  (l_low: (@list Z)) ,
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < vn_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((Zlength (l_low)) = i) ” 
  &&  “ ((Zlength (l_mid)) = un_pre) ” 
  &&  “ (l_done = (app (l_low) (l_mid))) ” 
  &&  “ ((Zlength (l_done)) = (un_pre + i )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_low ) ” 
  &&  “ (list_within_bound UINT_MOD l_mid ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.seg rp_pre i (i + un_pre ) l_mid )
  **  (UIntArray.undef_seg rp_pre (i + un_pre ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
) \/
(
forall (vn_pre: Z) (un_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (l_done_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : (i < vn_pre)) (PreH2 : (un_pre > 0)) (PreH3 : (vn_pre > 0)) (PreH4 : (vn_pre <= un_pre)) (PreH5 : (un_pre <= INT_MAX)) (PreH6 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH7 : (1 <= i)) (PreH8 : (i <= vn_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= UINT_MAX)) (PreH11 : ((Zlength (l_done_2)) = (un_pre + i ))) (PreH12 : ((Zlength (l_src)) = un_pre)) (PreH13 : ((Zlength (l_vp)) = vn_pre)) (PreH14 : (list_within_bound UINT_MOD l_done_2 )) (PreH15 : (list_within_bound UINT_MOD l_src )) (PreH16 : (list_within_bound UINT_MOD l_vp )) (PreH17 : ((list_to_Z (UINT_MOD) (l_done_2)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) ,
  (UIntArray.seg rp_pre 0 (un_pre + i ) l_done_2 )
|--
  EX (l_mid: (@list Z))  (l_low: (@list Z)) ,
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < vn_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((Zlength (l_low)) = i) ” 
  &&  “ ((Zlength (l_mid)) = un_pre) ” 
  &&  “ ((Zlength ((app (l_low) (l_mid)))) = (un_pre + i )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD (app (l_low) (l_mid)) ) ” 
  &&  “ (list_within_bound UINT_MOD l_low ) ” 
  &&  “ (list_within_bound UINT_MOD l_mid ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((app (l_low) (l_mid)))) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.seg rp_pre i (i + un_pre ) l_mid )
).

Definition mpn_mul_entail_wit_4 := 
(
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (l_done_2: (@list Z)) (l_low_2: (@list Z)) (l_mid_2: (@list Z)) (i: Z) (cy: Z) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : (un_pre <= INT_MAX)) (PreH5 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH6 : (1 <= i)) (PreH7 : (i < vn_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= UINT_MAX)) (PreH10 : ((Zlength (l_low_2)) = i)) (PreH11 : ((Zlength (l_mid_2)) = un_pre)) (PreH12 : (l_done_2 = (app (l_low_2) (l_mid_2)))) (PreH13 : ((Zlength (l_done_2)) = (un_pre + i ))) (PreH14 : ((Zlength (l_src)) = un_pre)) (PreH15 : ((Zlength (l_vp)) = vn_pre)) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (list_within_bound UINT_MOD l_low_2 )) (PreH18 : (list_within_bound UINT_MOD l_mid_2 )) (PreH19 : (list_within_bound UINT_MOD l_src )) (PreH20 : (list_within_bound UINT_MOD l_vp )) (PreH21 : ((list_to_Z (UINT_MOD) (l_done_2)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) ,
  (UIntArray.full vp_pre vn_pre l_vp )
  **  (UIntArray.seg rp_pre 0 i l_low_2 )
  **  (UIntArray.seg rp_pre i (i + un_pre ) l_mid_2 )
  **  (UIntArray.undef_seg rp_pre (i + un_pre ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
|--
  EX (l_done: (@list Z))  (l_mid: (@list Z))  (l_low: (@list Z)) ,
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < vn_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ (0 <= (Znth i l_vp 0)) ” 
  &&  “ ((Znth i l_vp 0) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_low)) = i) ” 
  &&  “ ((Zlength (l_mid)) = un_pre) ” 
  &&  “ (l_done = (app (l_low) (l_mid))) ” 
  &&  “ ((Zlength (l_done)) = (un_pre + i )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_low ) ” 
  &&  “ (list_within_bound UINT_MOD l_mid ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) )) ” 
  &&  “ ((rp_pre + (i * sizeof(UINT))) = (rp_pre + (i * sizeof(UINT)))) ” 
  &&  “ ((Znth i l_vp 0) = (Znth i l_vp 0)) ”
  &&  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.full (rp_pre + (i * sizeof(UINT))) un_pre l_mid )
  **  (UIntArray.undef_seg rp_pre (i + un_pre ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
) \/
(
forall (vn_pre: Z) (un_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (l_done_2: (@list Z)) (l_low_2: (@list Z)) (l_mid_2: (@list Z)) (i: Z) (cy: Z) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : (un_pre <= INT_MAX)) (PreH5 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH6 : (1 <= i)) (PreH7 : (i < vn_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= UINT_MAX)) (PreH10 : ((Zlength (l_low_2)) = i)) (PreH11 : ((Zlength (l_mid_2)) = un_pre)) (PreH12 : (l_done_2 = (app (l_low_2) (l_mid_2)))) (PreH13 : ((Zlength (l_done_2)) = (un_pre + i ))) (PreH14 : ((Zlength (l_src)) = un_pre)) (PreH15 : ((Zlength (l_vp)) = vn_pre)) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (list_within_bound UINT_MOD l_low_2 )) (PreH18 : (list_within_bound UINT_MOD l_mid_2 )) (PreH19 : (list_within_bound UINT_MOD l_src )) (PreH20 : (list_within_bound UINT_MOD l_vp )) (PreH21 : ((list_to_Z (UINT_MOD) (l_done_2)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) ,
  (UIntArray.seg rp_pre i (i + un_pre ) l_mid_2 )
|--
  EX (l_mid: (@list Z)) ,
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < vn_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ (0 <= (Znth i l_vp 0)) ” 
  &&  “ ((Znth i l_vp 0) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_low_2)) = i) ” 
  &&  “ ((Zlength (l_mid)) = un_pre) ” 
  &&  “ ((Zlength ((app (l_low_2) (l_mid)))) = (un_pre + i )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD (app (l_low_2) (l_mid)) ) ” 
  &&  “ (list_within_bound UINT_MOD l_low_2 ) ” 
  &&  “ (list_within_bound UINT_MOD l_mid ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((app (l_low_2) (l_mid)))) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) )) ”
  &&  (UIntArray.full (rp_pre + (i * sizeof(UINT))) un_pre l_mid )
).

Definition mpn_mul_entail_wit_5 := 
(
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (i: Z) (cy: Z) (vl: Z) (rp_i: Z) (l_done_2: (@list Z)) (l_low: (@list Z)) (l_mid: (@list Z)) (val_out: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = un_pre)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : ((val_out + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_mid)) + ((list_to_Z (UINT_MOD) (l_src)) * vl ) ))) (PreH5 : (un_pre > 0)) (PreH6 : (vn_pre > 0)) (PreH7 : (vn_pre <= un_pre)) (PreH8 : (un_pre <= INT_MAX)) (PreH9 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH10 : (1 <= i)) (PreH11 : (i < vn_pre)) (PreH12 : (0 <= cy)) (PreH13 : (cy <= UINT_MAX)) (PreH14 : (0 <= vl)) (PreH15 : (vl <= UINT_MAX)) (PreH16 : ((Zlength (l_low)) = i)) (PreH17 : ((Zlength (l_mid)) = un_pre)) (PreH18 : (l_done_2 = (app (l_low) (l_mid)))) (PreH19 : ((Zlength (l_done_2)) = (un_pre + i ))) (PreH20 : ((Zlength (l_src)) = un_pre)) (PreH21 : ((Zlength (l_vp)) = vn_pre)) (PreH22 : (list_within_bound UINT_MOD l_done_2 )) (PreH23 : (list_within_bound UINT_MOD l_low )) (PreH24 : (list_within_bound UINT_MOD l_mid )) (PreH25 : (list_within_bound UINT_MOD l_src )) (PreH26 : (list_within_bound UINT_MOD l_vp )) (PreH27 : ((list_to_Z (UINT_MOD) (l_done_2)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) (PreH28 : (rp_i = (rp_pre + (i * sizeof(UINT))))) (PreH29 : (vl = (Znth i l_vp 0))) ,
  (((rp_pre + ((i + un_pre ) * sizeof(UINT)))) # UInt  |-> retval)
  **  (UIntArray.undef_seg rp_pre ((i + un_pre ) + 1 ) (un_pre + vn_pre ) )
  **  (UIntArray.full rp_i un_pre l_out )
  **  (UIntArray.full up_pre un_pre l_src )
  **  ((( &( "vl" ) )) # UInt  |-> vl)
  **  ((( &( "rp_i" ) )) # Ptr  |-> rp_i)
  **  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  EX (l_done: (@list Z)) ,
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= vn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (un_pre + (i + 1 ) )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_vp)))) )) ”
  &&  ((( &( "vl" ) )) # UInt  |->_)
  **  ((( &( "rp_i" ) )) # Ptr  |->_)
  **  (UIntArray.seg rp_pre 0 (un_pre + (i + 1 ) ) l_done )
  **  (UIntArray.undef_seg rp_pre (un_pre + (i + 1 ) ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
) \/
(
forall (vn_pre: Z) (un_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (i: Z) (cy: Z) (vl: Z) (rp_i: Z) (l_done_2: (@list Z)) (l_low: (@list Z)) (l_mid: (@list Z)) (val_out: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Zlength (l_out)) = un_pre)) (PreH4 : (list_within_bound UINT_MOD l_out )) (PreH5 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH6 : ((val_out + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_mid)) + ((list_to_Z (UINT_MOD) (l_src)) * vl ) ))) (PreH7 : (un_pre > 0)) (PreH8 : (vn_pre > 0)) (PreH9 : (vn_pre <= un_pre)) (PreH10 : (un_pre <= INT_MAX)) (PreH11 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH12 : (1 <= i)) (PreH13 : (i < vn_pre)) (PreH14 : (0 <= cy)) (PreH15 : (cy <= UINT_MAX)) (PreH16 : (0 <= vl)) (PreH17 : (vl <= UINT_MAX)) (PreH18 : ((Zlength (l_low)) = i)) (PreH19 : ((Zlength (l_mid)) = un_pre)) (PreH20 : (l_done_2 = (app (l_low) (l_mid)))) (PreH21 : ((Zlength (l_done_2)) = (un_pre + i ))) (PreH22 : ((Zlength (l_src)) = un_pre)) (PreH23 : ((Zlength (l_vp)) = vn_pre)) (PreH24 : (list_within_bound UINT_MOD l_done_2 )) (PreH25 : (list_within_bound UINT_MOD l_low )) (PreH26 : (list_within_bound UINT_MOD l_mid )) (PreH27 : (list_within_bound UINT_MOD l_src )) (PreH28 : (list_within_bound UINT_MOD l_vp )) (PreH29 : ((list_to_Z (UINT_MOD) (l_done_2)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) (PreH30 : (rp_i = (rp_pre + (i * sizeof(UINT))))) (PreH31 : (vl = (Znth i l_vp 0))) ,
  (((rp_pre + ((i + un_pre ) * sizeof(UINT)))) # UInt  |-> retval)
  **  (UIntArray.full rp_i un_pre l_out )
  **  (UIntArray.seg rp_pre 0 i l_low )
|--
  EX (l_done: (@list Z)) ,
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= vn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (un_pre + (i + 1 ) )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_vp)))) )) ”
  &&  (UIntArray.seg rp_pre 0 (un_pre + (i + 1 ) ) l_done )
).

Definition mpn_mul_return_wit_1 := 
(
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (l_done: (@list Z)) (cy: Z) (i: Z) (PreH1 : (i >= vn_pre)) (PreH2 : (un_pre > 0)) (PreH3 : (vn_pre > 0)) (PreH4 : (vn_pre <= un_pre)) (PreH5 : (un_pre <= INT_MAX)) (PreH6 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH7 : (1 <= i)) (PreH8 : (i <= vn_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= UINT_MAX)) (PreH11 : ((Zlength (l_done)) = (un_pre + i ))) (PreH12 : ((Zlength (l_src)) = un_pre)) (PreH13 : ((Zlength (l_vp)) = vn_pre)) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (list_within_bound UINT_MOD l_src )) (PreH16 : (list_within_bound UINT_MOD l_vp )) (PreH17 : ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) ,
  (UIntArray.seg rp_pre 0 (un_pre + i ) l_done )
  **  (UIntArray.undef_seg rp_pre (un_pre + i ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  EX (val_out: Z)  (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = (un_pre + vn_pre )) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_out)) = val_out) ” 
  &&  “ (val_out = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) (l_vp)) )) ”
  &&  (UIntArray.full rp_pre (un_pre + vn_pre ) l_out )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
) \/
(
forall (vn_pre: Z) (un_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (l_done: (@list Z)) (cy: Z) (i: Z) (PreH1 : (i >= vn_pre)) (PreH2 : (un_pre > 0)) (PreH3 : (vn_pre > 0)) (PreH4 : (vn_pre <= un_pre)) (PreH5 : (un_pre <= INT_MAX)) (PreH6 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH7 : (1 <= i)) (PreH8 : (i <= vn_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= UINT_MAX)) (PreH11 : ((Zlength (l_done)) = (un_pre + i ))) (PreH12 : ((Zlength (l_src)) = un_pre)) (PreH13 : ((Zlength (l_vp)) = vn_pre)) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (list_within_bound UINT_MOD l_src )) (PreH16 : (list_within_bound UINT_MOD l_vp )) (PreH17 : ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) ,
  (UIntArray.seg rp_pre 0 (un_pre + i ) l_done )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = (un_pre + vn_pre )) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_out)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) (l_vp)) )) ”
  &&  (UIntArray.full rp_pre (un_pre + vn_pre ) l_out )
).

Definition mpn_mul_partial_solve_wit_1 := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH5 : ((Zlength (l_src)) = un_pre)) (PreH6 : ((Zlength (l_vp)) = vn_pre)) (PreH7 : (list_within_bound UINT_MOD l_src )) (PreH8 : (list_within_bound UINT_MOD l_vp )) (PreH9 : (0 <= (Znth 0 l_vp 0))) (PreH10 : ((Znth 0 l_vp 0) <= UINT_MAX)) ,
  (UIntArray.undef_full rp_pre un_pre )
  **  (UIntArray.undef_seg rp_pre un_pre (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ (0 <= (Znth 0 l_vp 0)) ” 
  &&  “ ((Znth 0 l_vp 0) <= UINT_MAX) ”
  &&  (((vp_pre + (0 * sizeof(UINT)))) # UInt  |-> (Znth 0 l_vp 0))
  **  (UIntArray.missing_i vp_pre 0 0 vn_pre l_vp )
  **  (UIntArray.undef_full rp_pre un_pre )
  **  (UIntArray.undef_seg rp_pre un_pre (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
.

Definition mpn_mul_partial_solve_wit_2_pure := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH5 : ((Zlength (l_src)) = un_pre)) (PreH6 : ((Zlength (l_vp)) = vn_pre)) (PreH7 : (list_within_bound UINT_MOD l_src )) (PreH8 : (list_within_bound UINT_MOD l_vp )) (PreH9 : (0 <= (Znth 0 l_vp 0))) (PreH10 : ((Znth 0 l_vp 0) <= UINT_MAX)) ,
  (UIntArray.full vp_pre vn_pre l_vp )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "vp" ) )) # Ptr  |-> vp_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "vn" ) )) # Int  |-> vn_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "vl" ) )) # UInt  |-> (Znth 0 l_vp 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "rp_i" ) )) # Ptr  |->_)
  **  (UIntArray.undef_full rp_pre un_pre )
  **  (UIntArray.undef_seg rp_pre un_pre (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
|--
  “ (un_pre > 0) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ (0 <= (Znth 0 l_vp 0)) ” 
  &&  “ ((Znth 0 l_vp 0) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ”
.

Definition mpn_mul_partial_solve_wit_2_aux := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH5 : ((Zlength (l_src)) = un_pre)) (PreH6 : ((Zlength (l_vp)) = vn_pre)) (PreH7 : (list_within_bound UINT_MOD l_src )) (PreH8 : (list_within_bound UINT_MOD l_vp )) (PreH9 : (0 <= (Znth 0 l_vp 0))) (PreH10 : ((Znth 0 l_vp 0) <= UINT_MAX)) ,
  (UIntArray.full vp_pre vn_pre l_vp )
  **  (UIntArray.undef_full rp_pre un_pre )
  **  (UIntArray.undef_seg rp_pre un_pre (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
|--
  “ (un_pre > 0) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ (0 <= (Znth 0 l_vp 0)) ” 
  &&  “ ((Znth 0 l_vp 0) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ (0 <= (Znth 0 l_vp 0)) ” 
  &&  “ ((Znth 0 l_vp 0) <= UINT_MAX) ”
  &&  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.undef_full rp_pre un_pre )
  **  (UIntArray.full vp_pre vn_pre l_vp )
  **  (UIntArray.undef_seg rp_pre un_pre (un_pre + vn_pre ) )
.

Definition mpn_mul_partial_solve_wit_2 := mpn_mul_partial_solve_wit_2_pure -> mpn_mul_partial_solve_wit_2_aux.

Definition mpn_mul_partial_solve_wit_3 := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (val': Z) (l': (@list Z)) (retval: Z) (PreH1 : ((Zlength (l')) = un_pre)) (PreH2 : (list_within_bound UINT_MOD l' )) (PreH3 : ((list_to_Z (UINT_MOD) (l')) = val')) (PreH4 : ((val' + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_src)) * (Znth 0 l_vp 0) ))) (PreH5 : (un_pre > 0)) (PreH6 : (vn_pre > 0)) (PreH7 : (vn_pre <= un_pre)) (PreH8 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH9 : ((Zlength (l_src)) = un_pre)) (PreH10 : ((Zlength (l_vp)) = vn_pre)) (PreH11 : (list_within_bound UINT_MOD l_src )) (PreH12 : (list_within_bound UINT_MOD l_vp )) (PreH13 : (0 <= (Znth 0 l_vp 0))) (PreH14 : ((Znth 0 l_vp 0) <= UINT_MAX)) ,
  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full rp_pre un_pre l' )
  **  (UIntArray.full vp_pre vn_pre l_vp )
  **  (UIntArray.undef_seg rp_pre un_pre (un_pre + vn_pre ) )
|--
  “ ((Zlength (l')) = un_pre) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val') ” 
  &&  “ ((val' + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_src)) * (Znth 0 l_vp 0) )) ” 
  &&  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ (0 <= (Znth 0 l_vp 0)) ” 
  &&  “ ((Znth 0 l_vp 0) <= UINT_MAX) ”
  &&  (((rp_pre + (un_pre * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (un_pre + 1 ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full rp_pre un_pre l' )
  **  (UIntArray.full vp_pre vn_pre l_vp )
.

Definition mpn_mul_partial_solve_wit_4 := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (l_done: (@list Z)) (l_low: (@list Z)) (l_mid: (@list Z)) (i: Z) (cy: Z) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : (un_pre <= INT_MAX)) (PreH5 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH6 : (1 <= i)) (PreH7 : (i < vn_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= UINT_MAX)) (PreH10 : ((Zlength (l_low)) = i)) (PreH11 : ((Zlength (l_mid)) = un_pre)) (PreH12 : (l_done = (app (l_low) (l_mid)))) (PreH13 : ((Zlength (l_done)) = (un_pre + i ))) (PreH14 : ((Zlength (l_src)) = un_pre)) (PreH15 : ((Zlength (l_vp)) = vn_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_low )) (PreH18 : (list_within_bound UINT_MOD l_mid )) (PreH19 : (list_within_bound UINT_MOD l_src )) (PreH20 : (list_within_bound UINT_MOD l_vp )) (PreH21 : ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) ,
  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.seg rp_pre i (i + un_pre ) l_mid )
  **  (UIntArray.undef_seg rp_pre (i + un_pre ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < vn_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((Zlength (l_low)) = i) ” 
  &&  “ ((Zlength (l_mid)) = un_pre) ” 
  &&  “ (l_done = (app (l_low) (l_mid))) ” 
  &&  “ ((Zlength (l_done)) = (un_pre + i )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_low ) ” 
  &&  “ (list_within_bound UINT_MOD l_mid ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) )) ”
  &&  (((vp_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_vp 0))
  **  (UIntArray.missing_i vp_pre i 0 vn_pre l_vp )
  **  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.seg rp_pre i (i + un_pre ) l_mid )
  **  (UIntArray.undef_seg rp_pre (i + un_pre ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
.

Definition mpn_mul_partial_solve_wit_5_pure := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (i: Z) (cy: Z) (vl: Z) (rp_i: Z) (l_done: (@list Z)) (l_low: (@list Z)) (l_mid: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : (un_pre <= INT_MAX)) (PreH5 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH6 : (1 <= i)) (PreH7 : (i < vn_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= UINT_MAX)) (PreH10 : (0 <= vl)) (PreH11 : (vl <= UINT_MAX)) (PreH12 : ((Zlength (l_low)) = i)) (PreH13 : ((Zlength (l_mid)) = un_pre)) (PreH14 : (l_done = (app (l_low) (l_mid)))) (PreH15 : ((Zlength (l_done)) = (un_pre + i ))) (PreH16 : ((Zlength (l_src)) = un_pre)) (PreH17 : ((Zlength (l_vp)) = vn_pre)) (PreH18 : (list_within_bound UINT_MOD l_done )) (PreH19 : (list_within_bound UINT_MOD l_low )) (PreH20 : (list_within_bound UINT_MOD l_mid )) (PreH21 : (list_within_bound UINT_MOD l_src )) (PreH22 : (list_within_bound UINT_MOD l_vp )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) (PreH24 : (rp_i = (rp_pre + (i * sizeof(UINT))))) (PreH25 : (vl = (Znth i l_vp 0))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "vp" ) )) # Ptr  |-> vp_pre)
  **  ((( &( "un" ) )) # Int  |-> un_pre)
  **  ((( &( "vn" ) )) # Int  |-> vn_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  ((( &( "vl" ) )) # UInt  |-> vl)
  **  ((( &( "rp_i" ) )) # Ptr  |-> rp_i)
  **  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.full rp_i un_pre l_mid )
  **  (UIntArray.undef_seg rp_pre (i + un_pre ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  “ (un_pre > 0) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ (0 <= vl) ” 
  &&  “ (vl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_mid)) = un_pre) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_mid ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ”
.

Definition mpn_mul_partial_solve_wit_5_aux := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (i: Z) (cy: Z) (vl: Z) (rp_i: Z) (l_done: (@list Z)) (l_low: (@list Z)) (l_mid: (@list Z)) (PreH1 : (un_pre > 0)) (PreH2 : (vn_pre > 0)) (PreH3 : (vn_pre <= un_pre)) (PreH4 : (un_pre <= INT_MAX)) (PreH5 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH6 : (1 <= i)) (PreH7 : (i < vn_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= UINT_MAX)) (PreH10 : (0 <= vl)) (PreH11 : (vl <= UINT_MAX)) (PreH12 : ((Zlength (l_low)) = i)) (PreH13 : ((Zlength (l_mid)) = un_pre)) (PreH14 : (l_done = (app (l_low) (l_mid)))) (PreH15 : ((Zlength (l_done)) = (un_pre + i ))) (PreH16 : ((Zlength (l_src)) = un_pre)) (PreH17 : ((Zlength (l_vp)) = vn_pre)) (PreH18 : (list_within_bound UINT_MOD l_done )) (PreH19 : (list_within_bound UINT_MOD l_low )) (PreH20 : (list_within_bound UINT_MOD l_mid )) (PreH21 : (list_within_bound UINT_MOD l_src )) (PreH22 : (list_within_bound UINT_MOD l_vp )) (PreH23 : ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) (PreH24 : (rp_i = (rp_pre + (i * sizeof(UINT))))) (PreH25 : (vl = (Znth i l_vp 0))) ,
  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.full rp_i un_pre l_mid )
  **  (UIntArray.undef_seg rp_pre (i + un_pre ) (un_pre + vn_pre ) )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  “ (un_pre > 0) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ (0 <= vl) ” 
  &&  “ (vl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_mid)) = un_pre) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_mid ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < vn_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ (0 <= vl) ” 
  &&  “ (vl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_low)) = i) ” 
  &&  “ ((Zlength (l_mid)) = un_pre) ” 
  &&  “ (l_done = (app (l_low) (l_mid))) ” 
  &&  “ ((Zlength (l_done)) = (un_pre + i )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_low ) ” 
  &&  “ (list_within_bound UINT_MOD l_mid ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) )) ” 
  &&  “ (rp_i = (rp_pre + (i * sizeof(UINT)))) ” 
  &&  “ (vl = (Znth i l_vp 0)) ”
  &&  (UIntArray.full rp_i un_pre l_mid )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.undef_seg rp_pre (i + un_pre ) (un_pre + vn_pre ) )
  **  (UIntArray.full vp_pre vn_pre l_vp )
.

Definition mpn_mul_partial_solve_wit_5 := mpn_mul_partial_solve_wit_5_pure -> mpn_mul_partial_solve_wit_5_aux.

Definition mpn_mul_partial_solve_wit_6 := 
forall (vn_pre: Z) (vp_pre: Z) (un_pre: Z) (up_pre: Z) (rp_pre: Z) (l_vp: (@list Z)) (l_src: (@list Z)) (i: Z) (cy: Z) (vl: Z) (rp_i: Z) (l_done: (@list Z)) (l_low: (@list Z)) (l_mid: (@list Z)) (val_out: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = un_pre)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : ((list_to_Z (UINT_MOD) (l_out)) = val_out)) (PreH4 : ((val_out + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_mid)) + ((list_to_Z (UINT_MOD) (l_src)) * vl ) ))) (PreH5 : (un_pre > 0)) (PreH6 : (vn_pre > 0)) (PreH7 : (vn_pre <= un_pre)) (PreH8 : (un_pre <= INT_MAX)) (PreH9 : ((un_pre + vn_pre ) <= INT_MAX)) (PreH10 : (1 <= i)) (PreH11 : (i < vn_pre)) (PreH12 : (0 <= cy)) (PreH13 : (cy <= UINT_MAX)) (PreH14 : (0 <= vl)) (PreH15 : (vl <= UINT_MAX)) (PreH16 : ((Zlength (l_low)) = i)) (PreH17 : ((Zlength (l_mid)) = un_pre)) (PreH18 : (l_done = (app (l_low) (l_mid)))) (PreH19 : ((Zlength (l_done)) = (un_pre + i ))) (PreH20 : ((Zlength (l_src)) = un_pre)) (PreH21 : ((Zlength (l_vp)) = vn_pre)) (PreH22 : (list_within_bound UINT_MOD l_done )) (PreH23 : (list_within_bound UINT_MOD l_low )) (PreH24 : (list_within_bound UINT_MOD l_mid )) (PreH25 : (list_within_bound UINT_MOD l_src )) (PreH26 : (list_within_bound UINT_MOD l_vp )) (PreH27 : ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) ))) (PreH28 : (rp_i = (rp_pre + (i * sizeof(UINT))))) (PreH29 : (vl = (Znth i l_vp 0))) ,
  (UIntArray.full rp_i un_pre l_out )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.undef_seg rp_pre (i + un_pre ) (un_pre + vn_pre ) )
  **  (UIntArray.full vp_pre vn_pre l_vp )
|--
  “ ((Zlength (l_out)) = un_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_out)) = val_out) ” 
  &&  “ ((val_out + (retval * (Z.pow (UINT_MOD) (un_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_mid)) + ((list_to_Z (UINT_MOD) (l_src)) * vl ) )) ” 
  &&  “ (un_pre > 0) ” 
  &&  “ (vn_pre > 0) ” 
  &&  “ (vn_pre <= un_pre) ” 
  &&  “ (un_pre <= INT_MAX) ” 
  &&  “ ((un_pre + vn_pre ) <= INT_MAX) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < vn_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ (0 <= vl) ” 
  &&  “ (vl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_low)) = i) ” 
  &&  “ ((Zlength (l_mid)) = un_pre) ” 
  &&  “ (l_done = (app (l_low) (l_mid))) ” 
  &&  “ ((Zlength (l_done)) = (un_pre + i )) ” 
  &&  “ ((Zlength (l_src)) = un_pre) ” 
  &&  “ ((Zlength (l_vp)) = vn_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_low ) ” 
  &&  “ (list_within_bound UINT_MOD l_mid ) ” 
  &&  “ (list_within_bound UINT_MOD l_src ) ” 
  &&  “ (list_within_bound UINT_MOD l_vp ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = ((list_to_Z (UINT_MOD) (l_src)) * (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_vp)))) )) ” 
  &&  “ (rp_i = (rp_pre + (i * sizeof(UINT)))) ” 
  &&  “ (vl = (Znth i l_vp 0)) ”
  &&  (((rp_pre + ((i + un_pre ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre ((i + un_pre ) + 1 ) (un_pre + vn_pre ) )
  **  (UIntArray.full rp_i un_pre l_out )
  **  (UIntArray.full up_pre un_pre l_src )
  **  (UIntArray.seg rp_pre 0 i l_low )
  **  (UIntArray.full vp_pre vn_pre l_vp )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_mul_safety_wit_1 : mpn_mul_safety_wit_1.
Axiom proof_of_mpn_mul_safety_wit_2 : mpn_mul_safety_wit_2.
Axiom proof_of_mpn_mul_safety_wit_3 : mpn_mul_safety_wit_3.
Axiom proof_of_mpn_mul_safety_wit_4 : mpn_mul_safety_wit_4.
Axiom proof_of_mpn_mul_safety_wit_5 : mpn_mul_safety_wit_5.
Axiom proof_of_mpn_mul_entail_wit_1 : mpn_mul_entail_wit_1.
Axiom proof_of_mpn_mul_entail_wit_2 : mpn_mul_entail_wit_2.
Axiom proof_of_mpn_mul_entail_wit_3 : mpn_mul_entail_wit_3.
Axiom proof_of_mpn_mul_entail_wit_4 : mpn_mul_entail_wit_4.
Axiom proof_of_mpn_mul_entail_wit_5 : mpn_mul_entail_wit_5.
Axiom proof_of_mpn_mul_return_wit_1 : mpn_mul_return_wit_1.
Axiom proof_of_mpn_mul_partial_solve_wit_1 : mpn_mul_partial_solve_wit_1.
Axiom proof_of_mpn_mul_partial_solve_wit_2_pure : mpn_mul_partial_solve_wit_2_pure.
Axiom proof_of_mpn_mul_partial_solve_wit_2 : mpn_mul_partial_solve_wit_2.
Axiom proof_of_mpn_mul_partial_solve_wit_3 : mpn_mul_partial_solve_wit_3.
Axiom proof_of_mpn_mul_partial_solve_wit_4 : mpn_mul_partial_solve_wit_4.
Axiom proof_of_mpn_mul_partial_solve_wit_5_pure : mpn_mul_partial_solve_wit_5_pure.
Axiom proof_of_mpn_mul_partial_solve_wit_5 : mpn_mul_partial_solve_wit_5.
Axiom proof_of_mpn_mul_partial_solve_wit_6 : mpn_mul_partial_solve_wit_6.

End VC_Correct.
