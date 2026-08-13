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

(*----- Function mpn_add -----*)

Definition mpn_add_safety_wit_1_rp_eq_bp := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (rp_pre = bp_pre)) (PreH2 : (an_pre > bn_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (bn_pre >= 0)) (PreH5 : ((an_pre - bn_pre ) > 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH9 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
|--
  “ ((an_pre - bn_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (an_pre - bn_pre )) ”
.

Definition mpn_add_safety_wit_2_rp_eq_ap := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (an_pre > bn_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (bn_pre >= 0)) (PreH5 : ((an_pre - bn_pre ) > 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH9 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  “ ((an_pre - bn_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (an_pre - bn_pre )) ”
.

Definition mpn_add_entail_wit_1_rp_eq_bp := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (an_pre >= bn_pre)) (PreH6 : (an_pre >= 0)) (PreH7 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.undef_seg rp_pre bn_pre an_pre )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp )) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.undef_seg rp_pre bn_pre an_pre )
.

Definition mpn_add_entail_wit_2_rp_eq_ap := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (an_pre >= bn_pre)) (PreH6 : (an_pre >= 0)) (PreH7 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap )) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
.

Definition mpn_add_entail_wit_3_rp_eq_bp := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (an_pre <= INT_MAX)) (PreH4 : (bn_pre <= INT_MAX)) (PreH5 : (an_pre >= INT_MIN)) (PreH6 : (bn_pre >= INT_MIN)) (PreH7 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH8 : (rp_pre = bp_pre)) (PreH9 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH10 : (rp_pre = bp_pre)) (PreH11 : (an_pre >= bn_pre)) (PreH12 : (an_pre >= 0)) (PreH13 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_seg rp_pre bn_pre an_pre )
|--
  EX (val_r_low: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((val_r_low + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp )) ” 
  &&  “ (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (an_pre <= INT_MAX)) (PreH4 : (bn_pre <= INT_MAX)) (PreH5 : (an_pre >= INT_MIN)) (PreH6 : (bn_pre >= INT_MIN)) (PreH7 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH8 : (rp_pre = bp_pre)) (PreH9 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH10 : (rp_pre = bp_pre)) (PreH11 : (an_pre >= bn_pre)) (PreH12 : (an_pre >= 0)) (PreH13 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_seg rp_pre bn_pre an_pre )
|--
  EX (val_r_low: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((val_r_low + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp )) ” 
  &&  “ (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
).

Definition mpn_add_entail_wit_4_rp_eq_ap := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (an_pre <= INT_MAX)) (PreH4 : (bn_pre <= INT_MAX)) (PreH5 : (an_pre >= INT_MIN)) (PreH6 : (bn_pre >= INT_MIN)) (PreH7 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH8 : (rp_pre = ap_pre)) (PreH9 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH10 : (rp_pre = ap_pre)) (PreH11 : (an_pre >= bn_pre)) (PreH12 : (an_pre >= 0)) (PreH13 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  EX (val_r_low: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((val_r_low + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap )) ” 
  &&  “ (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ”
  &&  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
.

Definition mpn_add_entail_wit_5_rp_eq_bp := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low_2: Z) (cy: Z) (PreH1 : (an_pre > bn_pre)) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low_2 + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH9 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low_2 bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
|--
  EX (val_r_low: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp )) ” 
  &&  “ (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
.

Definition mpn_add_entail_wit_6_rp_eq_ap := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low_2: Z) (cy: Z) (PreH1 : (an_pre > bn_pre)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low_2 + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH9 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD rp_pre val_r_low_2 bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  EX (val_r_low: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap )) ” 
  &&  “ (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ”
  &&  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
.

Definition mpn_add_entail_wit_7_rp_eq_bp := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (val': Z) (retval: Z) (PreH1 : ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + cy ))) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (an_pre > bn_pre)) (PreH4 : (an_pre >= bn_pre)) (PreH5 : (bn_pre >= 0)) (PreH6 : ((an_pre - bn_pre ) > 0)) (PreH7 : (0 <= cy)) (PreH8 : (cy <= UINT_MAX)) (PreH9 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH10 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + cy )) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp )) ” 
  &&  “ (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
.

Definition mpn_add_entail_wit_8_rp_eq_ap := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (val': Z) (retval: Z) (PreH1 : ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + cy ))) (PreH2 : ((rp_pre + (bn_pre * sizeof(UINT))) = (ap_pre + (bn_pre * sizeof(UINT))))) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (an_pre > bn_pre)) (PreH5 : (an_pre >= bn_pre)) (PreH6 : (bn_pre >= 0)) (PreH7 : ((an_pre - bn_pre ) > 0)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= UINT_MAX)) (PreH10 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH11 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + cy )) ” 
  &&  “ ((rp_pre + (bn_pre * sizeof(UINT))) = (ap_pre + (bn_pre * sizeof(UINT)))) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap )) ” 
  &&  “ (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
.

Definition mpn_add_entail_wit_9_1_rp_eq_bp := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (val': Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (bn_pre <= INT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre >= INT_MIN)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + cy ))) (PreH8 : (rp_pre = bp_pre)) (PreH9 : (an_pre > bn_pre)) (PreH10 : (an_pre >= bn_pre)) (PreH11 : (bn_pre >= 0)) (PreH12 : ((an_pre - bn_pre ) > 0)) (PreH13 : (0 <= cy)) (PreH14 : (cy <= UINT_MAX)) (PreH15 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH16 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
|--
  EX (val_r_out: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_bp + val_b_rp_eq_bp )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp an_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (val': Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (bn_pre <= INT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre >= INT_MIN)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + cy ))) (PreH8 : (rp_pre = bp_pre)) (PreH9 : (an_pre > bn_pre)) (PreH10 : (an_pre >= bn_pre)) (PreH11 : (bn_pre >= 0)) (PreH12 : ((an_pre - bn_pre ) > 0)) (PreH13 : (0 <= cy)) (PreH14 : (cy <= UINT_MAX)) (PreH15 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH16 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
|--
  EX (val_r_out: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_bp + val_b_rp_eq_bp )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp an_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
).

Definition mpn_add_entail_wit_9_2_rp_eq_bp := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (an_pre <= bn_pre)) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH9 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_bp + val_b_rp_eq_bp )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp an_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (an_pre <= bn_pre)) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH9 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_bp + val_b_rp_eq_bp )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp an_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
).

Definition mpn_add_entail_wit_10_1_rp_eq_ap := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (val': Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (bn_pre <= INT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre >= INT_MIN)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + cy ))) (PreH8 : ((rp_pre + (bn_pre * sizeof(UINT))) = (ap_pre + (bn_pre * sizeof(UINT))))) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (an_pre > bn_pre)) (PreH11 : (an_pre >= bn_pre)) (PreH12 : (bn_pre >= 0)) (PreH13 : ((an_pre - bn_pre ) > 0)) (PreH14 : (0 <= cy)) (PreH15 : (cy <= UINT_MAX)) (PreH16 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH17 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
|--
  EX (val_r_out: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_ap + val_b_rp_eq_ap )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_r_out an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (val': Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (bn_pre <= INT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre >= INT_MIN)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + cy ))) (PreH8 : ((rp_pre + (bn_pre * sizeof(UINT))) = (ap_pre + (bn_pre * sizeof(UINT))))) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (an_pre > bn_pre)) (PreH11 : (an_pre >= bn_pre)) (PreH12 : (bn_pre >= 0)) (PreH13 : ((an_pre - bn_pre ) > 0)) (PreH14 : (0 <= cy)) (PreH15 : (cy <= UINT_MAX)) (PreH16 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH17 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
|--
  EX (val_r_out: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_ap + val_b_rp_eq_ap )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_r_out an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
).

Definition mpn_add_entail_wit_10_2_rp_eq_ap := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (an_pre <= bn_pre)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH9 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_ap + val_b_rp_eq_ap )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_r_out an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (an_pre <= bn_pre)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH9 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_ap + val_b_rp_eq_ap )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_r_out an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
).

Definition mpn_add_return_wit_1_rp_eq_bp := 
forall (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_r_out_2: Z) (cy: Z) (PreH1 : (rp_pre = bp_pre)) (PreH2 : (0 <= cy)) (PreH3 : (cy <= UINT_MAX)) (PreH4 : ((val_r_out_2 + (cy * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_bp + val_b_rp_eq_bp ))) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp an_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out_2 an_pre )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_bp + val_b_rp_eq_bp )) ” 
  &&  “ (rp_pre = bp_pre) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp an_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
.

Definition mpn_add_return_wit_2_rp_eq_ap := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_r_out_2: Z) (cy: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (0 <= cy)) (PreH3 : (cy <= UINT_MAX)) (PreH4 : ((val_r_out_2 + (cy * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_ap + val_b_rp_eq_ap ))) ,
  (mpd_store_Z UINT_MOD ap_pre val_r_out_2 an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a_rp_eq_ap + val_b_rp_eq_ap )) ” 
  &&  “ (rp_pre = ap_pre) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_r_out an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
.

Definition mpn_add_partial_solve_wit_1_rp_eq_ap_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_ap an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_add_partial_solve_wit_1_rp_eq_ap_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_ap an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_ap an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
.

Definition mpn_add_partial_solve_wit_1_rp_eq_ap := mpn_add_partial_solve_wit_1_rp_eq_ap_pure -> mpn_add_partial_solve_wit_1_rp_eq_ap_aux.

Definition mpn_add_partial_solve_wit_2_rp_eq_bp_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (PreH1 : (rp_pre = bp_pre)) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_bp bn_pre )
  **  (UIntArray.undef_seg rp_pre bn_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_add_partial_solve_wit_2_rp_eq_bp_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (PreH1 : (rp_pre = bp_pre)) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_bp bn_pre )
  **  (UIntArray.undef_seg rp_pre bn_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_bp bn_pre )
  **  (UIntArray.undef_seg rp_pre bn_pre an_pre )
.

Definition mpn_add_partial_solve_wit_2_rp_eq_bp := mpn_add_partial_solve_wit_2_rp_eq_bp_pure -> mpn_add_partial_solve_wit_2_rp_eq_bp_aux.

Definition mpn_add_partial_solve_wit_3_rp_eq_bp_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (PreH1 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_bp bn_pre )
  **  (UIntArray.undef_seg rp_pre bn_pre an_pre )
|--
  “ (rp_pre = bp_pre) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_add_partial_solve_wit_3_rp_eq_bp_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (PreH1 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_bp bn_pre )
  **  (UIntArray.undef_seg rp_pre bn_pre an_pre )
|--
  “ (rp_pre = bp_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_bp bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_seg rp_pre bn_pre an_pre )
.

Definition mpn_add_partial_solve_wit_3_rp_eq_bp := mpn_add_partial_solve_wit_3_rp_eq_bp_pure -> mpn_add_partial_solve_wit_3_rp_eq_bp_aux.

Definition mpn_add_partial_solve_wit_4_rp_eq_ap_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (PreH1 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
|--
  “ (rp_pre = ap_pre) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_add_partial_solve_wit_4_rp_eq_ap_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (PreH1 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
|--
  “ (rp_pre = ap_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
.

Definition mpn_add_partial_solve_wit_4_rp_eq_ap := mpn_add_partial_solve_wit_4_rp_eq_ap_pure -> mpn_add_partial_solve_wit_4_rp_eq_ap_aux.

Definition mpn_add_partial_solve_wit_5_rp_eq_bp_pure := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (rp_pre = bp_pre)) (PreH2 : (an_pre > bn_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (bn_pre >= 0)) (PreH5 : ((an_pre - bn_pre ) > 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH9 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
|--
  “ ((rp_pre + (bn_pre * sizeof(UINT))) <> (ap_pre + (bn_pre * sizeof(UINT)))) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (cy = cy) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((bp_pre + (bn_pre * sizeof(UINT))) <> (ap_pre + (bn_pre * sizeof(UINT)))) ”
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (cy >= 0)) (PreH2 : (bn_pre <= INT_MAX)) (PreH3 : (an_pre <= INT_MAX)) (PreH4 : (bn_pre >= INT_MIN)) (PreH5 : (an_pre >= INT_MIN)) (PreH6 : (rp_pre = bp_pre)) (PreH7 : (an_pre > bn_pre)) (PreH8 : (an_pre >= bn_pre)) (PreH9 : (bn_pre >= 0)) (PreH10 : ((an_pre - bn_pre ) > 0)) (PreH11 : (0 <= cy)) (PreH12 : (cy <= UINT_MAX)) (PreH13 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH14 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
|--
  “ ((bp_pre + (bn_pre * sizeof(UINT))) <> (ap_pre + (bn_pre * sizeof(UINT)))) ” 
  &&  “ ((bp_pre + (bn_pre * sizeof(UINT))) <> (ap_pre + (bn_pre * sizeof(UINT)))) ”
).

Definition mpn_add_partial_solve_wit_5_rp_eq_bp_pure_split_goal_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (cy >= 0)) (PreH2 : (bn_pre <= INT_MAX)) (PreH3 : (an_pre <= INT_MAX)) (PreH4 : (bn_pre >= INT_MIN)) (PreH5 : (an_pre >= INT_MIN)) (PreH6 : (rp_pre = bp_pre)) (PreH7 : (an_pre > bn_pre)) (PreH8 : (an_pre >= bn_pre)) (PreH9 : (bn_pre >= 0)) (PreH10 : ((an_pre - bn_pre ) > 0)) (PreH11 : (0 <= cy)) (PreH12 : (cy <= UINT_MAX)) (PreH13 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH14 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
|--
  “ ((bp_pre + (bn_pre * sizeof(UINT))) <> (ap_pre + (bn_pre * sizeof(UINT)))) ”
.

Definition mpn_add_partial_solve_wit_5_rp_eq_bp_pure_split_goal_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (cy >= 0)) (PreH2 : (bn_pre <= INT_MAX)) (PreH3 : (an_pre <= INT_MAX)) (PreH4 : (bn_pre >= INT_MIN)) (PreH5 : (an_pre >= INT_MIN)) (PreH6 : (rp_pre = bp_pre)) (PreH7 : (an_pre > bn_pre)) (PreH8 : (an_pre >= bn_pre)) (PreH9 : (bn_pre >= 0)) (PreH10 : ((an_pre - bn_pre ) > 0)) (PreH11 : (0 <= cy)) (PreH12 : (cy <= UINT_MAX)) (PreH13 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH14 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
|--
  “ ((bp_pre + (bn_pre * sizeof(UINT))) <> (ap_pre + (bn_pre * sizeof(UINT)))) ”
.

Definition mpn_add_partial_solve_wit_5_rp_eq_bp_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (rp_pre = bp_pre)) (PreH2 : (an_pre > bn_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (bn_pre >= 0)) (PreH5 : ((an_pre - bn_pre ) > 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp ))) (PreH9 : (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
|--
  “ ((rp_pre + (bn_pre * sizeof(UINT))) <> (ap_pre + (bn_pre * sizeof(UINT)))) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (cy = cy) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((bp_pre + (bn_pre * sizeof(UINT))) <> (ap_pre + (bn_pre * sizeof(UINT)))) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_bp )) ” 
  &&  “ (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ”
  &&  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
.

Definition mpn_add_partial_solve_wit_5_rp_eq_bp := mpn_add_partial_solve_wit_5_rp_eq_bp_pure -> mpn_add_partial_solve_wit_5_rp_eq_bp_aux.

Definition mpn_add_partial_solve_wit_6_rp_eq_ap_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (an_pre > bn_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (bn_pre >= 0)) (PreH5 : ((an_pre - bn_pre ) > 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH9 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  “ ((rp_pre + (bn_pre * sizeof(UINT))) = (ap_pre + (bn_pre * sizeof(UINT)))) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (cy = cy) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ”
.

Definition mpn_add_partial_solve_wit_6_rp_eq_ap_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (val_a_low: Z) (val_a_high: Z) (val_r_low: Z) (cy: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (an_pre > bn_pre)) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (bn_pre >= 0)) (PreH5 : ((an_pre - bn_pre ) > 0)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap ))) (PreH9 : (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) ,
  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  “ ((rp_pre + (bn_pre * sizeof(UINT))) = (ap_pre + (bn_pre * sizeof(UINT)))) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (cy = cy) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((val_r_low + (cy * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b_rp_eq_ap )) ” 
  &&  “ (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ”
  &&  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap bn_pre )
.

Definition mpn_add_partial_solve_wit_6_rp_eq_ap := mpn_add_partial_solve_wit_6_rp_eq_ap_pure -> mpn_add_partial_solve_wit_6_rp_eq_ap_aux.

Definition mpn_add_which_implies_wit_1 := 
(
forall (val_a_rp_eq_ap: Z) (an: Z) (ap: Z) (bn: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (mpd_store_Z UINT_MOD ap val_a_rp_eq_ap an )
|--
  EX (val_a_high: Z)  (val_a_low: Z) ,
  “ (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap val_a_low bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT))) val_a_high (an - bn ) )
) \/
(
forall (val_a_rp_eq_ap: Z) (an: Z) (ap: Z) (bn: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (mpd_store_Z UINT_MOD ap val_a_rp_eq_ap an )
|--
  EX (val_a_high: Z)  (val_a_low: Z) ,
  “ (val_a_rp_eq_ap = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap val_a_low bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT))) val_a_high (an - bn ) )
).

Definition mpn_add_which_implies_wit_2 := 
(
forall (val_a_rp_eq_bp: Z) (an: Z) (ap: Z) (bn: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (mpd_store_Z UINT_MOD ap val_a_rp_eq_bp an )
|--
  EX (val_a_high: Z)  (val_a_low: Z) ,
  “ (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap val_a_low bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT))) val_a_high (an - bn ) )
) \/
(
forall (val_a_rp_eq_bp: Z) (an: Z) (ap: Z) (bn: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (mpd_store_Z UINT_MOD ap val_a_rp_eq_bp an )
|--
  EX (val_a_high: Z)  (val_a_low: Z) ,
  “ (val_a_rp_eq_bp = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap val_a_low bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT))) val_a_high (an - bn ) )
).

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_add_safety_wit_1_rp_eq_bp : mpn_add_safety_wit_1_rp_eq_bp.
Axiom proof_of_mpn_add_safety_wit_2_rp_eq_ap : mpn_add_safety_wit_2_rp_eq_ap.
Axiom proof_of_mpn_add_entail_wit_1_rp_eq_bp : mpn_add_entail_wit_1_rp_eq_bp.
Axiom proof_of_mpn_add_entail_wit_2_rp_eq_ap : mpn_add_entail_wit_2_rp_eq_ap.
Axiom proof_of_mpn_add_entail_wit_3_rp_eq_bp : mpn_add_entail_wit_3_rp_eq_bp.
Axiom proof_of_mpn_add_entail_wit_4_rp_eq_ap : mpn_add_entail_wit_4_rp_eq_ap.
Axiom proof_of_mpn_add_entail_wit_5_rp_eq_bp : mpn_add_entail_wit_5_rp_eq_bp.
Axiom proof_of_mpn_add_entail_wit_6_rp_eq_ap : mpn_add_entail_wit_6_rp_eq_ap.
Axiom proof_of_mpn_add_entail_wit_7_rp_eq_bp : mpn_add_entail_wit_7_rp_eq_bp.
Axiom proof_of_mpn_add_entail_wit_8_rp_eq_ap : mpn_add_entail_wit_8_rp_eq_ap.
Axiom proof_of_mpn_add_entail_wit_9_1_rp_eq_bp : mpn_add_entail_wit_9_1_rp_eq_bp.
Axiom proof_of_mpn_add_entail_wit_9_2_rp_eq_bp : mpn_add_entail_wit_9_2_rp_eq_bp.
Axiom proof_of_mpn_add_entail_wit_10_1_rp_eq_ap : mpn_add_entail_wit_10_1_rp_eq_ap.
Axiom proof_of_mpn_add_entail_wit_10_2_rp_eq_ap : mpn_add_entail_wit_10_2_rp_eq_ap.
Axiom proof_of_mpn_add_return_wit_1_rp_eq_bp : mpn_add_return_wit_1_rp_eq_bp.
Axiom proof_of_mpn_add_return_wit_2_rp_eq_ap : mpn_add_return_wit_2_rp_eq_ap.
Axiom proof_of_mpn_add_partial_solve_wit_1_rp_eq_ap_pure : mpn_add_partial_solve_wit_1_rp_eq_ap_pure.
Axiom proof_of_mpn_add_partial_solve_wit_1_rp_eq_ap : mpn_add_partial_solve_wit_1_rp_eq_ap.
Axiom proof_of_mpn_add_partial_solve_wit_2_rp_eq_bp_pure : mpn_add_partial_solve_wit_2_rp_eq_bp_pure.
Axiom proof_of_mpn_add_partial_solve_wit_2_rp_eq_bp : mpn_add_partial_solve_wit_2_rp_eq_bp.
Axiom proof_of_mpn_add_partial_solve_wit_3_rp_eq_bp_pure : mpn_add_partial_solve_wit_3_rp_eq_bp_pure.
Axiom proof_of_mpn_add_partial_solve_wit_3_rp_eq_bp : mpn_add_partial_solve_wit_3_rp_eq_bp.
Axiom proof_of_mpn_add_partial_solve_wit_4_rp_eq_ap_pure : mpn_add_partial_solve_wit_4_rp_eq_ap_pure.
Axiom proof_of_mpn_add_partial_solve_wit_4_rp_eq_ap : mpn_add_partial_solve_wit_4_rp_eq_ap.
Axiom proof_of_mpn_add_partial_solve_wit_5_rp_eq_bp_pure : mpn_add_partial_solve_wit_5_rp_eq_bp_pure.
Axiom proof_of_mpn_add_partial_solve_wit_5_rp_eq_bp : mpn_add_partial_solve_wit_5_rp_eq_bp.
Axiom proof_of_mpn_add_partial_solve_wit_6_rp_eq_ap_pure : mpn_add_partial_solve_wit_6_rp_eq_ap_pure.
Axiom proof_of_mpn_add_partial_solve_wit_6_rp_eq_ap : mpn_add_partial_solve_wit_6_rp_eq_ap.
Axiom proof_of_mpn_add_which_implies_wit_1 : mpn_add_which_implies_wit_1.
Axiom proof_of_mpn_add_which_implies_wit_2 : mpn_add_which_implies_wit_2.

End VC_Correct.
