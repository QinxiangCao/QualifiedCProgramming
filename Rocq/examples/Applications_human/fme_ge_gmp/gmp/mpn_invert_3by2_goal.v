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

(*----- Function mpn_invert_3by2 -----*)

Definition mpn_invert_3by2_safety_wit_1 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) ,
  ((( &( "qh" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition mpn_invert_3by2_safety_wit_2 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) ,
  ((( &( "qh" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |-> (Z.land u1_pre 65535))
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_3 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) ,
  ((( &( "qh" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |-> (Z.land u1_pre 65535))
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_4 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.shiftr u1_pre 16) <> 0)) (PreH2 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH7 : (u1_pre <= UINT_MAX)) (PreH8 : (0 <= u0_pre)) (PreH9 : (u0_pre <= UINT_MAX)) ,
  ((( &( "uh" ) )) # UInt  |-> (Z.shiftr u1_pre 16))
  **  ((( &( "qh" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |-> (Z.land u1_pre 65535))
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
|--
  “ ((Z.shiftr u1_pre 16) <> 0) ”
.

Definition mpn_invert_3by2_safety_wit_5 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (ul0 = (Z.land u1_pre 65535))) (PreH6 : (uh0 = (Z.shiftr u1_pre 16))) (PreH7 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH8 : (0 <= ul0)) (PreH9 : (ul0 < 65536)) (PreH10 : (1 <= uh0)) (PreH11 : (uh0 < 65536)) (PreH12 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH13 : (0 <= qh0)) (PreH14 : (qh0 < 65536)) (PreH15 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "ul" ) )) # UInt  |-> ul0)
  **  ((( &( "uh" ) )) # UInt  |-> uh0)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ql" ) )) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_6 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (ul0 = (Z.land u1_pre 65535))) (PreH6 : (uh0 = (Z.shiftr u1_pre 16))) (PreH7 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH8 : (0 <= ul0)) (PreH9 : (ul0 < 65536)) (PreH10 : (1 <= uh0)) (PreH11 : (uh0 < 65536)) (PreH12 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH13 : (0 <= qh0)) (PreH14 : (qh0 < 65536)) (PreH15 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "ul" ) )) # UInt  |-> ul0)
  **  ((( &( "uh" ) )) # UInt  |-> uh0)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ql" ) )) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_7 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (ul0 = (Z.land u1_pre 65535))) (PreH6 : (uh0 = (Z.shiftr u1_pre 16))) (PreH7 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH8 : (0 <= ul0)) (PreH9 : (ul0 < 65536)) (PreH10 : (1 <= uh0)) (PreH11 : (uh0 < 65536)) (PreH12 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH13 : (0 <= qh0)) (PreH14 : (qh0 < 65536)) (PreH15 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "ul" ) )) # UInt  |-> ul0)
  **  ((( &( "uh" ) )) # UInt  |-> uh0)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ql" ) )) # UInt  |->_)
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition mpn_invert_3by2_safety_wit_8 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |-> rhalf)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_9 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |-> rhalf)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_10 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |-> rhalf)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)))
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_11 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |-> rhalf)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)))
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_12 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |-> rhalf)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)))
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_invert_3by2_safety_wit_13 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : (0 <= p0)) (PreH11 : (p0 <= UINT_MAX)) (PreH12 : (0 <= ql0)) (PreH13 : (ql0 <= 65536)) (PreH14 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH15 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH16 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |-> rhalf)
  **  ((( &( "p" ) )) # UInt  |-> p0)
  **  ((( &( "ql" ) )) # UInt  |-> ql0)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_14 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : (0 <= p0)) (PreH11 : (p0 <= UINT_MAX)) (PreH12 : (0 <= ql0)) (PreH13 : (ql0 <= 65536)) (PreH14 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH15 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH16 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |-> rhalf)
  **  ((( &( "p" ) )) # UInt  |-> p0)
  **  ((( &( "ql" ) )) # UInt  |-> ql0)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_15 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : (0 <= p0)) (PreH11 : (p0 <= UINT_MAX)) (PreH12 : (0 <= ql0)) (PreH13 : (ql0 <= 65536)) (PreH14 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH15 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH16 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |-> rhalf)
  **  ((( &( "p" ) )) # UInt  |-> p0)
  **  ((( &( "ql" ) )) # UInt  |-> ql0)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition mpn_invert_3by2_safety_wit_16 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : (0 <= p0)) (PreH11 : (p0 <= UINT_MAX)) (PreH12 : (0 <= ql0)) (PreH13 : (ql0 <= 65536)) (PreH14 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH15 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH16 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)))
  **  ((( &( "p" ) )) # UInt  |-> p0)
  **  ((( &( "ql" ) )) # UInt  |-> ql0)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_17 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : (0 <= p0)) (PreH11 : (p0 <= UINT_MAX)) (PreH12 : (0 <= ql0)) (PreH13 : (ql0 <= 65536)) (PreH14 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH15 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH16 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)))
  **  ((( &( "p" ) )) # UInt  |-> p0)
  **  ((( &( "ql" ) )) # UInt  |-> ql0)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_18 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (ql0: Z) (rpre: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= ql0)) (PreH8 : (ql0 <= 65536)) (PreH9 : (0 <= ((qh0 * 65536 ) + ql0 ))) (PreH10 : (((qh0 * 65536 ) + ql0 ) <= UINT_MAX)) (PreH11 : (0 <= rpre)) (PreH12 : (rpre < (2 * u1_pre ))) (PreH13 : ((((((qh0 * 65536 ) + ql0 ) + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH14 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "ql" ) )) # UInt  |-> ql0)
  **  ((( &( "r" ) )) # UInt  |-> rpre)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_19 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (ql0: Z) (rpre: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= ql0)) (PreH8 : (ql0 <= 65536)) (PreH9 : (0 <= ((qh0 * 65536 ) + ql0 ))) (PreH10 : (((qh0 * 65536 ) + ql0 ) <= UINT_MAX)) (PreH11 : (0 <= rpre)) (PreH12 : (rpre < (2 * u1_pre ))) (PreH13 : ((((((qh0 * 65536 ) + ql0 ) + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH14 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "ql" ) )) # UInt  |-> ql0)
  **  ((( &( "r" ) )) # UInt  |-> rpre)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition mpn_invert_3by2_safety_wit_20 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= m0)) (PreH6 : (m0 <= UINT_MAX)) (PreH7 : (0 <= r0)) (PreH8 : (r0 < u1_pre)) (PreH9 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "m" ) )) # UInt  |-> m0)
  **  ((( &( "r" ) )) # UInt  |-> r0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_invert_3by2_safety_wit_21 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (u0_pre > 0)) (PreH9 : (0 <= m1)) (PreH10 : (m1 <= UINT_MAX)) (PreH11 : (0 <= r1)) (PreH12 : (r1 <= UINT_MAX)) (PreH13 : (0 <= tlv)) (PreH14 : (tlv <= UINT_MAX)) (PreH15 : (0 <= thv)) (PreH16 : (thv <= UINT_MAX)) (PreH17 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH18 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH19 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH20 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "m" ) )) # UInt  |-> (unsigned_last_nbits ((m1 - 1 )) (32)))
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits ((r1 + thv )) (32)))
  **  ((( &( "tl" ) )) # UInt  |-> tlv)
  **  ((( &( "th" ) )) # UInt  |-> thv)
|--
  “ False ”
.

Definition mpn_invert_3by2_entail_wit_1 := 
(
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) ,
  ((( &( "qh" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |-> (Z.shiftr u1_pre 16))
  **  ((( &( "ul" ) )) # UInt  |-> (Z.land u1_pre 65535))
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
|--
  “ ((Z.shiftr u1_pre 16) <> 0) ” 
  &&  “ ((Z.land u1_pre 65535) <= UINT_MAX) ” 
  &&  “ (u0_pre >= 0) ” 
  &&  “ (u1_pre >= 0) ” 
  &&  “ ((Z.land u1_pre 65535) >= 0) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ”
  &&  ((( &( "uh" ) )) # UInt  |-> (Z.shiftr u1_pre 16))
  **  ((( &( "qh" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |-> (Z.land u1_pre 65535))
  **  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "m" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH2 : ((Z.shiftr u1_pre 16) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((Z.shiftr u1_pre 16) >= 0)) (PreH7 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH8 : (u1_pre <= UINT_MAX)) (PreH9 : (0 <= u0_pre)) (PreH10 : (u0_pre <= UINT_MAX)) ,
  TT && emp 
|--
  “ ((Z.shiftr u1_pre 16) <> 0) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_1_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH2 : ((Z.shiftr u1_pre 16) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((Z.shiftr u1_pre 16) >= 0)) (PreH7 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH8 : (u1_pre <= UINT_MAX)) (PreH9 : (0 <= u0_pre)) (PreH10 : (u0_pre <= UINT_MAX)) ,
  ((Z.shiftr u1_pre 16) <> 0)
.

Definition mpn_invert_3by2_entail_wit_2 := 
(
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.shiftr u1_pre 16) <> 0)) (PreH2 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH7 : (u1_pre <= UINT_MAX)) (PreH8 : (0 <= u0_pre)) (PreH9 : (u0_pre <= UINT_MAX)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ ((Z.land u1_pre 65535) = (Z.land u1_pre 65535)) ” 
  &&  “ ((Z.shiftr u1_pre 16) = (Z.shiftr u1_pre 16)) ” 
  &&  “ (((Z.lxor u1_pre UINT_MAX) ÷ (Z.shiftr u1_pre 16) ) = ((Z.lxor u1_pre UINT_MAX) ÷ (Z.shiftr u1_pre 16) )) ” 
  &&  “ (0 <= (Z.land u1_pre 65535)) ” 
  &&  “ ((Z.land u1_pre 65535) < 65536) ” 
  &&  “ (1 <= (Z.shiftr u1_pre 16)) ” 
  &&  “ ((Z.shiftr u1_pre 16) < 65536) ” 
  &&  “ (u1_pre = (((Z.shiftr u1_pre 16) * 65536 ) + (Z.land u1_pre 65535) )) ” 
  &&  “ (0 <= ((Z.lxor u1_pre UINT_MAX) ÷ (Z.shiftr u1_pre 16) )) ” 
  &&  “ (((Z.lxor u1_pre UINT_MAX) ÷ (Z.shiftr u1_pre 16) ) < 65536) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.shiftr u1_pre 16) <> 0)) (PreH2 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH7 : (u1_pre <= UINT_MAX)) (PreH8 : (0 <= u0_pre)) (PreH9 : (u0_pre <= UINT_MAX)) ,
  TT && emp 
|--
  “ (((Z.lxor u1_pre UINT_MAX) ÷ (Z.shiftr u1_pre 16) ) < 65536) ” 
  &&  “ (0 <= ((Z.lxor u1_pre UINT_MAX) ÷ (Z.shiftr u1_pre 16) )) ” 
  &&  “ (u1_pre = (((Z.shiftr u1_pre 16) * 65536 ) + (Z.land u1_pre 65535) )) ” 
  &&  “ ((Z.shiftr u1_pre 16) < 65536) ” 
  &&  “ (1 <= (Z.shiftr u1_pre 16)) ” 
  &&  “ ((Z.land u1_pre 65535) < 65536) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_2_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.shiftr u1_pre 16) <> 0)) (PreH2 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH7 : (u1_pre <= UINT_MAX)) (PreH8 : (0 <= u0_pre)) (PreH9 : (u0_pre <= UINT_MAX)) ,
  (((Z.lxor u1_pre UINT_MAX) ÷ (Z.shiftr u1_pre 16) ) < 65536)
.

Definition mpn_invert_3by2_entail_wit_2_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.shiftr u1_pre 16) <> 0)) (PreH2 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH7 : (u1_pre <= UINT_MAX)) (PreH8 : (0 <= u0_pre)) (PreH9 : (u0_pre <= UINT_MAX)) ,
  (0 <= ((Z.lxor u1_pre UINT_MAX) ÷ (Z.shiftr u1_pre 16) ))
.

Definition mpn_invert_3by2_entail_wit_2_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.shiftr u1_pre 16) <> 0)) (PreH2 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH7 : (u1_pre <= UINT_MAX)) (PreH8 : (0 <= u0_pre)) (PreH9 : (u0_pre <= UINT_MAX)) ,
  (u1_pre = (((Z.shiftr u1_pre 16) * 65536 ) + (Z.land u1_pre 65535) ))
.

Definition mpn_invert_3by2_entail_wit_2_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.shiftr u1_pre 16) <> 0)) (PreH2 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH7 : (u1_pre <= UINT_MAX)) (PreH8 : (0 <= u0_pre)) (PreH9 : (u0_pre <= UINT_MAX)) ,
  ((Z.shiftr u1_pre 16) < 65536)
.

Definition mpn_invert_3by2_entail_wit_2_split_goal_5 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.shiftr u1_pre 16) <> 0)) (PreH2 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH7 : (u1_pre <= UINT_MAX)) (PreH8 : (0 <= u0_pre)) (PreH9 : (u0_pre <= UINT_MAX)) ,
  (1 <= (Z.shiftr u1_pre 16))
.

Definition mpn_invert_3by2_entail_wit_2_split_goal_6 := 
forall (u0_pre: Z) (u1_pre: Z) (PreH1 : ((Z.shiftr u1_pre 16) <> 0)) (PreH2 : ((Z.land u1_pre 65535) <= UINT_MAX)) (PreH3 : (u0_pre >= 0)) (PreH4 : (u1_pre >= 0)) (PreH5 : ((Z.land u1_pre 65535) >= 0)) (PreH6 : ((UINT_MOD ÷ 2 ) <= u1_pre)) (PreH7 : (u1_pre <= UINT_MAX)) (PreH8 : (0 <= u0_pre)) (PreH9 : (u0_pre <= UINT_MAX)) ,
  ((Z.land u1_pre 65535) < 65536)
.

Definition mpn_invert_3by2_entail_wit_3_1 := 
(
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < (qh0 * ul0 ))) (PreH2 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= u1_pre)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (ul0 = (Z.land u1_pre 65535))) (PreH9 : (uh0 = (Z.shiftr u1_pre 16))) (PreH10 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH11 : (0 <= ul0)) (PreH12 : (ul0 < 65536)) (PreH13 : (1 <= uh0)) (PreH14 : (uh0 < 65536)) (PreH15 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH16 : (0 <= qh0)) (PreH17 : (qh0 < 65536)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "ul" ) )) # UInt  |-> ul0)
  **  ((( &( "uh" ) )) # UInt  |-> uh0)
  **  ((( &( "p" ) )) # UInt  |-> (qh0 * ul0 ))
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= ((qh0 - 1 ) - 1 )) ” 
  &&  “ (((qh0 - 1 ) - 1 ) < 65536) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) + u1_pre )) (32)) - (qh0 * ul0 ) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) + u1_pre )) (32)) - (qh0 * ul0 ) )) (32)) < u1_pre) ” 
  &&  “ ((((((qh0 - 1 ) - 1 ) + 65536 ) * u1_pre ) + (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) + u1_pre )) (32)) - (qh0 * ul0 ) )) (32)) ) = ((Z.pow (65536) (3)) - 1 )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < (qh0 * ul0 ))) (PreH2 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= u1_pre)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (ul0 = (Z.land u1_pre 65535))) (PreH9 : (uh0 = (Z.shiftr u1_pre 16))) (PreH10 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH11 : (0 <= ul0)) (PreH12 : (ul0 < 65536)) (PreH13 : (1 <= uh0)) (PreH14 : (uh0 < 65536)) (PreH15 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH16 : (0 <= qh0)) (PreH17 : (qh0 < 65536)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ ((((((((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) - 1 ) - 1 ) + 65536 ) * ((uh0 * 65536 ) + ul0 ) ) + (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32)) ) = ((Z.pow (65536) (3)) - 1 )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32)) < ((uh0 * 65536 ) + ul0 )) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32))) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_3_1_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < (qh0 * ul0 ))) (PreH2 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= u1_pre)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (ul0 = (Z.land u1_pre 65535))) (PreH9 : (uh0 = (Z.shiftr u1_pre 16))) (PreH10 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH11 : (0 <= ul0)) (PreH12 : (ul0 < 65536)) (PreH13 : (1 <= uh0)) (PreH14 : (uh0 < 65536)) (PreH15 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH16 : (0 <= qh0)) (PreH17 : (qh0 < 65536)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((((((((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) - 1 ) - 1 ) + 65536 ) * ((uh0 * 65536 ) + ul0 ) ) + (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32)) ) = ((Z.pow (65536) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_3_1_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < (qh0 * ul0 ))) (PreH2 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= u1_pre)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (ul0 = (Z.land u1_pre 65535))) (PreH9 : (uh0 = (Z.shiftr u1_pre 16))) (PreH10 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH11 : (0 <= ul0)) (PreH12 : (ul0 < 65536)) (PreH13 : (1 <= uh0)) (PreH14 : (uh0 < 65536)) (PreH15 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH16 : (0 <= qh0)) (PreH17 : (qh0 < 65536)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32)) < ((uh0 * 65536 ) + ul0 ))
.

Definition mpn_invert_3by2_entail_wit_3_1_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < (qh0 * ul0 ))) (PreH2 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= u1_pre)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (ul0 = (Z.land u1_pre 65535))) (PreH9 : (uh0 = (Z.shiftr u1_pre 16))) (PreH10 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH11 : (0 <= ul0)) (PreH12 : (ul0 < 65536)) (PreH13 : (1 <= uh0)) (PreH14 : (uh0 < 65536)) (PreH15 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH16 : (0 <= qh0)) (PreH17 : (qh0 < 65536)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32)))
.

Definition mpn_invert_3by2_entail_wit_3_2 := 
(
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= (qh0 * ul0 ))) (PreH2 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= u1_pre)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (ul0 = (Z.land u1_pre 65535))) (PreH9 : (uh0 = (Z.shiftr u1_pre 16))) (PreH10 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH11 : (0 <= ul0)) (PreH12 : (ul0 < 65536)) (PreH13 : (1 <= uh0)) (PreH14 : (uh0 < 65536)) (PreH15 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH16 : (0 <= qh0)) (PreH17 : (qh0 < 65536)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "ul" ) )) # UInt  |-> ul0)
  **  ((( &( "uh" ) )) # UInt  |-> uh0)
  **  ((( &( "p" ) )) # UInt  |-> (qh0 * ul0 ))
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= (qh0 - 1 )) ” 
  &&  “ ((qh0 - 1 ) < 65536) ” 
  &&  “ (0 <= ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) - (qh0 * ul0 ) )) ” 
  &&  “ (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) - (qh0 * ul0 ) ) < u1_pre) ” 
  &&  “ (((((qh0 - 1 ) + 65536 ) * u1_pre ) + ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) - (qh0 * ul0 ) ) ) = ((Z.pow (65536) (3)) - 1 )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= (qh0 * ul0 ))) (PreH2 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= u1_pre)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (ul0 = (Z.land u1_pre 65535))) (PreH9 : (uh0 = (Z.shiftr u1_pre 16))) (PreH10 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH11 : (0 <= ul0)) (PreH12 : (ul0 < 65536)) (PreH13 : (1 <= uh0)) (PreH14 : (uh0 < 65536)) (PreH15 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH16 : (0 <= qh0)) (PreH17 : (qh0 < 65536)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((((((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) - 1 ) + 65536 ) * ((uh0 * 65536 ) + ul0 ) ) + ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) ) ) = ((Z.pow (65536) (3)) - 1 )) ” 
  &&  “ (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) ) < ((uh0 * 65536 ) + ul0 )) ” 
  &&  “ (0 <= (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) - 1 )) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_3_2_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= (qh0 * ul0 ))) (PreH2 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= u1_pre)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (ul0 = (Z.land u1_pre 65535))) (PreH9 : (uh0 = (Z.shiftr u1_pre 16))) (PreH10 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH11 : (0 <= ul0)) (PreH12 : (ul0 < 65536)) (PreH13 : (1 <= uh0)) (PreH14 : (uh0 < 65536)) (PreH15 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH16 : (0 <= qh0)) (PreH17 : (qh0 < 65536)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((((((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) - 1 ) + 65536 ) * ((uh0 * 65536 ) + ul0 ) ) + ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) ) ) = ((Z.pow (65536) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_3_2_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= (qh0 * ul0 ))) (PreH2 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= u1_pre)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (ul0 = (Z.land u1_pre 65535))) (PreH9 : (uh0 = (Z.shiftr u1_pre 16))) (PreH10 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH11 : (0 <= ul0)) (PreH12 : (ul0 < 65536)) (PreH13 : (1 <= uh0)) (PreH14 : (uh0 < 65536)) (PreH15 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH16 : (0 <= qh0)) (PreH17 : (qh0 < 65536)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) ) < ((uh0 * 65536 ) + ul0 ))
.

Definition mpn_invert_3by2_entail_wit_3_2_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= (qh0 * ul0 ))) (PreH2 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) >= u1_pre)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (ul0 = (Z.land u1_pre 65535))) (PreH9 : (uh0 = (Z.shiftr u1_pre 16))) (PreH10 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH11 : (0 <= ul0)) (PreH12 : (ul0 < 65536)) (PreH13 : (1 <= uh0)) (PreH14 : (uh0 < 65536)) (PreH15 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH16 : (0 <= qh0)) (PreH17 : (qh0 < 65536)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_3_3 := 
(
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < u1_pre)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (ul0 = (Z.land u1_pre 65535))) (PreH8 : (uh0 = (Z.shiftr u1_pre 16))) (PreH9 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH10 : (0 <= ul0)) (PreH11 : (ul0 < 65536)) (PreH12 : (1 <= uh0)) (PreH13 : (uh0 < 65536)) (PreH14 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH15 : (0 <= qh0)) (PreH16 : (qh0 < 65536)) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "ul" ) )) # UInt  |-> ul0)
  **  ((( &( "uh" ) )) # UInt  |-> uh0)
  **  ((( &( "p" ) )) # UInt  |-> (qh0 * ul0 ))
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= (qh0 - 1 )) ” 
  &&  “ ((qh0 - 1 ) < 65536) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) - (qh0 * ul0 ) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) - (qh0 * ul0 ) )) (32)) < u1_pre) ” 
  &&  “ (((((qh0 - 1 ) + 65536 ) * u1_pre ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) - (qh0 * ul0 ) )) (32)) ) = ((Z.pow (65536) (3)) - 1 )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < u1_pre)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (ul0 = (Z.land u1_pre 65535))) (PreH8 : (uh0 = (Z.shiftr u1_pre 16))) (PreH9 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH10 : (0 <= ul0)) (PreH11 : (ul0 < 65536)) (PreH12 : (1 <= uh0)) (PreH13 : (uh0 < 65536)) (PreH14 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH15 : (0 <= qh0)) (PreH16 : (qh0 < 65536)) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((((((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) - 1 ) + 65536 ) * ((uh0 * 65536 ) + ul0 ) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32)) ) = ((Z.pow (65536) (3)) - 1 )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32)) < ((uh0 * 65536 ) + ul0 )) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32))) ” 
  &&  “ (0 <= (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) - 1 )) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_3_3_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < u1_pre)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (ul0 = (Z.land u1_pre 65535))) (PreH8 : (uh0 = (Z.shiftr u1_pre 16))) (PreH9 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH10 : (0 <= ul0)) (PreH11 : (ul0 < 65536)) (PreH12 : (1 <= uh0)) (PreH13 : (uh0 < 65536)) (PreH14 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH15 : (0 <= qh0)) (PreH16 : (qh0 < 65536)) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((((((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) - 1 ) + 65536 ) * ((uh0 * 65536 ) + ul0 ) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32)) ) = ((Z.pow (65536) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_3_3_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < u1_pre)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (ul0 = (Z.land u1_pre 65535))) (PreH8 : (uh0 = (Z.shiftr u1_pre 16))) (PreH9 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH10 : (0 <= ul0)) (PreH11 : (ul0 < 65536)) (PreH12 : (1 <= uh0)) (PreH13 : (uh0 < 65536)) (PreH14 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH15 : (0 <= qh0)) (PreH16 : (qh0 < 65536)) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32)) < ((uh0 * 65536 ) + ul0 ))
.

Definition mpn_invert_3by2_entail_wit_3_3_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < u1_pre)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (ul0 = (Z.land u1_pre 65535))) (PreH8 : (uh0 = (Z.shiftr u1_pre 16))) (PreH9 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH10 : (0 <= ul0)) (PreH11 : (ul0 < 65536)) (PreH12 : (1 <= uh0)) (PreH13 : (uh0 < 65536)) (PreH14 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH15 : (0 <= qh0)) (PreH16 : (qh0 < 65536)) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) + ((uh0 * 65536 ) + ul0 ) )) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) )) (32)))
.

Definition mpn_invert_3by2_entail_wit_3_3_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((unsigned_last_nbits (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) + u1_pre )) (32)) < u1_pre)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) < (qh0 * ul0 ))) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (ul0 = (Z.land u1_pre 65535))) (PreH8 : (uh0 = (Z.shiftr u1_pre 16))) (PreH9 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH10 : (0 <= ul0)) (PreH11 : (ul0 < 65536)) (PreH12 : (1 <= uh0)) (PreH13 : (uh0 < 65536)) (PreH14 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH15 : (0 <= qh0)) (PreH16 : (qh0 < 65536)) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_3_4 := 
(
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) >= (qh0 * ul0 ))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (ul0 = (Z.land u1_pre 65535))) (PreH7 : (uh0 = (Z.shiftr u1_pre 16))) (PreH8 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH9 : (0 <= ul0)) (PreH10 : (ul0 < 65536)) (PreH11 : (1 <= uh0)) (PreH12 : (uh0 < 65536)) (PreH13 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH14 : (0 <= qh0)) (PreH15 : (qh0 < 65536)) (PreH16 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "ul" ) )) # UInt  |-> ul0)
  **  ((( &( "uh" ) )) # UInt  |-> uh0)
  **  ((( &( "p" ) )) # UInt  |-> (qh0 * ul0 ))
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= qh0) ” 
  &&  “ (qh0 < 65536) ” 
  &&  “ (0 <= ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) - (qh0 * ul0 ) )) ” 
  &&  “ (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) - (qh0 * ul0 ) ) < u1_pre) ” 
  &&  “ ((((qh0 + 65536 ) * u1_pre ) + ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) - (qh0 * ul0 ) ) ) = ((Z.pow (65536) (3)) - 1 )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  ((( &( "p" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "uh" ) )) # UInt  |->_)
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) >= (qh0 * ul0 ))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (ul0 = (Z.land u1_pre 65535))) (PreH7 : (uh0 = (Z.shiftr u1_pre 16))) (PreH8 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH9 : (0 <= ul0)) (PreH10 : (ul0 < 65536)) (PreH11 : (1 <= uh0)) (PreH12 : (uh0 < 65536)) (PreH13 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH14 : (0 <= qh0)) (PreH15 : (qh0 < 65536)) (PreH16 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ ((((((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) + 65536 ) * ((uh0 * 65536 ) + ul0 ) ) + ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) ) ) = ((Z.pow (65536) (3)) - 1 )) ” 
  &&  “ (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) ) < ((uh0 * 65536 ) + ul0 )) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_3_4_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) >= (qh0 * ul0 ))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (ul0 = (Z.land u1_pre 65535))) (PreH7 : (uh0 = (Z.shiftr u1_pre 16))) (PreH8 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH9 : (0 <= ul0)) (PreH10 : (ul0 < 65536)) (PreH11 : (1 <= uh0)) (PreH12 : (uh0 < 65536)) (PreH13 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH14 : (0 <= qh0)) (PreH15 : (qh0 < 65536)) (PreH16 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((((((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) + 65536 ) * ((uh0 * 65536 ) + ul0 ) ) + ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) ) ) = ((Z.pow (65536) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_3_4_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (ul0: Z) (uh0: Z) (qh0: Z) (PreH1 : ((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot u1_pre)) (32)) - (qh0 * uh0 ) )) (32)) 16)) (32)) 65535) >= (qh0 * ul0 ))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (ul0 = (Z.land u1_pre 65535))) (PreH7 : (uh0 = (Z.shiftr u1_pre 16))) (PreH8 : (qh0 = ((Z.lxor u1_pre UINT_MAX) ÷ uh0 ))) (PreH9 : (0 <= ul0)) (PreH10 : (ul0 < 65536)) (PreH11 : (1 <= uh0)) (PreH12 : (uh0 < 65536)) (PreH13 : (u1_pre = ((uh0 * 65536 ) + ul0 ))) (PreH14 : (0 <= qh0)) (PreH15 : (qh0 < 65536)) (PreH16 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((Z.lor (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot ((uh0 * 65536 ) + ul0 ))) (32)) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.shiftr ((uh0 * 65536 ) + ul0 ) 16) ) )) (32)) 16)) (32)) 65535) - (((Z.lxor ((uh0 * 65536 ) + ul0 ) UINT_MAX) ÷ uh0 ) * (Z.land ((uh0 * 65536 ) + ul0 ) 65535) ) ) < ((uh0 * 65536 ) + ul0 ))
.

Definition mpn_invert_3by2_entail_wit_4 := 
(
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= qh0) ” 
  &&  “ (qh0 < 65536) ” 
  &&  “ (0 <= rhalf) ” 
  &&  “ (rhalf < u1_pre) ” 
  &&  “ ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 )) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) (32)) <= 65536) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) = (((Z.shiftr rhalf 16) * qh0 ) + rhalf )) ” 
  &&  “ ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) (32)) = ((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) (32)) = ((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) = (((Z.shiftr rhalf 16) * qh0 ) + rhalf )) ” 
  &&  “ ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) (32)) <= 65536) ” 
  &&  “ (0 <= (unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32))) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_4_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) (32)) = ((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 ))
.

Definition mpn_invert_3by2_entail_wit_4_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))
.

Definition mpn_invert_3by2_entail_wit_4_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) (32)) <= 65536)
.

Definition mpn_invert_3by2_entail_wit_4_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) 16) + 1 )) (32)))
.

Definition mpn_invert_3by2_entail_wit_4_split_goal_5 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_4_split_goal_6 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= rhalf)) (PreH8 : (rhalf < u1_pre)) (PreH9 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH10 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr rhalf 16) * qh0 )) (32)) + rhalf )) (32)))
.

Definition mpn_invert_3by2_entail_wit_5_1 := 
(
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) >= (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "p" ) )) # UInt  |-> p0)
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= qh0) ” 
  &&  “ (qh0 < 65536) ” 
  &&  “ (0 <= (unsigned_last_nbits ((ql0 - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((ql0 - 1 )) (32)) <= 65536) ” 
  &&  “ (0 <= ((qh0 * 65536 ) + (unsigned_last_nbits ((ql0 - 1 )) (32)) )) ” 
  &&  “ (((qh0 * 65536 ) + (unsigned_last_nbits ((ql0 - 1 )) (32)) ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) + u1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) + u1_pre )) (32)) < (2 * u1_pre )) ” 
  &&  “ ((((((qh0 * 65536 ) + (unsigned_last_nbits ((ql0 - 1 )) (32)) ) + UINT_MOD ) * u1_pre ) + (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) + u1_pre )) (32)) ) = ((Z.pow (UINT_MOD) (2)) - 1 )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  ((( &( "p" ) )) # UInt  |->_)
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) >= (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ ((((((qh0 * 65536 ) + (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) - 1 )) (32)) ) + UINT_MOD ) * u1_pre ) + (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)) + u1_pre )) (32)) ) = ((Z.pow (UINT_MOD) (2)) - 1 )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)) + u1_pre )) (32)) < (2 * u1_pre )) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)) + u1_pre )) (32))) ” 
  &&  “ (((qh0 * 65536 ) + (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) - 1 )) (32)) ) <= UINT_MAX) ” 
  &&  “ (0 <= ((qh0 * 65536 ) + (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) - 1 )) (32)) )) ” 
  &&  “ ((unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) - 1 )) (32)) <= 65536) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) - 1 )) (32))) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_5_1_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) >= (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((((((qh0 * 65536 ) + (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) - 1 )) (32)) ) + UINT_MOD ) * u1_pre ) + (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)) + u1_pre )) (32)) ) = ((Z.pow (UINT_MOD) (2)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_5_1_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) >= (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)) + u1_pre )) (32)) < (2 * u1_pre ))
.

Definition mpn_invert_3by2_entail_wit_5_1_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) >= (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)) + u1_pre )) (32)))
.

Definition mpn_invert_3by2_entail_wit_5_1_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) >= (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((qh0 * 65536 ) + (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) - 1 )) (32)) ) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_5_1_split_goal_5 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) >= (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= ((qh0 * 65536 ) + (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) - 1 )) (32)) ))
.

Definition mpn_invert_3by2_entail_wit_5_1_split_goal_6 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) >= (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) - 1 )) (32)) <= 65536)
.

Definition mpn_invert_3by2_entail_wit_5_1_split_goal_7 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) >= (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) - 1 )) (32)))
.

Definition mpn_invert_3by2_entail_wit_5_2 := 
(
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) < (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "p" ) )) # UInt  |-> p0)
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= qh0) ” 
  &&  “ (qh0 < 65536) ” 
  &&  “ (0 <= ql0) ” 
  &&  “ (ql0 <= 65536) ” 
  &&  “ (0 <= ((qh0 * 65536 ) + ql0 )) ” 
  &&  “ (((qh0 * 65536 ) + ql0 ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) < (2 * u1_pre )) ” 
  &&  “ ((((((qh0 * 65536 ) + ql0 ) + UINT_MOD ) * u1_pre ) + (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) ) = ((Z.pow (UINT_MOD) (2)) - 1 )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  ((( &( "p" ) )) # UInt  |->_)
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) < (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ ((((((qh0 * 65536 ) + ((Z.shiftr p0 16) + 1 ) ) + UINT_MOD ) * u1_pre ) + (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)) ) = ((Z.pow (UINT_MOD) (2)) - 1 )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)) < (2 * u1_pre )) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32))) ” 
  &&  “ (((qh0 * 65536 ) + ((Z.shiftr p0 16) + 1 ) ) <= UINT_MAX) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_5_2_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) < (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((((((qh0 * 65536 ) + ((Z.shiftr p0 16) + 1 ) ) + UINT_MOD ) * u1_pre ) + (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)) ) = ((Z.pow (UINT_MOD) (2)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_5_2_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) < (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)) < (2 * u1_pre ))
.

Definition mpn_invert_3by2_entail_wit_5_2_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) < (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((((Z.shiftr p0 16) + 1 ) * u1_pre )) (32)) )) (32)))
.

Definition mpn_invert_3by2_entail_wit_5_2_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (rhalf: Z) (p0: Z) (ql0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl rhalf 16)) (32)) + 65535 )) (32)) - (unsigned_last_nbits ((ql0 * u1_pre )) (32)) )) (32)) < (Z.land UINT_MAX (Z.shiftl p0 16)))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= qh0)) (PreH7 : (qh0 < 65536)) (PreH8 : (0 <= rhalf)) (PreH9 : (rhalf < u1_pre)) (PreH10 : ((((qh0 + 65536 ) * u1_pre ) + rhalf ) = ((Z.pow (65536) (3)) - 1 ))) (PreH11 : (0 <= p0)) (PreH12 : (p0 <= UINT_MAX)) (PreH13 : (0 <= ql0)) (PreH14 : (ql0 <= 65536)) (PreH15 : (p0 = (((Z.shiftr rhalf 16) * qh0 ) + rhalf ))) (PreH16 : (ql0 = ((Z.shiftr p0 16) + 1 ))) (PreH17 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((qh0 * 65536 ) + ((Z.shiftr p0 16) + 1 ) ) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_6 := 
(
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (ql0: Z) (rpre: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= ql0)) (PreH8 : (ql0 <= 65536)) (PreH9 : (0 <= ((qh0 * 65536 ) + ql0 ))) (PreH10 : (((qh0 * 65536 ) + ql0 ) <= UINT_MAX)) (PreH11 : (0 <= rpre)) (PreH12 : (rpre < (2 * u1_pre ))) (PreH13 : ((((((qh0 * 65536 ) + ql0 ) + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH14 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "qh" ) )) # UInt  |-> qh0)
  **  ((( &( "ql" ) )) # UInt  |-> ql0)
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl qh0 16)) (32)) + ql0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl qh0 16)) (32)) + ql0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= rpre) ” 
  &&  “ (rpre < (2 * u1_pre )) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl qh0 16)) (32)) + ql0 )) (32)) + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  ((( &( "ql" ) )) # UInt  |->_)
  **  ((( &( "qh" ) )) # UInt  |->_)
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (ql0: Z) (rpre: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= ql0)) (PreH8 : (ql0 <= 65536)) (PreH9 : (0 <= ((qh0 * 65536 ) + ql0 ))) (PreH10 : (((qh0 * 65536 ) + ql0 ) <= UINT_MAX)) (PreH11 : (0 <= rpre)) (PreH12 : (rpre < (2 * u1_pre ))) (PreH13 : ((((((qh0 * 65536 ) + ql0 ) + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH14 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl qh0 16)) (32)) + ql0 )) (32)) + UINT_MOD ) * u1_pre ) + rpre ) = (((((qh0 * 65536 ) + ql0 ) + UINT_MOD ) * u1_pre ) + rpre )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl qh0 16)) (32)) + ql0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl qh0 16)) (32)) + ql0 )) (32))) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_6_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (ql0: Z) (rpre: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= ql0)) (PreH8 : (ql0 <= 65536)) (PreH9 : (0 <= ((qh0 * 65536 ) + ql0 ))) (PreH10 : (((qh0 * 65536 ) + ql0 ) <= UINT_MAX)) (PreH11 : (0 <= rpre)) (PreH12 : (rpre < (2 * u1_pre ))) (PreH13 : ((((((qh0 * 65536 ) + ql0 ) + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH14 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl qh0 16)) (32)) + ql0 )) (32)) + UINT_MOD ) * u1_pre ) + rpre ) = (((((qh0 * 65536 ) + ql0 ) + UINT_MOD ) * u1_pre ) + rpre ))
.

Definition mpn_invert_3by2_entail_wit_6_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (ql0: Z) (rpre: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= ql0)) (PreH8 : (ql0 <= 65536)) (PreH9 : (0 <= ((qh0 * 65536 ) + ql0 ))) (PreH10 : (((qh0 * 65536 ) + ql0 ) <= UINT_MAX)) (PreH11 : (0 <= rpre)) (PreH12 : (rpre < (2 * u1_pre ))) (PreH13 : ((((((qh0 * 65536 ) + ql0 ) + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH14 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl qh0 16)) (32)) + ql0 )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_6_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (qh0: Z) (ql0: Z) (rpre: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= qh0)) (PreH6 : (qh0 < 65536)) (PreH7 : (0 <= ql0)) (PreH8 : (ql0 <= 65536)) (PreH9 : (0 <= ((qh0 * 65536 ) + ql0 ))) (PreH10 : (((qh0 * 65536 ) + ql0 ) <= UINT_MAX)) (PreH11 : (0 <= rpre)) (PreH12 : (rpre < (2 * u1_pre ))) (PreH13 : ((((((qh0 * 65536 ) + ql0 ) + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH14 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl qh0 16)) (32)) + ql0 )) (32)))
.

Definition mpn_invert_3by2_entail_wit_7_1 := 
(
forall (u0_pre: Z) (u1_pre: Z) (mpre: Z) (rpre: Z) (PreH1 : (rpre >= u1_pre)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= mpre)) (PreH7 : (mpre <= UINT_MAX)) (PreH8 : (0 <= rpre)) (PreH9 : (rpre < (2 * u1_pre ))) (PreH10 : ((((mpre + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((mpre + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((mpre + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (rpre - u1_pre )) ” 
  &&  “ ((rpre - u1_pre ) < u1_pre) ” 
  &&  “ (((((unsigned_last_nbits ((mpre + 1 )) (32)) + UINT_MOD ) * u1_pre ) + (rpre - u1_pre ) ) = ((Z.pow (UINT_MOD) (2)) - 1 )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (mpre: Z) (rpre: Z) (PreH1 : (rpre >= u1_pre)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= mpre)) (PreH7 : (mpre <= UINT_MAX)) (PreH8 : (0 <= rpre)) (PreH9 : (rpre < (2 * u1_pre ))) (PreH10 : ((((mpre + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((((unsigned_last_nbits ((mpre + 1 )) (32)) + UINT_MOD ) * u1_pre ) + (rpre - u1_pre ) ) = (((mpre + UINT_MOD ) * u1_pre ) + rpre )) ” 
  &&  “ ((unsigned_last_nbits ((mpre + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((mpre + 1 )) (32))) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_7_1_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (mpre: Z) (rpre: Z) (PreH1 : (rpre >= u1_pre)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= mpre)) (PreH7 : (mpre <= UINT_MAX)) (PreH8 : (0 <= rpre)) (PreH9 : (rpre < (2 * u1_pre ))) (PreH10 : ((((mpre + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((((unsigned_last_nbits ((mpre + 1 )) (32)) + UINT_MOD ) * u1_pre ) + (rpre - u1_pre ) ) = (((mpre + UINT_MOD ) * u1_pre ) + rpre ))
.

Definition mpn_invert_3by2_entail_wit_7_1_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (mpre: Z) (rpre: Z) (PreH1 : (rpre >= u1_pre)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= mpre)) (PreH7 : (mpre <= UINT_MAX)) (PreH8 : (0 <= rpre)) (PreH9 : (rpre < (2 * u1_pre ))) (PreH10 : ((((mpre + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits ((mpre + 1 )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_7_1_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (mpre: Z) (rpre: Z) (PreH1 : (rpre >= u1_pre)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= mpre)) (PreH7 : (mpre <= UINT_MAX)) (PreH8 : (0 <= rpre)) (PreH9 : (rpre < (2 * u1_pre ))) (PreH10 : ((((mpre + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits ((mpre + 1 )) (32)))
.

Definition mpn_invert_3by2_entail_wit_7_2 := 
forall (u0_pre: Z) (u1_pre: Z) (mpre: Z) (rpre: Z) (PreH1 : (rpre < u1_pre)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= mpre)) (PreH7 : (mpre <= UINT_MAX)) (PreH8 : (0 <= rpre)) (PreH9 : (rpre < (2 * u1_pre ))) (PreH10 : ((((mpre + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= mpre) ” 
  &&  “ (mpre <= UINT_MAX) ” 
  &&  “ (0 <= rpre) ” 
  &&  “ (rpre < u1_pre) ” 
  &&  “ ((((mpre + UINT_MOD ) * u1_pre ) + rpre ) = ((Z.pow (UINT_MOD) (2)) - 1 )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
.

Definition mpn_invert_3by2_entail_wit_8_1 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m0 - 1 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((m0 - 1 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits ((m0 - 1 )) (32)) - 1 )) (32)) + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32)) ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre )) ” 
  &&  “ (((UINT_MOD - 1 ) - (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32)) ) < u1_pre) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((UINT_MOD - 1 ) - (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32)) ) < u1_pre) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits ((m0 - 1 )) (32)) - 1 )) (32)) + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32)) ) ) = ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) - u0_pre )) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((m0 - 1 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m0 - 1 )) (32)) - 1 )) (32))) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_8_1_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((UINT_MOD - 1 ) - (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32)) ) < u1_pre)
.

Definition mpn_invert_3by2_entail_wit_8_1_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((((unsigned_last_nbits (((unsigned_last_nbits ((m0 - 1 )) (32)) - 1 )) (32)) + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32)) ) ) = ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) - u0_pre ))
.

Definition mpn_invert_3by2_entail_wit_8_1_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_8_1_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre ) - u1_pre )) (32)))
.

Definition mpn_invert_3by2_entail_wit_8_1_split_goal_5 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((m0 - 1 )) (32)) - 1 )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_8_1_split_goal_6 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m0 - 1 )) (32)) - 1 )) (32)))
.

Definition mpn_invert_3by2_entail_wit_8_2 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= (unsigned_last_nbits ((m0 - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((m0 - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ (((((unsigned_last_nbits ((m0 - 1 )) (32)) + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32)) ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre )) ” 
  &&  “ (((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32)) ) < u1_pre) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32)) ) < u1_pre) ” 
  &&  “ (((((unsigned_last_nbits ((m0 - 1 )) (32)) + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32)) ) ) = ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) - u0_pre )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((m0 - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((m0 - 1 )) (32))) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_8_2_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32)) ) < u1_pre)
.

Definition mpn_invert_3by2_entail_wit_8_2_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((((unsigned_last_nbits ((m0 - 1 )) (32)) + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32)) ) ) = ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) - u0_pre ))
.

Definition mpn_invert_3by2_entail_wit_8_2_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_8_2_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) - u1_pre )) (32)))
.

Definition mpn_invert_3by2_entail_wit_8_2_split_goal_5 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits ((m0 - 1 )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_8_2_split_goal_6 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u1_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) < u0_pre)) (PreH3 : (u0_pre > 0)) (PreH4 : (0 <= u1_pre)) (PreH5 : (u1_pre <= UINT_MAX)) (PreH6 : (0 <= u0_pre)) (PreH7 : (u0_pre <= UINT_MAX)) (PreH8 : (0 <= m0)) (PreH9 : (m0 <= UINT_MAX)) (PreH10 : (0 <= r0)) (PreH11 : (r0 < u1_pre)) (PreH12 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits ((m0 - 1 )) (32)))
.

Definition mpn_invert_3by2_entail_wit_8_3 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u0_pre)) (PreH2 : (u0_pre > 0)) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (0 <= m0)) (PreH8 : (m0 <= UINT_MAX)) (PreH9 : (0 <= r0)) (PreH10 : (r0 < u1_pre)) (PreH11 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= m0) ” 
  &&  “ (m0 <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((((m0 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre )) ” 
  &&  “ (((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) ) < u1_pre) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u0_pre)) (PreH2 : (u0_pre > 0)) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (0 <= m0)) (PreH8 : (m0 <= UINT_MAX)) (PreH9 : (0 <= r0)) (PreH10 : (r0 < u1_pre)) (PreH11 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) ) < u1_pre) ” 
  &&  “ ((((m0 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) ) ) = ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) - u0_pre )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) <= UINT_MAX) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_8_3_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u0_pre)) (PreH2 : (u0_pre > 0)) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (0 <= m0)) (PreH8 : (m0 <= UINT_MAX)) (PreH9 : (0 <= r0)) (PreH10 : (r0 < u1_pre)) (PreH11 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) ) < u1_pre)
.

Definition mpn_invert_3by2_entail_wit_8_3_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u0_pre)) (PreH2 : (u0_pre > 0)) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (0 <= m0)) (PreH8 : (m0 <= UINT_MAX)) (PreH9 : (0 <= r0)) (PreH10 : (r0 < u1_pre)) (PreH11 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((((m0 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - (unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) ) ) = ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) - u0_pre ))
.

Definition mpn_invert_3by2_entail_wit_8_3_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) >= u0_pre)) (PreH2 : (u0_pre > 0)) (PreH3 : (0 <= u1_pre)) (PreH4 : (u1_pre <= UINT_MAX)) (PreH5 : (0 <= u0_pre)) (PreH6 : (u0_pre <= UINT_MAX)) (PreH7 : (0 <= m0)) (PreH8 : (m0 <= UINT_MAX)) (PreH9 : (0 <= r0)) (PreH10 : (r0 < u1_pre)) (PreH11 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH12 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((Z.lnot r0)) (32)) + u0_pre )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_9 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (((w1_value * UINT_MOD ) + w0_value ) = (u0_pre * m1 ))) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (u0_pre > 0)) (PreH7 : (0 <= m1)) (PreH8 : (m1 <= UINT_MAX)) (PreH9 : (0 <= r1)) (PreH10 : (r1 <= UINT_MAX)) (PreH11 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH12 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH13 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "tl" ) )) # UInt  |-> w0_value)
  **  ((( &( "th" ) )) # UInt  |-> w1_value)
  **  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "m" ) )) # UInt  |-> m1)
  **  ((( &( "r" ) )) # UInt  |-> r1)
|--
  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (r1 >= 0) ” 
  &&  “ (m1 >= 0) ” 
  &&  “ (u0_pre >= 0) ” 
  &&  “ (u1_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (u0_pre * m1 )) ” 
  &&  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= m1) ” 
  &&  “ (m1 <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre )) ” 
  &&  “ (((UINT_MOD - 1 ) - r1 ) < u1_pre) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  ((( &( "tl" ) )) # UInt  |-> w0_value)
  **  ((( &( "th" ) )) # UInt  |-> w1_value)
  **  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "m" ) )) # UInt  |-> m1)
  **  ((( &( "r" ) )) # UInt  |-> r1)
.

Definition mpn_invert_3by2_entail_wit_10 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w0_value)) (PreH2 : (w0_value <= UINT_MAX)) (PreH3 : (w1_value <= UINT_MAX)) (PreH4 : (r1 >= 0)) (PreH5 : (m1 >= 0)) (PreH6 : (u0_pre >= 0)) (PreH7 : (u1_pre >= 0)) (PreH8 : (w1_value >= 0)) (PreH9 : (((w1_value * UINT_MOD ) + w0_value ) = (u0_pre * m1 ))) (PreH10 : (0 <= u1_pre)) (PreH11 : (u1_pre <= UINT_MAX)) (PreH12 : (0 <= u0_pre)) (PreH13 : (u0_pre <= UINT_MAX)) (PreH14 : (u0_pre > 0)) (PreH15 : (0 <= m1)) (PreH16 : (m1 <= UINT_MAX)) (PreH17 : (0 <= r1)) (PreH18 : (r1 <= UINT_MAX)) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((( &( "tl" ) )) # UInt  |-> w0_value)
  **  ((( &( "th" ) )) # UInt  |-> w1_value)
  **  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "m" ) )) # UInt  |-> m1)
  **  ((( &( "r" ) )) # UInt  |-> r1)
|--
  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (r1 >= 0) ” 
  &&  “ (m1 >= 0) ” 
  &&  “ (u0_pre >= 0) ” 
  &&  “ (u1_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (u0_pre * m1 )) ” 
  &&  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= m1) ” 
  &&  “ (m1 <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre )) ” 
  &&  “ (((UINT_MOD - 1 ) - r1 ) < u1_pre) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  ((( &( "th" ) )) # UInt  |-> w1_value)
  **  ((( &( "tl" ) )) # UInt  |-> w0_value)
  **  ((( &( "u1" ) )) # UInt  |-> u1_pre)
  **  ((( &( "u0" ) )) # UInt  |-> u0_pre)
  **  ((( &( "m" ) )) # UInt  |-> m1)
  **  ((( &( "r" ) )) # UInt  |-> r1)
.

Definition mpn_invert_3by2_entail_wit_11 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w1_value)) (PreH2 : (w1_value <= UINT_MAX)) (PreH3 : (w0_value >= 0)) (PreH4 : (0 <= w0_value)) (PreH5 : (w0_value <= UINT_MAX)) (PreH6 : (w1_value <= UINT_MAX)) (PreH7 : (r1 >= 0)) (PreH8 : (m1 >= 0)) (PreH9 : (u0_pre >= 0)) (PreH10 : (u1_pre >= 0)) (PreH11 : (w1_value >= 0)) (PreH12 : (((w1_value * UINT_MOD ) + w0_value ) = (u0_pre * m1 ))) (PreH13 : (0 <= u1_pre)) (PreH14 : (u1_pre <= UINT_MAX)) (PreH15 : (0 <= u0_pre)) (PreH16 : (u0_pre <= UINT_MAX)) (PreH17 : (u0_pre > 0)) (PreH18 : (0 <= m1)) (PreH19 : (m1 <= UINT_MAX)) (PreH20 : (0 <= r1)) (PreH21 : (r1 <= UINT_MAX)) (PreH22 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH23 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH24 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= m1) ” 
  &&  “ (m1 <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (u0_pre * m1 )) ” 
  &&  “ ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre )) ” 
  &&  “ (((UINT_MOD - 1 ) - r1 ) < u1_pre) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
.

Definition mpn_invert_3by2_entail_wit_12_1 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= ((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) )) ” 
  &&  “ (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((r1 + thv )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((r1 + thv )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= tlv) ” 
  &&  “ (tlv <= UINT_MAX) ” 
  &&  “ (0 <= thv) ” 
  &&  “ (thv <= UINT_MAX) ” 
  &&  “ (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) ) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) ) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) ) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) ) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((r1 + thv )) (32))) ” 
  &&  “ (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) ) <= UINT_MAX) ” 
  &&  “ (0 <= ((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) )) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_12_1_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((Z.pow (UINT_MOD) (3)) - 1 ) < (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) ) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) ))
.

Definition mpn_invert_3by2_entail_wit_12_1_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) ) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_12_1_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits ((r1 + thv )) (32)))
.

Definition mpn_invert_3by2_entail_wit_12_1_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) ) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_12_1_split_goal_5 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= ((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 0)) ))
.

Definition mpn_invert_3by2_entail_wit_12_2 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= ((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) )) ” 
  &&  “ (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((r1 + thv )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((r1 + thv )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= tlv) ” 
  &&  “ (tlv <= UINT_MAX) ” 
  &&  “ (0 <= thv) ” 
  &&  “ (thv <= UINT_MAX) ” 
  &&  “ (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) ) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) ) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) ) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) ) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((r1 + thv )) (32))) ” 
  &&  “ (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) ) <= UINT_MAX) ” 
  &&  “ (0 <= ((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) )) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_12_2_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((Z.pow (UINT_MOD) (3)) - 1 ) < (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) ) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) ))
.

Definition mpn_invert_3by2_entail_wit_12_2_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) ) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_12_2_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits ((r1 + thv )) (32)))
.

Definition mpn_invert_3by2_entail_wit_12_2_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) ) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_12_2_split_goal_5 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= ((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 0 1)) ))
.

Definition mpn_invert_3by2_entail_wit_12_3 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= ((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) )) ” 
  &&  “ (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((r1 + thv )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((r1 + thv )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= tlv) ” 
  &&  “ (tlv <= UINT_MAX) ” 
  &&  “ (0 <= thv) ” 
  &&  “ (thv <= UINT_MAX) ” 
  &&  “ (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) ) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) ) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) ) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) ) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) ) <= UINT_MAX) ” 
  &&  “ (0 <= ((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) )) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_12_3_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((Z.pow (UINT_MOD) (3)) - 1 ) < (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) ) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) ))
.

Definition mpn_invert_3by2_entail_wit_12_3_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) ) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_12_3_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) ) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_12_3_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= ((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 0)) ))
.

Definition mpn_invert_3by2_entail_wit_12_4 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((r1 + thv )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((r1 + thv )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= tlv) ” 
  &&  “ (tlv <= UINT_MAX) ” 
  &&  “ (0 <= thv) ” 
  &&  “ (thv <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32)) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32)) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32)) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32)) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32))) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_12_4_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((Z.pow (UINT_MOD) (3)) - 1 ) < ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32)) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) ))
.

Definition mpn_invert_3by2_entail_wit_12_4_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32)) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_12_4_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_12_4_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) = u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) <= u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 0 (Z.land 1 1)) )) (32)))
.

Definition mpn_invert_3by2_entail_wit_12_5 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((r1 + thv )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((r1 + thv )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= tlv) ” 
  &&  “ (tlv <= UINT_MAX) ” 
  &&  “ (0 <= thv) ” 
  &&  “ (thv <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32)) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32)) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32)) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32)) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32))) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_12_5_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((Z.pow (UINT_MOD) (3)) - 1 ) < ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32)) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) ))
.

Definition mpn_invert_3by2_entail_wit_12_5_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32)) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_12_5_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_12_5_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv <= u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 0)) )) (32)))
.

Definition mpn_invert_3by2_entail_wit_12_6 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((r1 + thv )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((r1 + thv )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= tlv) ” 
  &&  “ (tlv <= UINT_MAX) ” 
  &&  “ (0 <= thv) ” 
  &&  “ (thv <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32)) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32)) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32)) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32)) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32))) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_12_6_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((Z.pow (UINT_MOD) (3)) - 1 ) < ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32)) + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) ))
.

Definition mpn_invert_3by2_entail_wit_12_6_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32)) + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_12_6_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_12_6_split_goal_4 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : (tlv > u0_pre)) (PreH2 : ((unsigned_last_nbits ((r1 + thv )) (32)) <> u1_pre)) (PreH3 : ((unsigned_last_nbits ((r1 + thv )) (32)) > u1_pre)) (PreH4 : ((unsigned_last_nbits ((r1 + thv )) (32)) < thv)) (PreH5 : (0 <= u1_pre)) (PreH6 : (u1_pre <= UINT_MAX)) (PreH7 : (0 <= u0_pre)) (PreH8 : (u0_pre <= UINT_MAX)) (PreH9 : (u0_pre > 0)) (PreH10 : (0 <= m1)) (PreH11 : (m1 <= UINT_MAX)) (PreH12 : (0 <= r1)) (PreH13 : (r1 <= UINT_MAX)) (PreH14 : (0 <= tlv)) (PreH15 : (tlv <= UINT_MAX)) (PreH16 : (0 <= thv)) (PreH17 : (thv <= UINT_MAX)) (PreH18 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH19 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH20 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH21 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((m1 - 1 )) (32)) - (Z.lor 1 (Z.land 0 1)) )) (32)))
.

Definition mpn_invert_3by2_entail_wit_12_7 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : ((unsigned_last_nbits ((r1 + thv )) (32)) >= thv)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (u0_pre > 0)) (PreH7 : (0 <= m1)) (PreH8 : (m1 <= UINT_MAX)) (PreH9 : (0 <= r1)) (PreH10 : (r1 <= UINT_MAX)) (PreH11 : (0 <= tlv)) (PreH12 : (tlv <= UINT_MAX)) (PreH13 : (0 <= thv)) (PreH14 : (thv <= UINT_MAX)) (PreH15 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH16 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH17 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= m1) ” 
  &&  “ (m1 <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((r1 + thv )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((r1 + thv )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= tlv) ” 
  &&  “ (tlv <= UINT_MAX) ” 
  &&  “ (0 <= thv) ” 
  &&  “ (thv <= UINT_MAX) ” 
  &&  “ (((m1 + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((m1 + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : ((unsigned_last_nbits ((r1 + thv )) (32)) >= thv)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (u0_pre > 0)) (PreH7 : (0 <= m1)) (PreH8 : (m1 <= UINT_MAX)) (PreH9 : (0 <= r1)) (PreH10 : (r1 <= UINT_MAX)) (PreH11 : (0 <= tlv)) (PreH12 : (tlv <= UINT_MAX)) (PreH13 : (0 <= thv)) (PreH14 : (thv <= UINT_MAX)) (PreH15 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH16 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH17 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((m1 + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ (((m1 + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ ((unsigned_last_nbits ((r1 + thv )) (32)) <= UINT_MAX) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_12_7_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : ((unsigned_last_nbits ((r1 + thv )) (32)) >= thv)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (u0_pre > 0)) (PreH7 : (0 <= m1)) (PreH8 : (m1 <= UINT_MAX)) (PreH9 : (0 <= r1)) (PreH10 : (r1 <= UINT_MAX)) (PreH11 : (0 <= tlv)) (PreH12 : (tlv <= UINT_MAX)) (PreH13 : (0 <= thv)) (PreH14 : (thv <= UINT_MAX)) (PreH15 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH16 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH17 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((Z.pow (UINT_MOD) (3)) - 1 ) < (((m1 + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) ))
.

Definition mpn_invert_3by2_entail_wit_12_7_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : ((unsigned_last_nbits ((r1 + thv )) (32)) >= thv)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (u0_pre > 0)) (PreH7 : (0 <= m1)) (PreH8 : (m1 <= UINT_MAX)) (PreH9 : (0 <= r1)) (PreH10 : (r1 <= UINT_MAX)) (PreH11 : (0 <= tlv)) (PreH12 : (tlv <= UINT_MAX)) (PreH13 : (0 <= thv)) (PreH14 : (thv <= UINT_MAX)) (PreH15 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH16 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH17 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((m1 + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))
.

Definition mpn_invert_3by2_entail_wit_12_7_split_goal_3 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (tlv: Z) (thv: Z) (PreH1 : ((unsigned_last_nbits ((r1 + thv )) (32)) >= thv)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (u0_pre > 0)) (PreH7 : (0 <= m1)) (PreH8 : (m1 <= UINT_MAX)) (PreH9 : (0 <= r1)) (PreH10 : (r1 <= UINT_MAX)) (PreH11 : (0 <= tlv)) (PreH12 : (tlv <= UINT_MAX)) (PreH13 : (0 <= thv)) (PreH14 : (thv <= UINT_MAX)) (PreH15 : (((thv * UINT_MOD ) + tlv ) = (u0_pre * m1 ))) (PreH16 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH17 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH18 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  ((unsigned_last_nbits ((r1 + thv )) (32)) <= UINT_MAX)
.

Definition mpn_invert_3by2_entail_wit_13_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m2: Z) (r2: Z) (tlv: Z) (thv: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (u0_pre > 0)) (PreH6 : (0 <= m2)) (PreH7 : (m2 <= UINT_MAX)) (PreH8 : (0 <= r2)) (PreH9 : (r2 <= UINT_MAX)) (PreH10 : (0 <= tlv)) (PreH11 : (tlv <= UINT_MAX)) (PreH12 : (0 <= thv)) (PreH13 : (thv <= UINT_MAX)) (PreH14 : (((m2 + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((m2 + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) ))) (PreH16 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= m2) ” 
  &&  “ (m2 <= UINT_MAX) ” 
  &&  “ (0 <= r2) ” 
  &&  “ (r2 <= UINT_MAX) ” 
  &&  “ (((m2 + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((m2 + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
.

Definition mpn_invert_3by2_entail_wit_13_2 := 
(
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : (u0_pre <= 0)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= m0)) (PreH7 : (m0 <= UINT_MAX)) (PreH8 : (0 <= r0)) (PreH9 : (r0 < u1_pre)) (PreH10 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (0 <= m0) ” 
  &&  “ (m0 <= UINT_MAX) ” 
  &&  “ (0 <= r0) ” 
  &&  “ (r0 <= UINT_MAX) ” 
  &&  “ (((m0 + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((m0 + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
) \/
(
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : (u0_pre <= 0)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= m0)) (PreH7 : (m0 <= UINT_MAX)) (PreH8 : (0 <= r0)) (PreH9 : (r0 < u1_pre)) (PreH10 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((m0 + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ” 
  &&  “ (((m0 + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ”
  &&  emp
).

Definition mpn_invert_3by2_entail_wit_13_2_split_goal_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : (u0_pre <= 0)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= m0)) (PreH7 : (m0 <= UINT_MAX)) (PreH8 : (0 <= r0)) (PreH9 : (r0 < u1_pre)) (PreH10 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((Z.pow (UINT_MOD) (3)) - 1 ) < (((m0 + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) ))
.

Definition mpn_invert_3by2_entail_wit_13_2_split_goal_2 := 
forall (u0_pre: Z) (u1_pre: Z) (m0: Z) (r0: Z) (PreH1 : (u0_pre <= 0)) (PreH2 : (0 <= u1_pre)) (PreH3 : (u1_pre <= UINT_MAX)) (PreH4 : (0 <= u0_pre)) (PreH5 : (u0_pre <= UINT_MAX)) (PreH6 : (0 <= m0)) (PreH7 : (m0 <= UINT_MAX)) (PreH8 : (0 <= r0)) (PreH9 : (r0 < u1_pre)) (PreH10 : ((((m0 + UINT_MOD ) * u1_pre ) + r0 ) = ((Z.pow (UINT_MOD) (2)) - 1 ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  (((m0 + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))
.

Definition mpn_invert_3by2_return_wit_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m3: Z) (r3: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (0 <= m3)) (PreH6 : (m3 <= UINT_MAX)) (PreH7 : (0 <= r3)) (PreH8 : (r3 <= UINT_MAX)) (PreH9 : (((m3 + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH10 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((m3 + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) ))) (PreH11 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= m3) ” 
  &&  “ (m3 <= UINT_MAX) ” 
  &&  “ (((m3 + UINT_MOD ) * ((UINT_MOD * u1_pre ) + u0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((m3 + UINT_MOD ) + 1 ) * ((UINT_MOD * u1_pre ) + u0_pre ) )) ”
  &&  emp
.

Definition mpn_invert_3by2_partial_solve_wit_1 := 
forall (u0_pre: Z) (u1_pre: Z) (m1: Z) (r1: Z) (PreH1 : (0 <= u1_pre)) (PreH2 : (u1_pre <= UINT_MAX)) (PreH3 : (0 <= u0_pre)) (PreH4 : (u0_pre <= UINT_MAX)) (PreH5 : (u0_pre > 0)) (PreH6 : (0 <= m1)) (PreH7 : (m1 <= UINT_MAX)) (PreH8 : (0 <= r1)) (PreH9 : (r1 <= UINT_MAX)) (PreH10 : ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre ))) (PreH11 : (((UINT_MOD - 1 ) - r1 ) < u1_pre)) (PreH12 : ((UINT_MOD ÷ 2 ) <= u1_pre)) ,
  TT && emp 
|--
  “ (0 <= u1_pre) ” 
  &&  “ (u1_pre <= UINT_MAX) ” 
  &&  “ (0 <= u0_pre) ” 
  &&  “ (u0_pre <= UINT_MAX) ” 
  &&  “ (u0_pre > 0) ” 
  &&  “ (0 <= m1) ” 
  &&  “ (m1 <= UINT_MAX) ” 
  &&  “ (0 <= r1) ” 
  &&  “ (r1 <= UINT_MAX) ” 
  &&  “ ((((m1 + UINT_MOD ) * u1_pre ) + ((UINT_MOD - 1 ) - r1 ) ) = (((Z.pow (UINT_MOD) (2)) - 1 ) - u0_pre )) ” 
  &&  “ (((UINT_MOD - 1 ) - r1 ) < u1_pre) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= u1_pre) ”
  &&  emp
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_invert_3by2_safety_wit_1 : mpn_invert_3by2_safety_wit_1.
Axiom proof_of_mpn_invert_3by2_safety_wit_2 : mpn_invert_3by2_safety_wit_2.
Axiom proof_of_mpn_invert_3by2_safety_wit_3 : mpn_invert_3by2_safety_wit_3.
Axiom proof_of_mpn_invert_3by2_safety_wit_4 : mpn_invert_3by2_safety_wit_4.
Axiom proof_of_mpn_invert_3by2_safety_wit_5 : mpn_invert_3by2_safety_wit_5.
Axiom proof_of_mpn_invert_3by2_safety_wit_6 : mpn_invert_3by2_safety_wit_6.
Axiom proof_of_mpn_invert_3by2_safety_wit_7 : mpn_invert_3by2_safety_wit_7.
Axiom proof_of_mpn_invert_3by2_safety_wit_8 : mpn_invert_3by2_safety_wit_8.
Axiom proof_of_mpn_invert_3by2_safety_wit_9 : mpn_invert_3by2_safety_wit_9.
Axiom proof_of_mpn_invert_3by2_safety_wit_10 : mpn_invert_3by2_safety_wit_10.
Axiom proof_of_mpn_invert_3by2_safety_wit_11 : mpn_invert_3by2_safety_wit_11.
Axiom proof_of_mpn_invert_3by2_safety_wit_12 : mpn_invert_3by2_safety_wit_12.
Axiom proof_of_mpn_invert_3by2_safety_wit_13 : mpn_invert_3by2_safety_wit_13.
Axiom proof_of_mpn_invert_3by2_safety_wit_14 : mpn_invert_3by2_safety_wit_14.
Axiom proof_of_mpn_invert_3by2_safety_wit_15 : mpn_invert_3by2_safety_wit_15.
Axiom proof_of_mpn_invert_3by2_safety_wit_16 : mpn_invert_3by2_safety_wit_16.
Axiom proof_of_mpn_invert_3by2_safety_wit_17 : mpn_invert_3by2_safety_wit_17.
Axiom proof_of_mpn_invert_3by2_safety_wit_18 : mpn_invert_3by2_safety_wit_18.
Axiom proof_of_mpn_invert_3by2_safety_wit_19 : mpn_invert_3by2_safety_wit_19.
Axiom proof_of_mpn_invert_3by2_safety_wit_20 : mpn_invert_3by2_safety_wit_20.
Axiom proof_of_mpn_invert_3by2_safety_wit_21 : mpn_invert_3by2_safety_wit_21.
Axiom proof_of_mpn_invert_3by2_entail_wit_1 : mpn_invert_3by2_entail_wit_1.
Axiom proof_of_mpn_invert_3by2_entail_wit_2 : mpn_invert_3by2_entail_wit_2.
Axiom proof_of_mpn_invert_3by2_entail_wit_3_1 : mpn_invert_3by2_entail_wit_3_1.
Axiom proof_of_mpn_invert_3by2_entail_wit_3_2 : mpn_invert_3by2_entail_wit_3_2.
Axiom proof_of_mpn_invert_3by2_entail_wit_3_3 : mpn_invert_3by2_entail_wit_3_3.
Axiom proof_of_mpn_invert_3by2_entail_wit_3_4 : mpn_invert_3by2_entail_wit_3_4.
Axiom proof_of_mpn_invert_3by2_entail_wit_4 : mpn_invert_3by2_entail_wit_4.
Axiom proof_of_mpn_invert_3by2_entail_wit_5_1 : mpn_invert_3by2_entail_wit_5_1.
Axiom proof_of_mpn_invert_3by2_entail_wit_5_2 : mpn_invert_3by2_entail_wit_5_2.
Axiom proof_of_mpn_invert_3by2_entail_wit_6 : mpn_invert_3by2_entail_wit_6.
Axiom proof_of_mpn_invert_3by2_entail_wit_7_1 : mpn_invert_3by2_entail_wit_7_1.
Axiom proof_of_mpn_invert_3by2_entail_wit_7_2 : mpn_invert_3by2_entail_wit_7_2.
Axiom proof_of_mpn_invert_3by2_entail_wit_8_1 : mpn_invert_3by2_entail_wit_8_1.
Axiom proof_of_mpn_invert_3by2_entail_wit_8_2 : mpn_invert_3by2_entail_wit_8_2.
Axiom proof_of_mpn_invert_3by2_entail_wit_8_3 : mpn_invert_3by2_entail_wit_8_3.
Axiom proof_of_mpn_invert_3by2_entail_wit_9 : mpn_invert_3by2_entail_wit_9.
Axiom proof_of_mpn_invert_3by2_entail_wit_10 : mpn_invert_3by2_entail_wit_10.
Axiom proof_of_mpn_invert_3by2_entail_wit_11 : mpn_invert_3by2_entail_wit_11.
Axiom proof_of_mpn_invert_3by2_entail_wit_12_1 : mpn_invert_3by2_entail_wit_12_1.
Axiom proof_of_mpn_invert_3by2_entail_wit_12_2 : mpn_invert_3by2_entail_wit_12_2.
Axiom proof_of_mpn_invert_3by2_entail_wit_12_3 : mpn_invert_3by2_entail_wit_12_3.
Axiom proof_of_mpn_invert_3by2_entail_wit_12_4 : mpn_invert_3by2_entail_wit_12_4.
Axiom proof_of_mpn_invert_3by2_entail_wit_12_5 : mpn_invert_3by2_entail_wit_12_5.
Axiom proof_of_mpn_invert_3by2_entail_wit_12_6 : mpn_invert_3by2_entail_wit_12_6.
Axiom proof_of_mpn_invert_3by2_entail_wit_12_7 : mpn_invert_3by2_entail_wit_12_7.
Axiom proof_of_mpn_invert_3by2_entail_wit_13_1 : mpn_invert_3by2_entail_wit_13_1.
Axiom proof_of_mpn_invert_3by2_entail_wit_13_2 : mpn_invert_3by2_entail_wit_13_2.
Axiom proof_of_mpn_invert_3by2_return_wit_1 : mpn_invert_3by2_return_wit_1.
Axiom proof_of_mpn_invert_3by2_partial_solve_wit_1 : mpn_invert_3by2_partial_solve_wit_1.

End VC_Correct.
