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

(*----- Function gmp_udiv_qrnnd_preinv -----*)

Definition gmp_udiv_qrnnd_preinv_safety_wit_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w1_value)) (PreH2 : (w1_value <= UINT_MAX)) (PreH3 : (w0_value >= 0)) (PreH4 : (0 <= w0_value)) (PreH5 : (w0_value <= UINT_MAX)) (PreH6 : (nh_pre <= UINT_MAX)) (PreH7 : (w1_value <= UINT_MAX)) (PreH8 : (di_pre >= 0)) (PreH9 : (d_pre >= 0)) (PreH10 : (nl_pre >= 0)) (PreH11 : (nh_pre >= 0)) (PreH12 : (w1_value >= 0)) (PreH13 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH14 : (0 <= nh_pre)) (PreH15 : (nh_pre < d_pre)) (PreH16 : (0 <= nl_pre)) (PreH17 : (nl_pre <= UINT_MAX)) (PreH18 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH19 : (d_pre <= UINT_MAX)) (PreH20 : (0 <= di_pre)) (PreH21 : (di_pre <= UINT_MAX)) (PreH22 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH23 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((( &( "qh" ) )) # UInt  |-> w1_value)
  **  ((( &( "ql" ) )) # UInt  |-> w0_value)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + nl_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "rr" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "nh" ) )) # UInt  |-> nh_pre)
  **  ((( &( "nl" ) )) # UInt  |-> nl_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "di" ) )) # UInt  |-> di_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gmp_udiv_qrnnd_preinv_safety_wit_2 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH2 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH3 : (0 <= w1_value)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : (w0_value >= 0)) (PreH6 : (0 <= w0_value)) (PreH7 : (w0_value <= UINT_MAX)) (PreH8 : (nh_pre <= UINT_MAX)) (PreH9 : (w1_value <= UINT_MAX)) (PreH10 : (di_pre >= 0)) (PreH11 : (d_pre >= 0)) (PreH12 : (nl_pre >= 0)) (PreH13 : (nh_pre >= 0)) (PreH14 : (w1_value >= 0)) (PreH15 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH16 : (0 <= nh_pre)) (PreH17 : (nh_pre < d_pre)) (PreH18 : (0 <= nl_pre)) (PreH19 : (nl_pre <= UINT_MAX)) (PreH20 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH21 : (d_pre <= UINT_MAX)) (PreH22 : (0 <= di_pre)) (PreH23 : (di_pre <= UINT_MAX)) (PreH24 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH25 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((( &( "qh" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)))
  **  ((( &( "ql" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + nl_pre )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + nl_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "rr" ) )) # UInt  |-> (unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)))
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "nh" ) )) # UInt  |-> nh_pre)
  **  ((( &( "nl" ) )) # UInt  |-> nl_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "di" ) )) # UInt  |-> di_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition gmp_udiv_qrnnd_preinv_safety_wit_3 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH2 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH3 : (0 <= w1_value)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : (w0_value >= 0)) (PreH6 : (0 <= w0_value)) (PreH7 : (w0_value <= UINT_MAX)) (PreH8 : (nh_pre <= UINT_MAX)) (PreH9 : (w1_value <= UINT_MAX)) (PreH10 : (di_pre >= 0)) (PreH11 : (d_pre >= 0)) (PreH12 : (nl_pre >= 0)) (PreH13 : (nh_pre >= 0)) (PreH14 : (w1_value >= 0)) (PreH15 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH16 : (0 <= nh_pre)) (PreH17 : (nh_pre < d_pre)) (PreH18 : (0 <= nl_pre)) (PreH19 : (nl_pre <= UINT_MAX)) (PreH20 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH21 : (d_pre <= UINT_MAX)) (PreH22 : (0 <= di_pre)) (PreH23 : (di_pre <= UINT_MAX)) (PreH24 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH25 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((( &( "qh" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)))
  **  ((( &( "ql" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + nl_pre )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + nl_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "rr" ) )) # UInt  |-> (unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)))
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "nh" ) )) # UInt  |-> nh_pre)
  **  ((( &( "nl" ) )) # UInt  |-> nl_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "di" ) )) # UInt  |-> di_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
|--
  “ (0 <> (INT_MIN)) ”
.

Definition gmp_udiv_qrnnd_preinv_safety_wit_4 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH2 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH3 : (0 <= w1_value)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : (w0_value >= 0)) (PreH6 : (0 <= w0_value)) (PreH7 : (w0_value <= UINT_MAX)) (PreH8 : (nh_pre <= UINT_MAX)) (PreH9 : (w1_value <= UINT_MAX)) (PreH10 : (di_pre >= 0)) (PreH11 : (d_pre >= 0)) (PreH12 : (nl_pre >= 0)) (PreH13 : (nh_pre >= 0)) (PreH14 : (w1_value >= 0)) (PreH15 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH16 : (0 <= nh_pre)) (PreH17 : (nh_pre < d_pre)) (PreH18 : (0 <= nl_pre)) (PreH19 : (nl_pre <= UINT_MAX)) (PreH20 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH21 : (d_pre <= UINT_MAX)) (PreH22 : (0 <= di_pre)) (PreH23 : (di_pre <= UINT_MAX)) (PreH24 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH25 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((( &( "qh" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)))
  **  ((( &( "ql" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + nl_pre )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + nl_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "rr" ) )) # UInt  |-> (unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)))
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "nh" ) )) # UInt  |-> nh_pre)
  **  ((( &( "nl" ) )) # UInt  |-> nl_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "di" ) )) # UInt  |-> di_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition gmp_udiv_qrnnd_preinv_safety_wit_5 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH2 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH3 : (0 <= w1_value)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : (w0_value >= 0)) (PreH6 : (0 <= w0_value)) (PreH7 : (w0_value <= UINT_MAX)) (PreH8 : (nh_pre <= UINT_MAX)) (PreH9 : (w1_value <= UINT_MAX)) (PreH10 : (di_pre >= 0)) (PreH11 : (d_pre >= 0)) (PreH12 : (nl_pre >= 0)) (PreH13 : (nh_pre >= 0)) (PreH14 : (w1_value >= 0)) (PreH15 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH16 : (0 <= nh_pre)) (PreH17 : (nh_pre < d_pre)) (PreH18 : (0 <= nl_pre)) (PreH19 : (nl_pre <= UINT_MAX)) (PreH20 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH21 : (d_pre <= UINT_MAX)) (PreH22 : (0 <= di_pre)) (PreH23 : (di_pre <= UINT_MAX)) (PreH24 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH25 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((( &( "qh" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)))
  **  ((( &( "ql" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + nl_pre )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + nl_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "rr" ) )) # UInt  |-> (unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)))
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "nh" ) )) # UInt  |-> nh_pre)
  **  ((( &( "nl" ) )) # UInt  |-> nl_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "di" ) )) # UInt  |-> di_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
|--
  “ (0 <> (INT_MIN)) ”
.

Definition gmp_udiv_qrnnd_preinv_entail_wit_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH2 : (0 <= nh_pre)) (PreH3 : (nh_pre < d_pre)) (PreH4 : (0 <= nl_pre)) (PreH5 : (nl_pre <= UINT_MAX)) (PreH6 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH7 : (d_pre <= UINT_MAX)) (PreH8 : (0 <= di_pre)) (PreH9 : (di_pre <= UINT_MAX)) (PreH10 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH11 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((( &( "ql" ) )) # UInt  |-> w0_value)
  **  ((( &( "qh" ) )) # UInt  |-> w1_value)
  **  ((( &( "x" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "rr" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "nh" ) )) # UInt  |-> nh_pre)
  **  ((( &( "nl" ) )) # UInt  |-> nl_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "di" ) )) # UInt  |-> di_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
|--
  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (nh_pre <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (di_pre >= 0) ” 
  &&  “ (d_pre >= 0) ” 
  &&  “ (nl_pre >= 0) ” 
  &&  “ (nh_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre )) ” 
  &&  “ (0 <= nh_pre) ” 
  &&  “ (nh_pre < d_pre) ” 
  &&  “ (0 <= nl_pre) ” 
  &&  “ (nl_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d_pre) ” 
  &&  “ (d_pre <= UINT_MAX) ” 
  &&  “ (0 <= di_pre) ” 
  &&  “ (di_pre <= UINT_MAX) ” 
  &&  “ (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) )) ”
  &&  ((( &( "ql" ) )) # UInt  |-> w0_value)
  **  ((( &( "qh" ) )) # UInt  |-> w1_value)
  **  ((( &( "x" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "rr" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "nh" ) )) # UInt  |-> nh_pre)
  **  ((( &( "nl" ) )) # UInt  |-> nl_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "di" ) )) # UInt  |-> di_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
.

Definition gmp_udiv_qrnnd_preinv_entail_wit_2 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w0_value)) (PreH2 : (w0_value <= UINT_MAX)) (PreH3 : (nh_pre <= UINT_MAX)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : (di_pre >= 0)) (PreH6 : (d_pre >= 0)) (PreH7 : (nl_pre >= 0)) (PreH8 : (nh_pre >= 0)) (PreH9 : (w1_value >= 0)) (PreH10 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH11 : (0 <= nh_pre)) (PreH12 : (nh_pre < d_pre)) (PreH13 : (0 <= nl_pre)) (PreH14 : (nl_pre <= UINT_MAX)) (PreH15 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH16 : (d_pre <= UINT_MAX)) (PreH17 : (0 <= di_pre)) (PreH18 : (di_pre <= UINT_MAX)) (PreH19 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH20 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((( &( "ql" ) )) # UInt  |-> w0_value)
  **  ((( &( "qh" ) )) # UInt  |-> w1_value)
  **  ((( &( "x" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "rr" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "nh" ) )) # UInt  |-> nh_pre)
  **  ((( &( "nl" ) )) # UInt  |-> nl_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "di" ) )) # UInt  |-> di_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
|--
  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (nh_pre <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (di_pre >= 0) ” 
  &&  “ (d_pre >= 0) ” 
  &&  “ (nl_pre >= 0) ” 
  &&  “ (nh_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre )) ” 
  &&  “ (0 <= nh_pre) ” 
  &&  “ (nh_pre < d_pre) ” 
  &&  “ (0 <= nl_pre) ” 
  &&  “ (nl_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d_pre) ” 
  &&  “ (d_pre <= UINT_MAX) ” 
  &&  “ (0 <= di_pre) ” 
  &&  “ (di_pre <= UINT_MAX) ” 
  &&  “ (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) )) ”
  &&  ((( &( "qh" ) )) # UInt  |-> w1_value)
  **  ((( &( "ql" ) )) # UInt  |-> w0_value)
  **  ((( &( "x" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "rr" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "nh" ) )) # UInt  |-> nh_pre)
  **  ((( &( "nl" ) )) # UInt  |-> nl_pre)
  **  ((( &( "d" ) )) # UInt  |-> d_pre)
  **  ((( &( "di" ) )) # UInt  |-> di_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_1 := 
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((q_pre) # UInt  |-> (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) + 1 )) (32)))
  **  ((r_pre) # UInt  |-> ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) - d_pre ))
|--
  EX (rv: Z)  (qv: Z) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_pre) ” 
  &&  “ (((nh_pre * UINT_MOD ) + nl_pre ) = ((qv * d_pre ) + rv )) ”
  &&  ((q_pre) # UInt  |-> qv)
  **  ((r_pre) # UInt  |-> rv)
) \/
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  TT && emp 
|--
  “ (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) + 1 )) (32)) * d_pre ) + ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) - d_pre ) )) ” 
  &&  “ (((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) - d_pre ) < d_pre) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) + 1 )) (32)) * d_pre ) + ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) - d_pre ) ))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_2 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) - d_pre ) < d_pre)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_3 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_1_split_goal_4 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) + 1 )) (32)))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_2 := 
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((q_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)))
  **  ((r_pre) # UInt  |-> ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) - d_pre ))
|--
  EX (rv: Z)  (qv: Z) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_pre) ” 
  &&  “ (((nh_pre * UINT_MOD ) + nl_pre ) = ((qv * d_pre ) + rv )) ”
  &&  ((q_pre) # UInt  |-> qv)
  **  ((r_pre) # UInt  |-> rv)
) \/
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  TT && emp 
|--
  “ (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)) * d_pre ) + ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) - d_pre ) )) ” 
  &&  “ (((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) - d_pre ) < d_pre) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)) * d_pre ) + ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) - d_pre ) ))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_2 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) - d_pre ) < d_pre)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_3 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_2_split_goal_4 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_3 := 
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((q_pre) # UInt  |-> (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) + 1 )) (32)))
  **  ((r_pre) # UInt  |-> ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) - d_pre ))
|--
  EX (rv: Z)  (qv: Z) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_pre) ” 
  &&  “ (((nh_pre * UINT_MOD ) + nl_pre ) = ((qv * d_pre ) + rv )) ”
  &&  ((q_pre) # UInt  |-> qv)
  **  ((r_pre) # UInt  |-> rv)
) \/
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  TT && emp 
|--
  “ (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) + 1 )) (32)) * d_pre ) + ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) - d_pre ) )) ” 
  &&  “ (((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) - d_pre ) < d_pre) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) + 1 )) (32)) * d_pre ) + ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) - d_pre ) ))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_2 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) - d_pre ) < d_pre)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_3 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_3_split_goal_4 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) + 1 )) (32)))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_4 := 
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((q_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)))
  **  ((r_pre) # UInt  |-> ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) - d_pre ))
|--
  EX (rv: Z)  (qv: Z) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_pre) ” 
  &&  “ (((nh_pre * UINT_MOD ) + nl_pre ) = ((qv * d_pre ) + rv )) ”
  &&  ((q_pre) # UInt  |-> qv)
  **  ((r_pre) # UInt  |-> rv)
) \/
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  TT && emp 
|--
  “ (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)) * d_pre ) + ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) - d_pre ) )) ” 
  &&  “ (((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) - d_pre ) < d_pre) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)) * d_pre ) + ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) - d_pre ) ))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_2 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) - d_pre ) < d_pre)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_3 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_4_split_goal_4 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) >= d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) + 1 )) (32)))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_5 := 
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((q_pre) # UInt  |-> ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ))
  **  ((r_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)))
|--
  EX (rv: Z)  (qv: Z) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_pre) ” 
  &&  “ (((nh_pre * UINT_MOD ) + nl_pre ) = ((qv * d_pre ) + rv )) ”
  &&  ((q_pre) # UInt  |-> qv)
  **  ((r_pre) # UInt  |-> rv)
) \/
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  TT && emp 
|--
  “ (((nh_pre * UINT_MOD ) + nl_pre ) = ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) * d_pre ) + (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) )) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32))) ” 
  &&  “ (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) <= UINT_MAX) ” 
  &&  “ (0 <= ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) )) ”
  &&  emp
).

Definition gmp_udiv_qrnnd_preinv_return_wit_5_split_goal_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((nh_pre * UINT_MOD ) + nl_pre ) = ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) * d_pre ) + (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) ))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_5_split_goal_2 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_5_split_goal_3 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ) <= UINT_MAX)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_5_split_goal_4 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (-0) ))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_6 := 
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((q_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)))
  **  ((r_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)))
|--
  EX (rv: Z)  (qv: Z) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_pre) ” 
  &&  “ (((nh_pre * UINT_MOD ) + nl_pre ) = ((qv * d_pre ) + rv )) ”
  &&  ((q_pre) # UInt  |-> qv)
  **  ((r_pre) # UInt  |-> rv)
) \/
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  TT && emp 
|--
  “ (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) * d_pre ) + (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) )) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) * d_pre ) + (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) ))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_2 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_3 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_6_split_goal_4 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 0 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_7 := 
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((q_pre) # UInt  |-> ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ))
  **  ((r_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)))
|--
  EX (rv: Z)  (qv: Z) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_pre) ” 
  &&  “ (((nh_pre * UINT_MOD ) + nl_pre ) = ((qv * d_pre ) + rv )) ”
  &&  ((q_pre) # UInt  |-> qv)
  **  ((r_pre) # UInt  |-> rv)
) \/
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  TT && emp 
|--
  “ (((nh_pre * UINT_MOD ) + nl_pre ) = ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) * d_pre ) + (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) )) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32))) ” 
  &&  “ (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) <= UINT_MAX) ” 
  &&  “ (0 <= ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) )) ”
  &&  emp
).

Definition gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((nh_pre * UINT_MOD ) + nl_pre ) = ((((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) * d_pre ) + (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) ))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_2 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_3 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ) <= UINT_MAX)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_7_split_goal_4 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-0) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) <= (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (-0) ))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_8 := 
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((q_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)))
  **  ((r_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)))
|--
  EX (rv: Z)  (qv: Z) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (rv < d_pre) ” 
  &&  “ (((nh_pre * UINT_MOD ) + nl_pre ) = ((qv * d_pre ) + rv )) ”
  &&  ((q_pre) # UInt  |-> qv)
  **  ((r_pre) # UInt  |-> rv)
) \/
(
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  TT && emp 
|--
  “ (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) * d_pre ) + (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) )) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (((nh_pre * UINT_MOD ) + nl_pre ) = (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) * d_pre ) + (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) ))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_2 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)))
.

Definition gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_3 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qrnnd_preinv_return_wit_8_split_goal_4 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) + (Z.land (-1) d_pre) )) (32)) < d_pre)) (PreH2 : ((unsigned_last_nbits ((nl_pre - (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) * d_pre )) (32)) )) (32)) > (unsigned_last_nbits ((w0_value + nl_pre )) (32)))) (PreH3 : ((unsigned_last_nbits ((w0_value + nl_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (nh_pre <= UINT_MAX)) (PreH10 : (w1_value <= UINT_MAX)) (PreH11 : (di_pre >= 0)) (PreH12 : (d_pre >= 0)) (PreH13 : (nl_pre >= 0)) (PreH14 : (nh_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (nh_pre * di_pre ))) (PreH17 : (0 <= nh_pre)) (PreH18 : (nh_pre < d_pre)) (PreH19 : (0 <= nl_pre)) (PreH20 : (nl_pre <= UINT_MAX)) (PreH21 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH22 : (d_pre <= UINT_MAX)) (PreH23 : (0 <= di_pre)) (PreH24 : (di_pre <= UINT_MAX)) (PreH25 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + (nh_pre + 1 ) )) (32)) + 1 )) (32)) + (unsigned_last_nbits ((-1)) (32)) )) (32)))
.

Definition gmp_udiv_qrnnd_preinv_partial_solve_wit_1 := 
forall (di_pre: Z) (d_pre: Z) (nl_pre: Z) (nh_pre: Z) (r_pre: Z) (q_pre: Z) (PreH1 : (0 <= nh_pre)) (PreH2 : (nh_pre < d_pre)) (PreH3 : (0 <= nl_pre)) (PreH4 : (nl_pre <= UINT_MAX)) (PreH5 : ((UINT_MOD ÷ 2 ) <= d_pre)) (PreH6 : (d_pre <= UINT_MAX)) (PreH7 : (0 <= di_pre)) (PreH8 : (di_pre <= UINT_MAX)) (PreH9 : (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH10 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
|--
  “ (0 <= nh_pre) ” 
  &&  “ (nh_pre < d_pre) ” 
  &&  “ (0 <= nl_pre) ” 
  &&  “ (nl_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d_pre) ” 
  &&  “ (d_pre <= UINT_MAX) ” 
  &&  “ (0 <= di_pre) ” 
  &&  “ (di_pre <= UINT_MAX) ” 
  &&  “ (((di_pre + UINT_MOD ) * (UINT_MOD * d_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((di_pre + UINT_MOD ) + 1 ) * (UINT_MOD * d_pre ) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r_pre) # UInt  |->_)
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_gmp_udiv_qrnnd_preinv_safety_wit_1 : gmp_udiv_qrnnd_preinv_safety_wit_1.
Axiom proof_of_gmp_udiv_qrnnd_preinv_safety_wit_2 : gmp_udiv_qrnnd_preinv_safety_wit_2.
Axiom proof_of_gmp_udiv_qrnnd_preinv_safety_wit_3 : gmp_udiv_qrnnd_preinv_safety_wit_3.
Axiom proof_of_gmp_udiv_qrnnd_preinv_safety_wit_4 : gmp_udiv_qrnnd_preinv_safety_wit_4.
Axiom proof_of_gmp_udiv_qrnnd_preinv_safety_wit_5 : gmp_udiv_qrnnd_preinv_safety_wit_5.
Axiom proof_of_gmp_udiv_qrnnd_preinv_entail_wit_1 : gmp_udiv_qrnnd_preinv_entail_wit_1.
Axiom proof_of_gmp_udiv_qrnnd_preinv_entail_wit_2 : gmp_udiv_qrnnd_preinv_entail_wit_2.
Axiom proof_of_gmp_udiv_qrnnd_preinv_return_wit_1 : gmp_udiv_qrnnd_preinv_return_wit_1.
Axiom proof_of_gmp_udiv_qrnnd_preinv_return_wit_2 : gmp_udiv_qrnnd_preinv_return_wit_2.
Axiom proof_of_gmp_udiv_qrnnd_preinv_return_wit_3 : gmp_udiv_qrnnd_preinv_return_wit_3.
Axiom proof_of_gmp_udiv_qrnnd_preinv_return_wit_4 : gmp_udiv_qrnnd_preinv_return_wit_4.
Axiom proof_of_gmp_udiv_qrnnd_preinv_return_wit_5 : gmp_udiv_qrnnd_preinv_return_wit_5.
Axiom proof_of_gmp_udiv_qrnnd_preinv_return_wit_6 : gmp_udiv_qrnnd_preinv_return_wit_6.
Axiom proof_of_gmp_udiv_qrnnd_preinv_return_wit_7 : gmp_udiv_qrnnd_preinv_return_wit_7.
Axiom proof_of_gmp_udiv_qrnnd_preinv_return_wit_8 : gmp_udiv_qrnnd_preinv_return_wit_8.
Axiom proof_of_gmp_udiv_qrnnd_preinv_partial_solve_wit_1 : gmp_udiv_qrnnd_preinv_partial_solve_wit_1.

End VC_Correct.
