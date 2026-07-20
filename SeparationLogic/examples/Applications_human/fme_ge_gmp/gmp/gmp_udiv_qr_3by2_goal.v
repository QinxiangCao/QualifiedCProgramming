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

(*----- Function gmp_udiv_qr_3by2 -----*)

Definition gmp_udiv_qr_3by2_safety_wit_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 < qlo)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ (0 <> (INT_MIN)) ”
.

Definition gmp_udiv_qr_3by2_safety_wit_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 < qlo)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition gmp_udiv_qr_3by2_safety_wit_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition gmp_udiv_qr_3by2_safety_wit_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition gmp_udiv_qr_3by2_safety_wit_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition gmp_udiv_qr_3by2_safety_wit_6 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition gmp_udiv_qr_3by2_safety_wit_7 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 < qlo)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ (0 <> (INT_MIN)) ”
.

Definition gmp_udiv_qr_3by2_safety_wit_8 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 < qlo)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition gmp_udiv_qr_3by2_safety_wit_9 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition gmp_udiv_qr_3by2_safety_wit_10 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition gmp_udiv_qr_3by2_safety_wit_11 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition gmp_udiv_qr_3by2_safety_wit_12 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> qpre)
  **  ((( &( "rv1" ) )) # UInt  |-> rpre1)
  **  ((( &( "rv0" ) )) # UInt  |-> rpre0)
  **  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
|--
  “ False ”
.

Definition gmp_udiv_qr_3by2_safety_wit_13 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid0 >= d0_pre)) (PreH3 : (rmid1 <= d1_pre)) (PreH4 : (rmid1 >= d1_pre)) (PreH5 : (0 <= n2_pre)) (PreH6 : (n2_pre <= UINT_MAX)) (PreH7 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH8 : (0 <= n1_pre)) (PreH9 : (n1_pre <= UINT_MAX)) (PreH10 : (0 <= n0_pre)) (PreH11 : (n0_pre <= UINT_MAX)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH13 : (d1_pre <= UINT_MAX)) (PreH14 : (0 <= d0_pre)) (PreH15 : (d0_pre <= UINT_MAX)) (PreH16 : (0 <= dinv_pre)) (PreH17 : (dinv_pre <= UINT_MAX)) (PreH18 : (0 <= qmid)) (PreH19 : (qmid <= UINT_MAX)) (PreH20 : (0 <= rmid1)) (PreH21 : (rmid1 <= UINT_MAX)) (PreH22 : (0 <= rmid0)) (PreH23 : (rmid0 <= UINT_MAX)) (PreH24 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH25 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits ((qmid + 1 )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> rmid1)
  **  ((( &( "rv0" ) )) # UInt  |-> rmid0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (rmid0 - d0_pre ))
|--
  “ False ”
.

Definition gmp_udiv_qr_3by2_entail_wit_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH2 : (0 <= n2_pre)) (PreH3 : (n2_pre <= UINT_MAX)) (PreH4 : (0 <= n1_pre)) (PreH5 : (n1_pre <= UINT_MAX)) (PreH6 : (0 <= n0_pre)) (PreH7 : (n0_pre <= UINT_MAX)) (PreH8 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH10 : (d1_pre <= UINT_MAX)) (PreH11 : (0 <= d0_pre)) (PreH12 : (d0_pre <= UINT_MAX)) (PreH13 : (0 <= dinv_pre)) (PreH14 : (dinv_pre <= UINT_MAX)) (PreH15 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH16 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "q0" ) )) # UInt  |-> w0_value)
  **  ((( &( "qv" ) )) # UInt  |-> w1_value)
  **  ((( &( "rv0" ) )) # UInt  |->_)
  **  ((( &( "rv1" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((( &( "q0" ) )) # UInt  |-> w0_value)
  **  ((( &( "qv" ) )) # UInt  |-> w1_value)
  **  ((( &( "rv0" ) )) # UInt  |->_)
  **  ((( &( "rv1" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_entail_wit_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w0_value)) (PreH2 : (w0_value <= UINT_MAX)) (PreH3 : (w1_value <= UINT_MAX)) (PreH4 : (dinv_pre >= 0)) (PreH5 : (d0_pre >= 0)) (PreH6 : (d1_pre >= 0)) (PreH7 : (n0_pre >= 0)) (PreH8 : (n1_pre >= 0)) (PreH9 : (n2_pre >= 0)) (PreH10 : (w1_value >= 0)) (PreH11 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH12 : (0 <= n2_pre)) (PreH13 : (n2_pre <= UINT_MAX)) (PreH14 : (0 <= n1_pre)) (PreH15 : (n1_pre <= UINT_MAX)) (PreH16 : (0 <= n0_pre)) (PreH17 : (n0_pre <= UINT_MAX)) (PreH18 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH19 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH20 : (d1_pre <= UINT_MAX)) (PreH21 : (0 <= d0_pre)) (PreH22 : (d0_pre <= UINT_MAX)) (PreH23 : (0 <= dinv_pre)) (PreH24 : (dinv_pre <= UINT_MAX)) (PreH25 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH26 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "q0" ) )) # UInt  |-> w0_value)
  **  ((( &( "qv" ) )) # UInt  |-> w1_value)
  **  ((( &( "rv0" ) )) # UInt  |->_)
  **  ((( &( "rv1" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((( &( "qv" ) )) # UInt  |-> w1_value)
  **  ((( &( "q0" ) )) # UInt  |-> w0_value)
  **  ((( &( "rv0" ) )) # UInt  |->_)
  **  ((( &( "rv1" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_entail_wit_3_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_2: Z) (w1_value_2: Z) (PreH1 : (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) ))) (PreH2 : (n0_pre >= d0_pre)) (PreH3 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (w1_value <= UINT_MAX)) (PreH10 : (dinv_pre >= 0)) (PreH11 : (d0_pre >= 0)) (PreH12 : (d1_pre >= 0)) (PreH13 : (n0_pre >= 0)) (PreH14 : (n1_pre >= 0)) (PreH15 : (n2_pre >= 0)) (PreH16 : (w1_value >= 0)) (PreH17 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH18 : (0 <= n2_pre)) (PreH19 : (n2_pre <= UINT_MAX)) (PreH20 : (0 <= n1_pre)) (PreH21 : (n1_pre <= UINT_MAX)) (PreH22 : (0 <= n0_pre)) (PreH23 : (n0_pre <= UINT_MAX)) (PreH24 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH26 : (d1_pre <= UINT_MAX)) (PreH27 : (0 <= d0_pre)) (PreH28 : (d0_pre <= UINT_MAX)) (PreH29 : (0 <= dinv_pre)) (PreH30 : (dinv_pre <= UINT_MAX)) (PreH31 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= w0_value_2) ” 
  &&  “ (w0_value_2 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (w1_value_2 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) >= 0) ” 
  &&  “ (w1_value_2 >= 0) ” 
  &&  “ (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) ” 
  &&  “ (n0_pre >= d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_entail_wit_3_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_3: Z) (w1_value_3: Z) (PreH1 : (((w1_value_3 * UINT_MOD ) + w0_value_3 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) ))) (PreH2 : (n0_pre < d0_pre)) (PreH3 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (w1_value <= UINT_MAX)) (PreH10 : (dinv_pre >= 0)) (PreH11 : (d0_pre >= 0)) (PreH12 : (d1_pre >= 0)) (PreH13 : (n0_pre >= 0)) (PreH14 : (n1_pre >= 0)) (PreH15 : (n2_pre >= 0)) (PreH16 : (w1_value >= 0)) (PreH17 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH18 : (0 <= n2_pre)) (PreH19 : (n2_pre <= UINT_MAX)) (PreH20 : (0 <= n1_pre)) (PreH21 : (n1_pre <= UINT_MAX)) (PreH22 : (0 <= n0_pre)) (PreH23 : (n0_pre <= UINT_MAX)) (PreH24 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH26 : (d1_pre <= UINT_MAX)) (PreH27 : (0 <= d0_pre)) (PreH28 : (d0_pre <= UINT_MAX)) (PreH29 : (0 <= dinv_pre)) (PreH30 : (dinv_pre <= UINT_MAX)) (PreH31 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t0" ) )) # UInt  |-> w0_value_3)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_3)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= w0_value_3) ” 
  &&  “ (w0_value_3 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (w1_value_3 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) >= 0) ” 
  &&  “ (w1_value_3 >= 0) ” 
  &&  “ (((w1_value_3 * UINT_MOD ) + w0_value_3 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) ” 
  &&  “ (n0_pre < d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((( &( "t0" ) )) # UInt  |-> w0_value_3)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_3)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_entail_wit_3_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_4: Z) (w1_value_4: Z) (PreH1 : (((w1_value_4 * UINT_MOD ) + w0_value_4 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) ))) (PreH2 : (n0_pre >= d0_pre)) (PreH3 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (w1_value <= UINT_MAX)) (PreH10 : (dinv_pre >= 0)) (PreH11 : (d0_pre >= 0)) (PreH12 : (d1_pre >= 0)) (PreH13 : (n0_pre >= 0)) (PreH14 : (n1_pre >= 0)) (PreH15 : (n2_pre >= 0)) (PreH16 : (w1_value >= 0)) (PreH17 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH18 : (0 <= n2_pre)) (PreH19 : (n2_pre <= UINT_MAX)) (PreH20 : (0 <= n1_pre)) (PreH21 : (n1_pre <= UINT_MAX)) (PreH22 : (0 <= n0_pre)) (PreH23 : (n0_pre <= UINT_MAX)) (PreH24 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH26 : (d1_pre <= UINT_MAX)) (PreH27 : (0 <= d0_pre)) (PreH28 : (d0_pre <= UINT_MAX)) (PreH29 : (0 <= dinv_pre)) (PreH30 : (dinv_pre <= UINT_MAX)) (PreH31 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t0" ) )) # UInt  |-> w0_value_4)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_4)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= w0_value_4) ” 
  &&  “ (w0_value_4 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (w1_value_4 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) >= 0) ” 
  &&  “ (w1_value_4 >= 0) ” 
  &&  “ (((w1_value_4 * UINT_MOD ) + w0_value_4 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) ” 
  &&  “ (n0_pre >= d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((( &( "t0" ) )) # UInt  |-> w0_value_4)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_4)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_entail_wit_3_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_5: Z) (w1_value_5: Z) (PreH1 : (((w1_value_5 * UINT_MOD ) + w0_value_5 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) ))) (PreH2 : (n0_pre < d0_pre)) (PreH3 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value)) (PreH4 : (0 <= w1_value)) (PreH5 : (w1_value <= UINT_MAX)) (PreH6 : (w0_value >= 0)) (PreH7 : (0 <= w0_value)) (PreH8 : (w0_value <= UINT_MAX)) (PreH9 : (w1_value <= UINT_MAX)) (PreH10 : (dinv_pre >= 0)) (PreH11 : (d0_pre >= 0)) (PreH12 : (d1_pre >= 0)) (PreH13 : (n0_pre >= 0)) (PreH14 : (n1_pre >= 0)) (PreH15 : (n2_pre >= 0)) (PreH16 : (w1_value >= 0)) (PreH17 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH18 : (0 <= n2_pre)) (PreH19 : (n2_pre <= UINT_MAX)) (PreH20 : (0 <= n1_pre)) (PreH21 : (n1_pre <= UINT_MAX)) (PreH22 : (0 <= n0_pre)) (PreH23 : (n0_pre <= UINT_MAX)) (PreH24 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH25 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH26 : (d1_pre <= UINT_MAX)) (PreH27 : (0 <= d0_pre)) (PreH28 : (d0_pre <= UINT_MAX)) (PreH29 : (0 <= dinv_pre)) (PreH30 : (dinv_pre <= UINT_MAX)) (PreH31 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH32 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t0" ) )) # UInt  |-> w0_value_5)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_5)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= w0_value_5) ” 
  &&  “ (w0_value_5 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (w1_value_5 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) >= 0) ” 
  &&  “ (w1_value_5 >= 0) ” 
  &&  “ (((w1_value_5 * UINT_MOD ) + w0_value_5 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) ” 
  &&  “ (n0_pre < d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((( &( "t0" ) )) # UInt  |-> w0_value_5)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_5)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_entail_wit_4_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_2: Z) (w1_value_2: Z) (PreH1 : (0 <= w0_value_2)) (PreH2 : (w0_value_2 <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) <= UINT_MAX)) (PreH4 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH5 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH6 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX)) (PreH7 : (w1_value_2 <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) >= 0)) (PreH9 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH10 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH11 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) >= 0)) (PreH12 : (w1_value_2 >= 0)) (PreH13 : (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) ))) (PreH14 : (n0_pre >= d0_pre)) (PreH15 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value)) (PreH16 : (0 <= w1_value)) (PreH17 : (w1_value <= UINT_MAX)) (PreH18 : (w0_value >= 0)) (PreH19 : (0 <= w0_value)) (PreH20 : (w0_value <= UINT_MAX)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (dinv_pre >= 0)) (PreH23 : (d0_pre >= 0)) (PreH24 : (d1_pre >= 0)) (PreH25 : (n0_pre >= 0)) (PreH26 : (n1_pre >= 0)) (PreH27 : (n2_pre >= 0)) (PreH28 : (w1_value >= 0)) (PreH29 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH30 : (0 <= n2_pre)) (PreH31 : (n2_pre <= UINT_MAX)) (PreH32 : (0 <= n1_pre)) (PreH33 : (n1_pre <= UINT_MAX)) (PreH34 : (0 <= n0_pre)) (PreH35 : (n0_pre <= UINT_MAX)) (PreH36 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH37 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH38 : (d1_pre <= UINT_MAX)) (PreH39 : (0 <= d0_pre)) (PreH40 : (d0_pre <= UINT_MAX)) (PreH41 : (0 <= dinv_pre)) (PreH42 : (dinv_pre <= UINT_MAX)) (PreH43 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH44 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= w1_value_2) ” 
  &&  “ (w1_value_2 <= UINT_MAX) ” 
  &&  “ (w0_value_2 >= 0) ” 
  &&  “ (0 <= w0_value_2) ” 
  &&  “ (w0_value_2 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (w1_value_2 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) >= 0) ” 
  &&  “ (w1_value_2 >= 0) ” 
  &&  “ (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) ” 
  &&  “ (n0_pre >= d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_entail_wit_4_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_3: Z) (w1_value_3: Z) (PreH1 : (0 <= w0_value_3)) (PreH2 : (w0_value_3 <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) <= UINT_MAX)) (PreH4 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH5 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH6 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX)) (PreH7 : (w1_value_3 <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) >= 0)) (PreH9 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH10 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH11 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) >= 0)) (PreH12 : (w1_value_3 >= 0)) (PreH13 : (((w1_value_3 * UINT_MOD ) + w0_value_3 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) ))) (PreH14 : (n0_pre < d0_pre)) (PreH15 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value)) (PreH16 : (0 <= w1_value)) (PreH17 : (w1_value <= UINT_MAX)) (PreH18 : (w0_value >= 0)) (PreH19 : (0 <= w0_value)) (PreH20 : (w0_value <= UINT_MAX)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (dinv_pre >= 0)) (PreH23 : (d0_pre >= 0)) (PreH24 : (d1_pre >= 0)) (PreH25 : (n0_pre >= 0)) (PreH26 : (n1_pre >= 0)) (PreH27 : (n2_pre >= 0)) (PreH28 : (w1_value >= 0)) (PreH29 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH30 : (0 <= n2_pre)) (PreH31 : (n2_pre <= UINT_MAX)) (PreH32 : (0 <= n1_pre)) (PreH33 : (n1_pre <= UINT_MAX)) (PreH34 : (0 <= n0_pre)) (PreH35 : (n0_pre <= UINT_MAX)) (PreH36 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH37 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH38 : (d1_pre <= UINT_MAX)) (PreH39 : (0 <= d0_pre)) (PreH40 : (d0_pre <= UINT_MAX)) (PreH41 : (0 <= dinv_pre)) (PreH42 : (dinv_pre <= UINT_MAX)) (PreH43 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH44 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t0" ) )) # UInt  |-> w0_value_3)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_3)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= w1_value_3) ” 
  &&  “ (w1_value_3 <= UINT_MAX) ” 
  &&  “ (w0_value_3 >= 0) ” 
  &&  “ (0 <= w0_value_3) ” 
  &&  “ (w0_value_3 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (w1_value_3 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) >= 0) ” 
  &&  “ (w1_value_3 >= 0) ” 
  &&  “ (((w1_value_3 * UINT_MOD ) + w0_value_3 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) ” 
  &&  “ (n0_pre < d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((( &( "t1" ) )) # UInt  |-> w1_value_3)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_3)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_entail_wit_4_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_4: Z) (w1_value_4: Z) (PreH1 : (0 <= w0_value_4)) (PreH2 : (w0_value_4 <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) <= UINT_MAX)) (PreH4 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH5 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH6 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX)) (PreH7 : (w1_value_4 <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) >= 0)) (PreH9 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH10 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH11 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) >= 0)) (PreH12 : (w1_value_4 >= 0)) (PreH13 : (((w1_value_4 * UINT_MOD ) + w0_value_4 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) ))) (PreH14 : (n0_pre >= d0_pre)) (PreH15 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value)) (PreH16 : (0 <= w1_value)) (PreH17 : (w1_value <= UINT_MAX)) (PreH18 : (w0_value >= 0)) (PreH19 : (0 <= w0_value)) (PreH20 : (w0_value <= UINT_MAX)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (dinv_pre >= 0)) (PreH23 : (d0_pre >= 0)) (PreH24 : (d1_pre >= 0)) (PreH25 : (n0_pre >= 0)) (PreH26 : (n1_pre >= 0)) (PreH27 : (n2_pre >= 0)) (PreH28 : (w1_value >= 0)) (PreH29 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH30 : (0 <= n2_pre)) (PreH31 : (n2_pre <= UINT_MAX)) (PreH32 : (0 <= n1_pre)) (PreH33 : (n1_pre <= UINT_MAX)) (PreH34 : (0 <= n0_pre)) (PreH35 : (n0_pre <= UINT_MAX)) (PreH36 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH37 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH38 : (d1_pre <= UINT_MAX)) (PreH39 : (0 <= d0_pre)) (PreH40 : (d0_pre <= UINT_MAX)) (PreH41 : (0 <= dinv_pre)) (PreH42 : (dinv_pre <= UINT_MAX)) (PreH43 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH44 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t0" ) )) # UInt  |-> w0_value_4)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_4)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= w1_value_4) ” 
  &&  “ (w1_value_4 <= UINT_MAX) ” 
  &&  “ (w0_value_4 >= 0) ” 
  &&  “ (0 <= w0_value_4) ” 
  &&  “ (w0_value_4 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (w1_value_4 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) >= 0) ” 
  &&  “ (w1_value_4 >= 0) ” 
  &&  “ (((w1_value_4 * UINT_MOD ) + w0_value_4 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) ” 
  &&  “ (n0_pre >= d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((( &( "t1" ) )) # UInt  |-> w1_value_4)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_4)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_entail_wit_4_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_5: Z) (w1_value_5: Z) (PreH1 : (0 <= w0_value_5)) (PreH2 : (w0_value_5 <= UINT_MAX)) (PreH3 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) <= UINT_MAX)) (PreH4 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH5 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH6 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX)) (PreH7 : (w1_value_5 <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) >= 0)) (PreH9 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH10 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH11 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) >= 0)) (PreH12 : (w1_value_5 >= 0)) (PreH13 : (((w1_value_5 * UINT_MOD ) + w0_value_5 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) ))) (PreH14 : (n0_pre < d0_pre)) (PreH15 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value)) (PreH16 : (0 <= w1_value)) (PreH17 : (w1_value <= UINT_MAX)) (PreH18 : (w0_value >= 0)) (PreH19 : (0 <= w0_value)) (PreH20 : (w0_value <= UINT_MAX)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (dinv_pre >= 0)) (PreH23 : (d0_pre >= 0)) (PreH24 : (d1_pre >= 0)) (PreH25 : (n0_pre >= 0)) (PreH26 : (n1_pre >= 0)) (PreH27 : (n2_pre >= 0)) (PreH28 : (w1_value >= 0)) (PreH29 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH30 : (0 <= n2_pre)) (PreH31 : (n2_pre <= UINT_MAX)) (PreH32 : (0 <= n1_pre)) (PreH33 : (n1_pre <= UINT_MAX)) (PreH34 : (0 <= n0_pre)) (PreH35 : (n0_pre <= UINT_MAX)) (PreH36 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH37 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH38 : (d1_pre <= UINT_MAX)) (PreH39 : (0 <= d0_pre)) (PreH40 : (d0_pre <= UINT_MAX)) (PreH41 : (0 <= dinv_pre)) (PreH42 : (dinv_pre <= UINT_MAX)) (PreH43 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH44 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t0" ) )) # UInt  |-> w0_value_5)
  **  ((( &( "t1" ) )) # UInt  |-> w1_value_5)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= w1_value_5) ” 
  &&  “ (w1_value_5 <= UINT_MAX) ” 
  &&  “ (w0_value_5 >= 0) ” 
  &&  “ (0 <= w0_value_5) ” 
  &&  “ (w0_value_5 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (w1_value_5 <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) >= 0) ” 
  &&  “ (w1_value_5 >= 0) ” 
  &&  “ (((w1_value_5 * UINT_MOD ) + w0_value_5 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) ” 
  &&  “ (n0_pre < d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((( &( "t1" ) )) # UInt  |-> w1_value_5)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_5)
  **  ((( &( "qv" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)))
  **  ((( &( "q0" ) )) # UInt  |-> (unsigned_last_nbits ((w0_value + n1_pre )) (32)))
  **  ((( &( "rv0" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "rv1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)))
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((n0_pre - d0_pre )) (32)))
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r0" ) )) # Ptr  |-> r0_pre)
  **  ((( &( "n2" ) )) # UInt  |-> n2_pre)
  **  ((( &( "n1" ) )) # UInt  |-> n1_pre)
  **  ((( &( "n0" ) )) # UInt  |-> n0_pre)
  **  ((( &( "d1" ) )) # UInt  |-> d1_pre)
  **  ((( &( "d0" ) )) # UInt  |-> d0_pre)
  **  ((( &( "dinv" ) )) # UInt  |-> dinv_pre)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_entail_wit_5_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_2: Z) (w1_value_2: Z) (PreH1 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= w0_value_2)) (PreH2 : (0 <= w1_value_2)) (PreH3 : (w1_value_2 <= UINT_MAX)) (PreH4 : (w0_value_2 >= 0)) (PreH5 : (0 <= w0_value_2)) (PreH6 : (w0_value_2 <= UINT_MAX)) (PreH7 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH9 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH10 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX)) (PreH11 : (w1_value_2 <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) >= 0)) (PreH13 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH14 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH15 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) >= 0)) (PreH16 : (w1_value_2 >= 0)) (PreH17 : (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) ))) (PreH18 : (n0_pre >= d0_pre)) (PreH19 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value)) (PreH20 : (0 <= w1_value)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (w0_value >= 0)) (PreH23 : (0 <= w0_value)) (PreH24 : (w0_value <= UINT_MAX)) (PreH25 : (w1_value <= UINT_MAX)) (PreH26 : (dinv_pre >= 0)) (PreH27 : (d0_pre >= 0)) (PreH28 : (d1_pre >= 0)) (PreH29 : (n0_pre >= 0)) (PreH30 : (n1_pre >= 0)) (PreH31 : (n2_pre >= 0)) (PreH32 : (w1_value >= 0)) (PreH33 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH34 : (0 <= n2_pre)) (PreH35 : (n2_pre <= UINT_MAX)) (PreH36 : (0 <= n1_pre)) (PreH37 : (n1_pre <= UINT_MAX)) (PreH38 : (0 <= n0_pre)) (PreH39 : (n0_pre <= UINT_MAX)) (PreH40 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH41 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH42 : (d1_pre <= UINT_MAX)) (PreH43 : (0 <= d0_pre)) (PreH44 : (d0_pre <= UINT_MAX)) (PreH45 : (0 <= dinv_pre)) (PreH46 : (dinv_pre <= UINT_MAX)) (PreH47 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH48 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)))
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) < (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_5_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_2: Z) (w1_value_2: Z) (PreH1 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) < w0_value_2)) (PreH2 : (0 <= w1_value_2)) (PreH3 : (w1_value_2 <= UINT_MAX)) (PreH4 : (w0_value_2 >= 0)) (PreH5 : (0 <= w0_value_2)) (PreH6 : (w0_value_2 <= UINT_MAX)) (PreH7 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH9 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH10 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX)) (PreH11 : (w1_value_2 <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) >= 0)) (PreH13 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH14 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH15 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) >= 0)) (PreH16 : (w1_value_2 >= 0)) (PreH17 : (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) ))) (PreH18 : (n0_pre >= d0_pre)) (PreH19 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value)) (PreH20 : (0 <= w1_value)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (w0_value >= 0)) (PreH23 : (0 <= w0_value)) (PreH24 : (w0_value <= UINT_MAX)) (PreH25 : (w1_value <= UINT_MAX)) (PreH26 : (dinv_pre >= 0)) (PreH27 : (d0_pre >= 0)) (PreH28 : (d1_pre >= 0)) (PreH29 : (n0_pre >= 0)) (PreH30 : (n1_pre >= 0)) (PreH31 : (n2_pre >= 0)) (PreH32 : (w1_value >= 0)) (PreH33 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH34 : (0 <= n2_pre)) (PreH35 : (n2_pre <= UINT_MAX)) (PreH36 : (0 <= n1_pre)) (PreH37 : (n1_pre <= UINT_MAX)) (PreH38 : (0 <= n0_pre)) (PreH39 : (n0_pre <= UINT_MAX)) (PreH40 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH41 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH42 : (d1_pre <= UINT_MAX)) (PreH43 : (0 <= d0_pre)) (PreH44 : (d0_pre <= UINT_MAX)) (PreH45 : (0 <= dinv_pre)) (PreH46 : (dinv_pre <= UINT_MAX)) (PreH47 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH48 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)))
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) < (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_5_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_2: Z) (w1_value_2: Z) (PreH1 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= w0_value_2)) (PreH2 : (0 <= w1_value_2)) (PreH3 : (w1_value_2 <= UINT_MAX)) (PreH4 : (w0_value_2 >= 0)) (PreH5 : (0 <= w0_value_2)) (PreH6 : (w0_value_2 <= UINT_MAX)) (PreH7 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH9 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH10 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX)) (PreH11 : (w1_value_2 <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) >= 0)) (PreH13 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH14 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH15 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) >= 0)) (PreH16 : (w1_value_2 >= 0)) (PreH17 : (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) ))) (PreH18 : (n0_pre < d0_pre)) (PreH19 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value)) (PreH20 : (0 <= w1_value)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (w0_value >= 0)) (PreH23 : (0 <= w0_value)) (PreH24 : (w0_value <= UINT_MAX)) (PreH25 : (w1_value <= UINT_MAX)) (PreH26 : (dinv_pre >= 0)) (PreH27 : (d0_pre >= 0)) (PreH28 : (d1_pre >= 0)) (PreH29 : (n0_pre >= 0)) (PreH30 : (n1_pre >= 0)) (PreH31 : (n2_pre >= 0)) (PreH32 : (w1_value >= 0)) (PreH33 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH34 : (0 <= n2_pre)) (PreH35 : (n2_pre <= UINT_MAX)) (PreH36 : (0 <= n1_pre)) (PreH37 : (n1_pre <= UINT_MAX)) (PreH38 : (0 <= n0_pre)) (PreH39 : (n0_pre <= UINT_MAX)) (PreH40 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH41 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH42 : (d1_pre <= UINT_MAX)) (PreH43 : (0 <= d0_pre)) (PreH44 : (d0_pre <= UINT_MAX)) (PreH45 : (0 <= dinv_pre)) (PreH46 : (dinv_pre <= UINT_MAX)) (PreH47 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH48 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)))
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) < (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_5_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_2: Z) (w1_value_2: Z) (PreH1 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) < w0_value_2)) (PreH2 : (0 <= w1_value_2)) (PreH3 : (w1_value_2 <= UINT_MAX)) (PreH4 : (w0_value_2 >= 0)) (PreH5 : (0 <= w0_value_2)) (PreH6 : (w0_value_2 <= UINT_MAX)) (PreH7 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH9 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH10 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX)) (PreH11 : (w1_value_2 <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) >= 0)) (PreH13 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH14 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH15 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) >= 0)) (PreH16 : (w1_value_2 >= 0)) (PreH17 : (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) ))) (PreH18 : (n0_pre < d0_pre)) (PreH19 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value)) (PreH20 : (0 <= w1_value)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (w0_value >= 0)) (PreH23 : (0 <= w0_value)) (PreH24 : (w0_value <= UINT_MAX)) (PreH25 : (w1_value <= UINT_MAX)) (PreH26 : (dinv_pre >= 0)) (PreH27 : (d0_pre >= 0)) (PreH28 : (d1_pre >= 0)) (PreH29 : (n0_pre >= 0)) (PreH30 : (n1_pre >= 0)) (PreH31 : (n2_pre >= 0)) (PreH32 : (w1_value >= 0)) (PreH33 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH34 : (0 <= n2_pre)) (PreH35 : (n2_pre <= UINT_MAX)) (PreH36 : (0 <= n1_pre)) (PreH37 : (n1_pre <= UINT_MAX)) (PreH38 : (0 <= n0_pre)) (PreH39 : (n0_pre <= UINT_MAX)) (PreH40 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH41 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH42 : (d1_pre <= UINT_MAX)) (PreH43 : (0 <= d0_pre)) (PreH44 : (d0_pre <= UINT_MAX)) (PreH45 : (0 <= dinv_pre)) (PreH46 : (dinv_pre <= UINT_MAX)) (PreH47 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH48 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)))
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) < (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 0 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_5_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_2: Z) (w1_value_2: Z) (PreH1 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= w0_value_2)) (PreH2 : (0 <= w1_value_2)) (PreH3 : (w1_value_2 <= UINT_MAX)) (PreH4 : (w0_value_2 >= 0)) (PreH5 : (0 <= w0_value_2)) (PreH6 : (w0_value_2 <= UINT_MAX)) (PreH7 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH9 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH10 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX)) (PreH11 : (w1_value_2 <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) >= 0)) (PreH13 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH14 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH15 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) >= 0)) (PreH16 : (w1_value_2 >= 0)) (PreH17 : (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) ))) (PreH18 : (n0_pre >= d0_pre)) (PreH19 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value)) (PreH20 : (0 <= w1_value)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (w0_value >= 0)) (PreH23 : (0 <= w0_value)) (PreH24 : (w0_value <= UINT_MAX)) (PreH25 : (w1_value <= UINT_MAX)) (PreH26 : (dinv_pre >= 0)) (PreH27 : (d0_pre >= 0)) (PreH28 : (d1_pre >= 0)) (PreH29 : (n0_pre >= 0)) (PreH30 : (n1_pre >= 0)) (PreH31 : (n2_pre >= 0)) (PreH32 : (w1_value >= 0)) (PreH33 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH34 : (0 <= n2_pre)) (PreH35 : (n2_pre <= UINT_MAX)) (PreH36 : (0 <= n1_pre)) (PreH37 : (n1_pre <= UINT_MAX)) (PreH38 : (0 <= n0_pre)) (PreH39 : (n0_pre <= UINT_MAX)) (PreH40 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH41 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH42 : (d1_pre <= UINT_MAX)) (PreH43 : (0 <= d0_pre)) (PreH44 : (d0_pre <= UINT_MAX)) (PreH45 : (0 <= dinv_pre)) (PreH46 : (dinv_pre <= UINT_MAX)) (PreH47 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH48 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)))
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) < (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_5_6 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_2: Z) (w1_value_2: Z) (PreH1 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) < w0_value_2)) (PreH2 : (0 <= w1_value_2)) (PreH3 : (w1_value_2 <= UINT_MAX)) (PreH4 : (w0_value_2 >= 0)) (PreH5 : (0 <= w0_value_2)) (PreH6 : (w0_value_2 <= UINT_MAX)) (PreH7 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH9 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH10 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX)) (PreH11 : (w1_value_2 <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) >= 0)) (PreH13 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH14 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH15 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) >= 0)) (PreH16 : (w1_value_2 >= 0)) (PreH17 : (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) ))) (PreH18 : (n0_pre >= d0_pre)) (PreH19 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value)) (PreH20 : (0 <= w1_value)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (w0_value >= 0)) (PreH23 : (0 <= w0_value)) (PreH24 : (w0_value <= UINT_MAX)) (PreH25 : (w1_value <= UINT_MAX)) (PreH26 : (dinv_pre >= 0)) (PreH27 : (d0_pre >= 0)) (PreH28 : (d1_pre >= 0)) (PreH29 : (n0_pre >= 0)) (PreH30 : (n1_pre >= 0)) (PreH31 : (n2_pre >= 0)) (PreH32 : (w1_value >= 0)) (PreH33 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH34 : (0 <= n2_pre)) (PreH35 : (n2_pre <= UINT_MAX)) (PreH36 : (0 <= n1_pre)) (PreH37 : (n1_pre <= UINT_MAX)) (PreH38 : (0 <= n0_pre)) (PreH39 : (n0_pre <= UINT_MAX)) (PreH40 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH41 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH42 : (d1_pre <= UINT_MAX)) (PreH43 : (0 <= d0_pre)) (PreH44 : (d0_pre <= UINT_MAX)) (PreH45 : (0 <= dinv_pre)) (PreH46 : (dinv_pre <= UINT_MAX)) (PreH47 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH48 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)))
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) < (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 0 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_5_7 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_2: Z) (w1_value_2: Z) (PreH1 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= w0_value_2)) (PreH2 : (0 <= w1_value_2)) (PreH3 : (w1_value_2 <= UINT_MAX)) (PreH4 : (w0_value_2 >= 0)) (PreH5 : (0 <= w0_value_2)) (PreH6 : (w0_value_2 <= UINT_MAX)) (PreH7 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH9 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH10 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX)) (PreH11 : (w1_value_2 <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) >= 0)) (PreH13 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH14 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH15 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) >= 0)) (PreH16 : (w1_value_2 >= 0)) (PreH17 : (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) ))) (PreH18 : (n0_pre < d0_pre)) (PreH19 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value)) (PreH20 : (0 <= w1_value)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (w0_value >= 0)) (PreH23 : (0 <= w0_value)) (PreH24 : (w0_value <= UINT_MAX)) (PreH25 : (w1_value <= UINT_MAX)) (PreH26 : (dinv_pre >= 0)) (PreH27 : (d0_pre >= 0)) (PreH28 : (d1_pre >= 0)) (PreH29 : (n0_pre >= 0)) (PreH30 : (n1_pre >= 0)) (PreH31 : (n2_pre >= 0)) (PreH32 : (w1_value >= 0)) (PreH33 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH34 : (0 <= n2_pre)) (PreH35 : (n2_pre <= UINT_MAX)) (PreH36 : (0 <= n1_pre)) (PreH37 : (n1_pre <= UINT_MAX)) (PreH38 : (0 <= n0_pre)) (PreH39 : (n0_pre <= UINT_MAX)) (PreH40 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH41 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH42 : (d1_pre <= UINT_MAX)) (PreH43 : (0 <= d0_pre)) (PreH44 : (d0_pre <= UINT_MAX)) (PreH45 : (0 <= dinv_pre)) (PreH46 : (dinv_pre <= UINT_MAX)) (PreH47 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH48 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)))
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) < (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_5_8 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (w0_value_2: Z) (w1_value_2: Z) (PreH1 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) < w0_value_2)) (PreH2 : (0 <= w1_value_2)) (PreH3 : (w1_value_2 <= UINT_MAX)) (PreH4 : (w0_value_2 >= 0)) (PreH5 : (0 <= w0_value_2)) (PreH6 : (w0_value_2 <= UINT_MAX)) (PreH7 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) <= UINT_MAX)) (PreH8 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) <= UINT_MAX)) (PreH9 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX)) (PreH10 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX)) (PreH11 : (w1_value_2 <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) >= 0)) (PreH13 : ((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) >= 0)) (PreH14 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= 0)) (PreH15 : ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) >= 0)) (PreH16 : (w1_value_2 >= 0)) (PreH17 : (((w1_value_2 * UINT_MOD ) + w0_value_2 ) = (d0_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) ))) (PreH18 : (n0_pre < d0_pre)) (PreH19 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value)) (PreH20 : (0 <= w1_value)) (PreH21 : (w1_value <= UINT_MAX)) (PreH22 : (w0_value >= 0)) (PreH23 : (0 <= w0_value)) (PreH24 : (w0_value <= UINT_MAX)) (PreH25 : (w1_value <= UINT_MAX)) (PreH26 : (dinv_pre >= 0)) (PreH27 : (d0_pre >= 0)) (PreH28 : (d1_pre >= 0)) (PreH29 : (n0_pre >= 0)) (PreH30 : (n1_pre >= 0)) (PreH31 : (n2_pre >= 0)) (PreH32 : (w1_value >= 0)) (PreH33 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH34 : (0 <= n2_pre)) (PreH35 : (n2_pre <= UINT_MAX)) (PreH36 : (0 <= n1_pre)) (PreH37 : (n1_pre <= UINT_MAX)) (PreH38 : (0 <= n0_pre)) (PreH39 : (n0_pre <= UINT_MAX)) (PreH40 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH41 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH42 : (d1_pre <= UINT_MAX)) (PreH43 : (0 <= d0_pre)) (PreH44 : (d0_pre <= UINT_MAX)) (PreH45 : (0 <= dinv_pre)) (PreH46 : (dinv_pre <= UINT_MAX)) (PreH47 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH48 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((( &( "t1" ) )) # UInt  |-> w1_value_2)
  **  ((( &( "t0" ) )) # UInt  |-> w0_value_2)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)))
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) < (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ (qext = ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) + 1 )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) >= (unsigned_last_nbits ((w0_value + n1_pre )) (32))) ” 
  &&  “ (((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits ((n1_pre - (unsigned_last_nbits ((d1_pre * (unsigned_last_nbits (((unsigned_last_nbits ((w1_value + n2_pre )) (32)) + 1 )) (32)) )) (32)) )) (32)) - d1_pre )) (32)) - 1 )) (32)) - w1_value_2 )) (32)) - 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits (((unsigned_last_nbits ((n0_pre - d0_pre )) (32)) - w0_value_2 )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "t1" ) )) # UInt  |->_)
  **  ((( &( "t0" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_6_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qhat: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (qext_2 = (qhat + 1 ))) (PreH2 : (0 <= n2_pre)) (PreH3 : (n2_pre <= UINT_MAX)) (PreH4 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH5 : (0 <= n1_pre)) (PreH6 : (n1_pre <= UINT_MAX)) (PreH7 : (0 <= n0_pre)) (PreH8 : (n0_pre <= UINT_MAX)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH10 : (d1_pre <= UINT_MAX)) (PreH11 : (0 <= d0_pre)) (PreH12 : (d0_pre <= UINT_MAX)) (PreH13 : (0 <= dinv_pre)) (PreH14 : (dinv_pre <= UINT_MAX)) (PreH15 : (0 <= qhat)) (PreH16 : (qhat <= UINT_MAX)) (PreH17 : (1 <= qext_2)) (PreH18 : (qext_2 <= UINT_MOD)) (PreH19 : (0 <= rpre1)) (PreH20 : (rpre1 <= UINT_MAX)) (PreH21 : (0 <= rpre0)) (PreH22 : (rpre0 <= UINT_MAX)) (PreH23 : (0 <= qlo)) (PreH24 : (qlo <= UINT_MAX)) (PreH25 : (rpre1 < qlo)) (PreH26 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (0 < (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ (qext = (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qhat + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ (rpre1 < qlo) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ ((unsigned_last_nbits ((qhat + 1 )) (32)) = 0) ” 
  &&  “ (qext = UINT_MOD) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qhat + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ (rpre1 < qlo) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_6_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qhat: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (qext_2 = (qhat + 1 ))) (PreH2 : (0 <= n2_pre)) (PreH3 : (n2_pre <= UINT_MAX)) (PreH4 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH5 : (0 <= n1_pre)) (PreH6 : (n1_pre <= UINT_MAX)) (PreH7 : (0 <= n0_pre)) (PreH8 : (n0_pre <= UINT_MAX)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH10 : (d1_pre <= UINT_MAX)) (PreH11 : (0 <= d0_pre)) (PreH12 : (d0_pre <= UINT_MAX)) (PreH13 : (0 <= dinv_pre)) (PreH14 : (dinv_pre <= UINT_MAX)) (PreH15 : (0 <= qhat)) (PreH16 : (qhat <= UINT_MAX)) (PreH17 : (1 <= qext_2)) (PreH18 : (qext_2 <= UINT_MOD)) (PreH19 : (0 <= rpre1)) (PreH20 : (rpre1 <= UINT_MAX)) (PreH21 : (0 <= rpre0)) (PreH22 : (rpre0 <= UINT_MAX)) (PreH23 : (0 <= qlo)) (PreH24 : (qlo <= UINT_MAX)) (PreH25 : (rpre1 >= qlo)) (PreH26 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH27 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (0 < (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ (qext = (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qhat + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ (rpre1 >= qlo) ” 
  &&  “ ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ ((unsigned_last_nbits ((qhat + 1 )) (32)) = 0) ” 
  &&  “ (qext = UINT_MOD) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qhat + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ (rpre1 >= qlo) ” 
  &&  “ ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_6_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qhat: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (qext_2 = (qhat + 1 ))) (PreH2 : (0 <= n2_pre)) (PreH3 : (n2_pre <= UINT_MAX)) (PreH4 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH5 : (0 <= n1_pre)) (PreH6 : (n1_pre <= UINT_MAX)) (PreH7 : (0 <= n0_pre)) (PreH8 : (n0_pre <= UINT_MAX)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH10 : (d1_pre <= UINT_MAX)) (PreH11 : (0 <= d0_pre)) (PreH12 : (d0_pre <= UINT_MAX)) (PreH13 : (0 <= dinv_pre)) (PreH14 : (dinv_pre <= UINT_MAX)) (PreH15 : (0 <= qhat)) (PreH16 : (qhat <= UINT_MAX)) (PreH17 : (1 <= qext_2)) (PreH18 : (qext_2 <= UINT_MOD)) (PreH19 : (0 <= rpre1)) (PreH20 : (rpre1 <= UINT_MAX)) (PreH21 : (0 <= rpre0)) (PreH22 : (rpre0 <= UINT_MAX)) (PreH23 : (0 <= qlo)) (PreH24 : (qlo <= UINT_MAX)) (PreH25 : (rpre1 >= qlo)) (PreH26 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH27 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  (EX (qext: Z) ,
  “ (0 < (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ (qext = (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qhat + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ (rpre1 >= qlo) ” 
  &&  “ ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_))
  ||
  (EX (qext: Z) ,
  “ ((unsigned_last_nbits ((qhat + 1 )) (32)) = 0) ” 
  &&  “ (qext = UINT_MOD) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qhat + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qhat + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ (rpre1 >= qlo) ” 
  &&  “ ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_))
.

Definition gmp_udiv_qr_3by2_entail_wit_7_1 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext_2 = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 < qlo)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  EX (qext: Z) ,
  “ (0 < qpre) ” 
  &&  “ (qext = qpre) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= qpre) ” 
  &&  “ (qpre <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ ((-0) = 0) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext_2 = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 < qlo)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qpre * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_7_1_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext_2 = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 < qlo)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qpre * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))
.

Definition gmp_udiv_qr_3by2_entail_wit_7_2 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext_2 = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  EX (qext: Z) ,
  “ (0 < qpre) ” 
  &&  “ (qext = qpre) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= qpre) ” 
  &&  “ (qpre <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((-1)) (32)) = UINT_MAX) ” 
  &&  “ ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext_2 = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qpre * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_7_2_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext_2 = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qpre * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))
.

Definition gmp_udiv_qr_3by2_entail_wit_7_3 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext_2 = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  EX (qext: Z) ,
  “ (0 < qpre) ” 
  &&  “ (qext = qpre) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= qpre) ” 
  &&  “ (qpre <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((-1)) (32)) = UINT_MAX) ” 
  &&  “ ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext_2 = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qpre * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_7_3_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (0 < qpre)) (PreH3 : (qext_2 = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qpre * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))
.

Definition gmp_udiv_qr_3by2_entail_wit_7_4 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext_2 = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 < qlo)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  EX (qext: Z) ,
  “ (qpre = 0) ” 
  &&  “ (qext = UINT_MOD) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= qpre) ” 
  &&  “ (qpre <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ ((-0) = 0) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext_2 = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 < qlo)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((UINT_MOD * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_7_4_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 < qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext_2 = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 < qlo)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((UINT_MOD * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))
.

Definition gmp_udiv_qr_3by2_entail_wit_7_5 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext_2 = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  EX (qext: Z) ,
  “ (qpre = 0) ” 
  &&  “ (qext = UINT_MOD) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= qpre) ” 
  &&  “ (qpre <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((-1)) (32)) = UINT_MAX) ” 
  &&  “ ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2))) ” 
  &&  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext_2 = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((UINT_MOD * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_7_5_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext_2 = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((UINT_MOD * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))
.

Definition gmp_udiv_qr_3by2_entail_wit_7_6 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext_2 = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  EX (qext: Z) ,
  “ (qpre = 0) ” 
  &&  “ (qext = UINT_MOD) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= qpre) ” 
  &&  “ (qpre <= UINT_MAX) ” 
  &&  “ (1 <= qext) ” 
  &&  “ (qext <= UINT_MOD) ” 
  &&  “ (0 <= rpre1) ” 
  &&  “ (rpre1 <= UINT_MAX) ” 
  &&  “ (0 <= rpre0) ” 
  &&  “ (rpre0 <= UINT_MAX) ” 
  &&  “ (0 <= qlo) ” 
  &&  “ (qlo <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((-1)) (32)) = UINT_MAX) ” 
  &&  “ ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2))) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext_2 = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((UINT_MOD * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 )) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_7_6_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext_2: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (PreH1 : (rpre1 >= qlo)) (PreH2 : (qpre = 0)) (PreH3 : (qext_2 = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext_2)) (PreH20 : (qext_2 <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (rpre1 >= qlo)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext_2 * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((UINT_MOD * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_1 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (qpre + m )) ” 
  &&  “ ((qpre + m ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_1_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_1_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_1_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_1_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_1_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_2 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (qpre + m )) ” 
  &&  “ ((qpre + m ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_2_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_2_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_2_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_2_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_2_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_3 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (qpre + m )) ” 
  &&  “ ((qpre + m ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_3_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_3_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_3_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_3_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_3_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_4 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (qpre + m )) ” 
  &&  “ ((qpre + m ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_4_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_5 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (qpre + m )) ” 
  &&  “ ((qpre + m ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_5_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_6 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (qpre + m )) ” 
  &&  “ ((qpre + m ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_6_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (qpre = 0)) (PreH3 : (qext = UINT_MOD)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_7 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (qpre + m )) ” 
  &&  “ ((qpre + m ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_7_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_7_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_7_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_7_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_7_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_8 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (qpre + m )) ” 
  &&  “ ((qpre + m ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_8_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((qpre + m ) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_8_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_8_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_8_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_8_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = 0)) (PreH28 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_9 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qpre + m )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qpre + m )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_9_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_9_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_9_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_9_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_9_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_9_split_goal_6 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_9_split_goal_7 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits ((qpre + m )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_10 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qpre + m )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qpre + m )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_10_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_10_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_10_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_10_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_10_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_10_split_goal_6 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_10_split_goal_7 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) >= (Z.pow (UINT_MOD) (2)))) (PreH29 : (((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) + (Z.pow (UINT_MOD) (2)) ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits ((qpre + m )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_11 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qpre + m )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qpre + m )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_11_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_11_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_11_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_11_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_11_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 0 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_11_split_goal_6 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_11_split_goal_7 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) >= rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits ((qpre + m )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_12 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((( &( "q0" ) )) # UInt  |-> qlo)
  **  ((( &( "mask" ) )) # UInt  |-> m)
  **  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qpre + m )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) <= UINT_MAX) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "q0" ) )) # UInt  |->_)
  **  ((( &( "mask" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) )) ” 
  &&  “ ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qpre + m )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_8_12_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qpre + m )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_12_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) * UINT_MOD ) + (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_12_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_12_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_12_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((rpre1 + (Z.land m d1_pre) )) (32)) + 1 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_8_12_split_goal_6 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  ((unsigned_last_nbits ((qpre + m )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_8_12_split_goal_7 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qpre: Z) (qext: Z) (rpre1: Z) (rpre0: Z) (qlo: Z) (m: Z) (PreH1 : ((unsigned_last_nbits ((rpre0 + (Z.land m d0_pre) )) (32)) < rpre0)) (PreH2 : (0 < qpre)) (PreH3 : (qext = qpre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qpre)) (PreH18 : (qpre <= UINT_MAX)) (PreH19 : (1 <= qext)) (PreH20 : (qext <= UINT_MOD)) (PreH21 : (0 <= rpre1)) (PreH22 : (rpre1 <= UINT_MAX)) (PreH23 : (0 <= rpre0)) (PreH24 : (rpre0 <= UINT_MAX)) (PreH25 : (0 <= qlo)) (PreH26 : (qlo <= UINT_MAX)) (PreH27 : (m = UINT_MAX)) (PreH28 : ((((rpre1 * UINT_MOD ) + rpre0 ) + ((d1_pre * UINT_MOD ) + d0_pre ) ) < (Z.pow (UINT_MOD) (2)))) (PreH29 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qext * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rpre1 * UINT_MOD ) ) + rpre0 ))) ,
  (0 <= (unsigned_last_nbits ((qpre + m )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_1 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rmid0 - d0_pre )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qmid + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qmid + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= ((rmid1 - d1_pre ) - 0 )) ” 
  &&  “ (((rmid1 - d1_pre ) - 0 ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rmid0 - d0_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rmid0 - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ (((((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qmid + 1 )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qmid + 1 )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) )) ” 
  &&  “ (((((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((unsigned_last_nbits ((rmid0 - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rmid0 - d0_pre )) (32))) ” 
  &&  “ (((rmid1 - d1_pre ) - 0 ) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((qmid + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qmid + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_9_1_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qmid + 1 )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_1_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (((((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) ) < ((d1_pre * UINT_MOD ) + d0_pre ))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_1_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((unsigned_last_nbits ((rmid0 - d0_pre )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_9_1_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (0 <= (unsigned_last_nbits ((rmid0 - d0_pre )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_1_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (((rmid1 - d1_pre ) - 0 ) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_9_1_split_goal_6 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((unsigned_last_nbits ((qmid + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_9_1_split_goal_7 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (0 <= (unsigned_last_nbits ((qmid + 1 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_2 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (unsigned_last_nbits ((rmid0 - d0_pre )) (32)))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qmid + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qmid + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= ((rmid1 - d1_pre ) - 1 )) ” 
  &&  “ (((rmid1 - d1_pre ) - 1 ) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rmid0 - d0_pre )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((rmid0 - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ (((((rmid1 - d1_pre ) - 1 ) * UINT_MOD ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qmid + 1 )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (((rmid1 - d1_pre ) - 1 ) * UINT_MOD ) ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qmid + 1 )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (((rmid1 - d1_pre ) - 1 ) * UINT_MOD ) ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) )) ” 
  &&  “ (((((rmid1 - d1_pre ) - 1 ) * UINT_MOD ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((unsigned_last_nbits ((rmid0 - d0_pre )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((rmid0 - d0_pre )) (32))) ” 
  &&  “ (((rmid1 - d1_pre ) - 1 ) <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits ((qmid + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qmid + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_9_2_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qmid + 1 )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (((rmid1 - d1_pre ) - 1 ) * UINT_MOD ) ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_2_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (((((rmid1 - d1_pre ) - 1 ) * UINT_MOD ) + (unsigned_last_nbits ((rmid0 - d0_pre )) (32)) ) < ((d1_pre * UINT_MOD ) + d0_pre ))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_2_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((unsigned_last_nbits ((rmid0 - d0_pre )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_9_2_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (0 <= (unsigned_last_nbits ((rmid0 - d0_pre )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_2_split_goal_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (((rmid1 - d1_pre ) - 1 ) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_9_2_split_goal_6 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((unsigned_last_nbits ((qmid + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_9_2_split_goal_7 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 > d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (0 <= (unsigned_last_nbits ((qmid + 1 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_3 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid0 >= d0_pre)) (PreH3 : (rmid1 <= d1_pre)) (PreH4 : (rmid1 >= d1_pre)) (PreH5 : (0 <= n2_pre)) (PreH6 : (n2_pre <= UINT_MAX)) (PreH7 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH8 : (0 <= n1_pre)) (PreH9 : (n1_pre <= UINT_MAX)) (PreH10 : (0 <= n0_pre)) (PreH11 : (n0_pre <= UINT_MAX)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH13 : (d1_pre <= UINT_MAX)) (PreH14 : (0 <= d0_pre)) (PreH15 : (d0_pre <= UINT_MAX)) (PreH16 : (0 <= dinv_pre)) (PreH17 : (dinv_pre <= UINT_MAX)) (PreH18 : (0 <= qmid)) (PreH19 : (qmid <= UINT_MAX)) (PreH20 : (0 <= rmid1)) (PreH21 : (rmid1 <= UINT_MAX)) (PreH22 : (0 <= rmid0)) (PreH23 : (rmid0 <= UINT_MAX)) (PreH24 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH25 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> (rmid0 - d0_pre ))
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qmid + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((qmid + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= ((rmid1 - d1_pre ) - 0 )) ” 
  &&  “ (((rmid1 - d1_pre ) - 0 ) <= UINT_MAX) ” 
  &&  “ (0 <= (rmid0 - d0_pre )) ” 
  &&  “ ((rmid0 - d0_pre ) <= UINT_MAX) ” 
  &&  “ (((((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) + (rmid0 - d0_pre ) ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qmid + 1 )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) ) + (rmid0 - d0_pre ) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid0 >= d0_pre)) (PreH3 : (rmid1 <= d1_pre)) (PreH4 : (rmid1 >= d1_pre)) (PreH5 : (0 <= n2_pre)) (PreH6 : (n2_pre <= UINT_MAX)) (PreH7 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH8 : (0 <= n1_pre)) (PreH9 : (n1_pre <= UINT_MAX)) (PreH10 : (0 <= n0_pre)) (PreH11 : (n0_pre <= UINT_MAX)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH13 : (d1_pre <= UINT_MAX)) (PreH14 : (0 <= d0_pre)) (PreH15 : (d0_pre <= UINT_MAX)) (PreH16 : (0 <= dinv_pre)) (PreH17 : (dinv_pre <= UINT_MAX)) (PreH18 : (0 <= qmid)) (PreH19 : (qmid <= UINT_MAX)) (PreH20 : (0 <= rmid1)) (PreH21 : (rmid1 <= UINT_MAX)) (PreH22 : (0 <= rmid0)) (PreH23 : (rmid0 <= UINT_MAX)) (PreH24 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH25 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  TT && emp 
|--
  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qmid + 1 )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) ) + (rmid0 - d0_pre ) )) ” 
  &&  “ (((((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) + (rmid0 - d0_pre ) ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((unsigned_last_nbits ((qmid + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ (0 <= (unsigned_last_nbits ((qmid + 1 )) (32))) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_9_3_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid0 >= d0_pre)) (PreH3 : (rmid1 <= d1_pre)) (PreH4 : (rmid1 >= d1_pre)) (PreH5 : (0 <= n2_pre)) (PreH6 : (n2_pre <= UINT_MAX)) (PreH7 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH8 : (0 <= n1_pre)) (PreH9 : (n1_pre <= UINT_MAX)) (PreH10 : (0 <= n0_pre)) (PreH11 : (n0_pre <= UINT_MAX)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH13 : (d1_pre <= UINT_MAX)) (PreH14 : (0 <= d0_pre)) (PreH15 : (d0_pre <= UINT_MAX)) (PreH16 : (0 <= dinv_pre)) (PreH17 : (dinv_pre <= UINT_MAX)) (PreH18 : (0 <= qmid)) (PreH19 : (qmid <= UINT_MAX)) (PreH20 : (0 <= rmid1)) (PreH21 : (rmid1 <= UINT_MAX)) (PreH22 : (0 <= rmid0)) (PreH23 : (rmid0 <= UINT_MAX)) (PreH24 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH25 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = ((((unsigned_last_nbits ((qmid + 1 )) (32)) * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) ) + (rmid0 - d0_pre ) ))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_3_split_goal_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid0 >= d0_pre)) (PreH3 : (rmid1 <= d1_pre)) (PreH4 : (rmid1 >= d1_pre)) (PreH5 : (0 <= n2_pre)) (PreH6 : (n2_pre <= UINT_MAX)) (PreH7 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH8 : (0 <= n1_pre)) (PreH9 : (n1_pre <= UINT_MAX)) (PreH10 : (0 <= n0_pre)) (PreH11 : (n0_pre <= UINT_MAX)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH13 : (d1_pre <= UINT_MAX)) (PreH14 : (0 <= d0_pre)) (PreH15 : (d0_pre <= UINT_MAX)) (PreH16 : (0 <= dinv_pre)) (PreH17 : (dinv_pre <= UINT_MAX)) (PreH18 : (0 <= qmid)) (PreH19 : (qmid <= UINT_MAX)) (PreH20 : (0 <= rmid1)) (PreH21 : (rmid1 <= UINT_MAX)) (PreH22 : (0 <= rmid0)) (PreH23 : (rmid0 <= UINT_MAX)) (PreH24 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH25 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (((((rmid1 - d1_pre ) - 0 ) * UINT_MOD ) + (rmid0 - d0_pre ) ) < ((d1_pre * UINT_MOD ) + d0_pre ))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_3_split_goal_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid0 >= d0_pre)) (PreH3 : (rmid1 <= d1_pre)) (PreH4 : (rmid1 >= d1_pre)) (PreH5 : (0 <= n2_pre)) (PreH6 : (n2_pre <= UINT_MAX)) (PreH7 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH8 : (0 <= n1_pre)) (PreH9 : (n1_pre <= UINT_MAX)) (PreH10 : (0 <= n0_pre)) (PreH11 : (n0_pre <= UINT_MAX)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH13 : (d1_pre <= UINT_MAX)) (PreH14 : (0 <= d0_pre)) (PreH15 : (d0_pre <= UINT_MAX)) (PreH16 : (0 <= dinv_pre)) (PreH17 : (dinv_pre <= UINT_MAX)) (PreH18 : (0 <= qmid)) (PreH19 : (qmid <= UINT_MAX)) (PreH20 : (0 <= rmid1)) (PreH21 : (rmid1 <= UINT_MAX)) (PreH22 : (0 <= rmid0)) (PreH23 : (rmid0 <= UINT_MAX)) (PreH24 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH25 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((unsigned_last_nbits ((qmid + 1 )) (32)) <= UINT_MAX)
.

Definition gmp_udiv_qr_3by2_entail_wit_9_3_split_goal_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 >= d0_pre)) (PreH2 : (rmid0 >= d0_pre)) (PreH3 : (rmid1 <= d1_pre)) (PreH4 : (rmid1 >= d1_pre)) (PreH5 : (0 <= n2_pre)) (PreH6 : (n2_pre <= UINT_MAX)) (PreH7 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH8 : (0 <= n1_pre)) (PreH9 : (n1_pre <= UINT_MAX)) (PreH10 : (0 <= n0_pre)) (PreH11 : (n0_pre <= UINT_MAX)) (PreH12 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH13 : (d1_pre <= UINT_MAX)) (PreH14 : (0 <= d0_pre)) (PreH15 : (d0_pre <= UINT_MAX)) (PreH16 : (0 <= dinv_pre)) (PreH17 : (dinv_pre <= UINT_MAX)) (PreH18 : (0 <= qmid)) (PreH19 : (qmid <= UINT_MAX)) (PreH20 : (0 <= rmid1)) (PreH21 : (rmid1 <= UINT_MAX)) (PreH22 : (0 <= rmid0)) (PreH23 : (rmid0 <= UINT_MAX)) (PreH24 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH25 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (0 <= (unsigned_last_nbits ((qmid + 1 )) (32)))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_4 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 <= d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= qmid) ” 
  &&  “ (qmid <= UINT_MAX) ” 
  &&  “ (0 <= rmid1) ” 
  &&  “ (rmid1 <= UINT_MAX) ” 
  &&  “ (0 <= rmid0) ” 
  &&  “ (rmid0 <= UINT_MAX) ” 
  &&  “ (((rmid1 * UINT_MOD ) + rmid0 ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 <= d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  TT && emp 
|--
  “ (((rmid1 * UINT_MOD ) + rmid0 ) < ((d1_pre * UINT_MOD ) + d0_pre )) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_9_4_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid0 < d0_pre)) (PreH2 : (rmid1 <= d1_pre)) (PreH3 : (rmid1 >= d1_pre)) (PreH4 : (0 <= n2_pre)) (PreH5 : (n2_pre <= UINT_MAX)) (PreH6 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH7 : (0 <= n1_pre)) (PreH8 : (n1_pre <= UINT_MAX)) (PreH9 : (0 <= n0_pre)) (PreH10 : (n0_pre <= UINT_MAX)) (PreH11 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH12 : (d1_pre <= UINT_MAX)) (PreH13 : (0 <= d0_pre)) (PreH14 : (d0_pre <= UINT_MAX)) (PreH15 : (0 <= dinv_pre)) (PreH16 : (dinv_pre <= UINT_MAX)) (PreH17 : (0 <= qmid)) (PreH18 : (qmid <= UINT_MAX)) (PreH19 : (0 <= rmid1)) (PreH20 : (rmid1 <= UINT_MAX)) (PreH21 : (0 <= rmid0)) (PreH22 : (rmid0 <= UINT_MAX)) (PreH23 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH24 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (((rmid1 * UINT_MOD ) + rmid0 ) < ((d1_pre * UINT_MOD ) + d0_pre ))
.

Definition gmp_udiv_qr_3by2_entail_wit_9_5 := 
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid1 < d1_pre)) (PreH2 : (0 <= n2_pre)) (PreH3 : (n2_pre <= UINT_MAX)) (PreH4 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH5 : (0 <= n1_pre)) (PreH6 : (n1_pre <= UINT_MAX)) (PreH7 : (0 <= n0_pre)) (PreH8 : (n0_pre <= UINT_MAX)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH10 : (d1_pre <= UINT_MAX)) (PreH11 : (0 <= d0_pre)) (PreH12 : (d0_pre <= UINT_MAX)) (PreH13 : (0 <= dinv_pre)) (PreH14 : (dinv_pre <= UINT_MAX)) (PreH15 : (0 <= qmid)) (PreH16 : (qmid <= UINT_MAX)) (PreH17 : (0 <= rmid1)) (PreH18 : (rmid1 <= UINT_MAX)) (PreH19 : (0 <= rmid0)) (PreH20 : (rmid0 <= UINT_MAX)) (PreH21 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH22 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (0 <= qmid) ” 
  &&  “ (qmid <= UINT_MAX) ” 
  &&  “ (0 <= rmid1) ” 
  &&  “ (rmid1 <= UINT_MAX) ” 
  &&  “ (0 <= rmid0) ” 
  &&  “ (rmid0 <= UINT_MAX) ” 
  &&  “ (((rmid1 * UINT_MOD ) + rmid0 ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
) \/
(
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid1 < d1_pre)) (PreH2 : (0 <= n2_pre)) (PreH3 : (n2_pre <= UINT_MAX)) (PreH4 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH5 : (0 <= n1_pre)) (PreH6 : (n1_pre <= UINT_MAX)) (PreH7 : (0 <= n0_pre)) (PreH8 : (n0_pre <= UINT_MAX)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH10 : (d1_pre <= UINT_MAX)) (PreH11 : (0 <= d0_pre)) (PreH12 : (d0_pre <= UINT_MAX)) (PreH13 : (0 <= dinv_pre)) (PreH14 : (dinv_pre <= UINT_MAX)) (PreH15 : (0 <= qmid)) (PreH16 : (qmid <= UINT_MAX)) (PreH17 : (0 <= rmid1)) (PreH18 : (rmid1 <= UINT_MAX)) (PreH19 : (0 <= rmid0)) (PreH20 : (rmid0 <= UINT_MAX)) (PreH21 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH22 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  TT && emp 
|--
  “ (((rmid1 * UINT_MOD ) + rmid0 ) < ((d1_pre * UINT_MOD ) + d0_pre )) ”
  &&  emp
).

Definition gmp_udiv_qr_3by2_entail_wit_9_5_split_goal_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (qmid: Z) (rmid1: Z) (rmid0: Z) (PreH1 : (rmid1 < d1_pre)) (PreH2 : (0 <= n2_pre)) (PreH3 : (n2_pre <= UINT_MAX)) (PreH4 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH5 : (0 <= n1_pre)) (PreH6 : (n1_pre <= UINT_MAX)) (PreH7 : (0 <= n0_pre)) (PreH8 : (n0_pre <= UINT_MAX)) (PreH9 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH10 : (d1_pre <= UINT_MAX)) (PreH11 : (0 <= d0_pre)) (PreH12 : (d0_pre <= UINT_MAX)) (PreH13 : (0 <= dinv_pre)) (PreH14 : (dinv_pre <= UINT_MAX)) (PreH15 : (0 <= qmid)) (PreH16 : (qmid <= UINT_MAX)) (PreH17 : (0 <= rmid1)) (PreH18 : (rmid1 <= UINT_MAX)) (PreH19 : (0 <= rmid0)) (PreH20 : (rmid0 <= UINT_MAX)) (PreH21 : (((rmid1 * UINT_MOD ) + rmid0 ) < (2 * ((d1_pre * UINT_MOD ) + d0_pre ) ))) (PreH22 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qmid * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rmid1 * UINT_MOD ) ) + rmid0 ))) ,
  (((rmid1 * UINT_MOD ) + rmid0 ) < ((d1_pre * UINT_MOD ) + d0_pre ))
.

Definition gmp_udiv_qr_3by2_return_wit_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (qout: Z) (rv1out: Z) (rv0out: Z) (PreH1 : (0 <= n2_pre)) (PreH2 : (n2_pre <= UINT_MAX)) (PreH3 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH4 : (0 <= n1_pre)) (PreH5 : (n1_pre <= UINT_MAX)) (PreH6 : (0 <= n0_pre)) (PreH7 : (n0_pre <= UINT_MAX)) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH9 : (d1_pre <= UINT_MAX)) (PreH10 : (0 <= d0_pre)) (PreH11 : (d0_pre <= UINT_MAX)) (PreH12 : (0 <= dinv_pre)) (PreH13 : (dinv_pre <= UINT_MAX)) (PreH14 : (0 <= qout)) (PreH15 : (qout <= UINT_MAX)) (PreH16 : (0 <= rv1out)) (PreH17 : (rv1out <= UINT_MAX)) (PreH18 : (0 <= rv0out)) (PreH19 : (rv0out <= UINT_MAX)) (PreH20 : (((rv1out * UINT_MOD ) + rv0out ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH21 : ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qout * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rv1out * UINT_MOD ) ) + rv0out ))) ,
  ((q_pre) # UInt  |-> qout)
  **  ((r1_pre) # UInt  |-> rv1out)
  **  ((r0_pre) # UInt  |-> rv0out)
|--
  EX (rv0: Z)  (rv1: Z)  (qv: Z) ,
  “ (0 <= qv) ” 
  &&  “ (qv <= UINT_MAX) ” 
  &&  “ (0 <= rv1) ” 
  &&  “ (rv1 <= UINT_MAX) ” 
  &&  “ (0 <= rv0) ” 
  &&  “ (rv0 <= UINT_MAX) ” 
  &&  “ (((rv1 * UINT_MOD ) + rv0 ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((((n2_pre * (Z.pow (UINT_MOD) (2)) ) + (n1_pre * UINT_MOD ) ) + n0_pre ) = (((qv * ((d1_pre * UINT_MOD ) + d0_pre ) ) + (rv1 * UINT_MOD ) ) + rv0 )) ”
  &&  ((q_pre) # UInt  |-> qv)
  **  ((r1_pre) # UInt  |-> rv1)
  **  ((r0_pre) # UInt  |-> rv0)
.

Definition gmp_udiv_qr_3by2_partial_solve_wit_1 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (PreH1 : (0 <= n2_pre)) (PreH2 : (n2_pre <= UINT_MAX)) (PreH3 : (0 <= n1_pre)) (PreH4 : (n1_pre <= UINT_MAX)) (PreH5 : (0 <= n0_pre)) (PreH6 : (n0_pre <= UINT_MAX)) (PreH7 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH8 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH9 : (d1_pre <= UINT_MAX)) (PreH10 : (0 <= d0_pre)) (PreH11 : (d0_pre <= UINT_MAX)) (PreH12 : (0 <= dinv_pre)) (PreH13 : (dinv_pre <= UINT_MAX)) (PreH14 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH15 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_partial_solve_wit_2 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (n0_pre >= d0_pre)) (PreH2 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value)) (PreH3 : (0 <= w1_value)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : (w0_value >= 0)) (PreH6 : (0 <= w0_value)) (PreH7 : (w0_value <= UINT_MAX)) (PreH8 : (w1_value <= UINT_MAX)) (PreH9 : (dinv_pre >= 0)) (PreH10 : (d0_pre >= 0)) (PreH11 : (d1_pre >= 0)) (PreH12 : (n0_pre >= 0)) (PreH13 : (n1_pre >= 0)) (PreH14 : (n2_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH17 : (0 <= n2_pre)) (PreH18 : (n2_pre <= UINT_MAX)) (PreH19 : (0 <= n1_pre)) (PreH20 : (n1_pre <= UINT_MAX)) (PreH21 : (0 <= n0_pre)) (PreH22 : (n0_pre <= UINT_MAX)) (PreH23 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH24 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH25 : (d1_pre <= UINT_MAX)) (PreH26 : (0 <= d0_pre)) (PreH27 : (d0_pre <= UINT_MAX)) (PreH28 : (0 <= dinv_pre)) (PreH29 : (dinv_pre <= UINT_MAX)) (PreH30 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH31 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (n0_pre >= d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_partial_solve_wit_3 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (n0_pre < d0_pre)) (PreH2 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value)) (PreH3 : (0 <= w1_value)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : (w0_value >= 0)) (PreH6 : (0 <= w0_value)) (PreH7 : (w0_value <= UINT_MAX)) (PreH8 : (w1_value <= UINT_MAX)) (PreH9 : (dinv_pre >= 0)) (PreH10 : (d0_pre >= 0)) (PreH11 : (d1_pre >= 0)) (PreH12 : (n0_pre >= 0)) (PreH13 : (n1_pre >= 0)) (PreH14 : (n2_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH17 : (0 <= n2_pre)) (PreH18 : (n2_pre <= UINT_MAX)) (PreH19 : (0 <= n1_pre)) (PreH20 : (n1_pre <= UINT_MAX)) (PreH21 : (0 <= n0_pre)) (PreH22 : (n0_pre <= UINT_MAX)) (PreH23 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH24 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH25 : (d1_pre <= UINT_MAX)) (PreH26 : (0 <= d0_pre)) (PreH27 : (d0_pre <= UINT_MAX)) (PreH28 : (0 <= dinv_pre)) (PreH29 : (dinv_pre <= UINT_MAX)) (PreH30 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH31 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (n0_pre < d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) >= w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_partial_solve_wit_4 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (n0_pre >= d0_pre)) (PreH2 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value)) (PreH3 : (0 <= w1_value)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : (w0_value >= 0)) (PreH6 : (0 <= w0_value)) (PreH7 : (w0_value <= UINT_MAX)) (PreH8 : (w1_value <= UINT_MAX)) (PreH9 : (dinv_pre >= 0)) (PreH10 : (d0_pre >= 0)) (PreH11 : (d1_pre >= 0)) (PreH12 : (n0_pre >= 0)) (PreH13 : (n1_pre >= 0)) (PreH14 : (n2_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH17 : (0 <= n2_pre)) (PreH18 : (n2_pre <= UINT_MAX)) (PreH19 : (0 <= n1_pre)) (PreH20 : (n1_pre <= UINT_MAX)) (PreH21 : (0 <= n0_pre)) (PreH22 : (n0_pre <= UINT_MAX)) (PreH23 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH24 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH25 : (d1_pre <= UINT_MAX)) (PreH26 : (0 <= d0_pre)) (PreH27 : (d0_pre <= UINT_MAX)) (PreH28 : (0 <= dinv_pre)) (PreH29 : (dinv_pre <= UINT_MAX)) (PreH30 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH31 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (n0_pre >= d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Definition gmp_udiv_qr_3by2_partial_solve_wit_5 := 
forall (dinv_pre: Z) (d0_pre: Z) (d1_pre: Z) (n0_pre: Z) (n1_pre: Z) (n2_pre: Z) (r0_pre: Z) (r1_pre: Z) (q_pre: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (n0_pre < d0_pre)) (PreH2 : ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value)) (PreH3 : (0 <= w1_value)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : (w0_value >= 0)) (PreH6 : (0 <= w0_value)) (PreH7 : (w0_value <= UINT_MAX)) (PreH8 : (w1_value <= UINT_MAX)) (PreH9 : (dinv_pre >= 0)) (PreH10 : (d0_pre >= 0)) (PreH11 : (d1_pre >= 0)) (PreH12 : (n0_pre >= 0)) (PreH13 : (n1_pre >= 0)) (PreH14 : (n2_pre >= 0)) (PreH15 : (w1_value >= 0)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre ))) (PreH17 : (0 <= n2_pre)) (PreH18 : (n2_pre <= UINT_MAX)) (PreH19 : (0 <= n1_pre)) (PreH20 : (n1_pre <= UINT_MAX)) (PreH21 : (0 <= n0_pre)) (PreH22 : (n0_pre <= UINT_MAX)) (PreH23 : (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre ))) (PreH24 : ((UINT_MOD ÷ 2 ) <= d1_pre)) (PreH25 : (d1_pre <= UINT_MAX)) (PreH26 : (0 <= d0_pre)) (PreH27 : (d0_pre <= UINT_MAX)) (PreH28 : (0 <= dinv_pre)) (PreH29 : (dinv_pre <= UINT_MAX)) (PreH30 : (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 ))) (PreH31 : (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) ))) ,
  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
|--
  “ (n0_pre < d0_pre) ” 
  &&  “ ((unsigned_last_nbits ((w0_value + n1_pre )) (32)) < w0_value) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (dinv_pre >= 0) ” 
  &&  “ (d0_pre >= 0) ” 
  &&  “ (d1_pre >= 0) ” 
  &&  “ (n0_pre >= 0) ” 
  &&  “ (n1_pre >= 0) ” 
  &&  “ (n2_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = (n2_pre * dinv_pre )) ” 
  &&  “ (0 <= n2_pre) ” 
  &&  “ (n2_pre <= UINT_MAX) ” 
  &&  “ (0 <= n1_pre) ” 
  &&  “ (n1_pre <= UINT_MAX) ” 
  &&  “ (0 <= n0_pre) ” 
  &&  “ (n0_pre <= UINT_MAX) ” 
  &&  “ (((n2_pre * UINT_MOD ) + n1_pre ) < ((d1_pre * UINT_MOD ) + d0_pre )) ” 
  &&  “ ((UINT_MOD ÷ 2 ) <= d1_pre) ” 
  &&  “ (d1_pre <= UINT_MAX) ” 
  &&  “ (0 <= d0_pre) ” 
  &&  “ (d0_pre <= UINT_MAX) ” 
  &&  “ (0 <= dinv_pre) ” 
  &&  “ (dinv_pre <= UINT_MAX) ” 
  &&  “ (((dinv_pre + UINT_MOD ) * ((UINT_MOD * d1_pre ) + d0_pre ) ) <= ((Z.pow (UINT_MOD) (3)) - 1 )) ” 
  &&  “ (((Z.pow (UINT_MOD) (3)) - 1 ) < (((dinv_pre + UINT_MOD ) + 1 ) * ((UINT_MOD * d1_pre ) + d0_pre ) )) ”
  &&  ((q_pre) # UInt  |->_)
  **  ((r1_pre) # UInt  |->_)
  **  ((r0_pre) # UInt  |->_)
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_1 : gmp_udiv_qr_3by2_safety_wit_1.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_2 : gmp_udiv_qr_3by2_safety_wit_2.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_3 : gmp_udiv_qr_3by2_safety_wit_3.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_4 : gmp_udiv_qr_3by2_safety_wit_4.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_5 : gmp_udiv_qr_3by2_safety_wit_5.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_6 : gmp_udiv_qr_3by2_safety_wit_6.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_7 : gmp_udiv_qr_3by2_safety_wit_7.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_8 : gmp_udiv_qr_3by2_safety_wit_8.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_9 : gmp_udiv_qr_3by2_safety_wit_9.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_10 : gmp_udiv_qr_3by2_safety_wit_10.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_11 : gmp_udiv_qr_3by2_safety_wit_11.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_12 : gmp_udiv_qr_3by2_safety_wit_12.
Axiom proof_of_gmp_udiv_qr_3by2_safety_wit_13 : gmp_udiv_qr_3by2_safety_wit_13.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_1 : gmp_udiv_qr_3by2_entail_wit_1.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_2 : gmp_udiv_qr_3by2_entail_wit_2.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_3_1 : gmp_udiv_qr_3by2_entail_wit_3_1.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_3_2 : gmp_udiv_qr_3by2_entail_wit_3_2.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_3_3 : gmp_udiv_qr_3by2_entail_wit_3_3.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_3_4 : gmp_udiv_qr_3by2_entail_wit_3_4.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_4_1 : gmp_udiv_qr_3by2_entail_wit_4_1.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_4_2 : gmp_udiv_qr_3by2_entail_wit_4_2.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_4_3 : gmp_udiv_qr_3by2_entail_wit_4_3.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_4_4 : gmp_udiv_qr_3by2_entail_wit_4_4.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_5_1 : gmp_udiv_qr_3by2_entail_wit_5_1.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_5_2 : gmp_udiv_qr_3by2_entail_wit_5_2.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_5_3 : gmp_udiv_qr_3by2_entail_wit_5_3.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_5_4 : gmp_udiv_qr_3by2_entail_wit_5_4.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_5_5 : gmp_udiv_qr_3by2_entail_wit_5_5.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_5_6 : gmp_udiv_qr_3by2_entail_wit_5_6.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_5_7 : gmp_udiv_qr_3by2_entail_wit_5_7.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_5_8 : gmp_udiv_qr_3by2_entail_wit_5_8.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_6_1 : gmp_udiv_qr_3by2_entail_wit_6_1.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_6_2 : gmp_udiv_qr_3by2_entail_wit_6_2.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_6_3 : gmp_udiv_qr_3by2_entail_wit_6_3.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_7_1 : gmp_udiv_qr_3by2_entail_wit_7_1.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_7_2 : gmp_udiv_qr_3by2_entail_wit_7_2.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_7_3 : gmp_udiv_qr_3by2_entail_wit_7_3.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_7_4 : gmp_udiv_qr_3by2_entail_wit_7_4.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_7_5 : gmp_udiv_qr_3by2_entail_wit_7_5.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_7_6 : gmp_udiv_qr_3by2_entail_wit_7_6.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_1 : gmp_udiv_qr_3by2_entail_wit_8_1.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_2 : gmp_udiv_qr_3by2_entail_wit_8_2.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_3 : gmp_udiv_qr_3by2_entail_wit_8_3.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_4 : gmp_udiv_qr_3by2_entail_wit_8_4.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_5 : gmp_udiv_qr_3by2_entail_wit_8_5.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_6 : gmp_udiv_qr_3by2_entail_wit_8_6.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_7 : gmp_udiv_qr_3by2_entail_wit_8_7.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_8 : gmp_udiv_qr_3by2_entail_wit_8_8.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_9 : gmp_udiv_qr_3by2_entail_wit_8_9.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_10 : gmp_udiv_qr_3by2_entail_wit_8_10.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_11 : gmp_udiv_qr_3by2_entail_wit_8_11.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_8_12 : gmp_udiv_qr_3by2_entail_wit_8_12.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_9_1 : gmp_udiv_qr_3by2_entail_wit_9_1.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_9_2 : gmp_udiv_qr_3by2_entail_wit_9_2.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_9_3 : gmp_udiv_qr_3by2_entail_wit_9_3.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_9_4 : gmp_udiv_qr_3by2_entail_wit_9_4.
Axiom proof_of_gmp_udiv_qr_3by2_entail_wit_9_5 : gmp_udiv_qr_3by2_entail_wit_9_5.
Axiom proof_of_gmp_udiv_qr_3by2_return_wit_1 : gmp_udiv_qr_3by2_return_wit_1.
Axiom proof_of_gmp_udiv_qr_3by2_partial_solve_wit_1 : gmp_udiv_qr_3by2_partial_solve_wit_1.
Axiom proof_of_gmp_udiv_qr_3by2_partial_solve_wit_2 : gmp_udiv_qr_3by2_partial_solve_wit_2.
Axiom proof_of_gmp_udiv_qr_3by2_partial_solve_wit_3 : gmp_udiv_qr_3by2_partial_solve_wit_3.
Axiom proof_of_gmp_udiv_qr_3by2_partial_solve_wit_4 : gmp_udiv_qr_3by2_partial_solve_wit_4.
Axiom proof_of_gmp_udiv_qr_3by2_partial_solve_wit_5 : gmp_udiv_qr_3by2_partial_solve_wit_5.

End VC_Correct.
