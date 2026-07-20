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

(*----- Function gmp_clz -----*)

Definition gmp_clz_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= UINT_MAX)) ,
  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # UInt  |->_)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gmp_clz_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= UINT_MAX)) ,
  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # UInt  |-> 0)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition gmp_clz_safety_wit_3 := 
forall (x_pre: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= UINT_MAX)) ,
  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> 8)
  **  ((( &( "c" ) )) # UInt  |-> 0)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition gmp_clz_safety_wit_4 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : ((c % ( 8 ) ) = 0)) (PreH3 : (0 <= c)) (PreH4 : (c <= 24)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ ((32 - 8 ) <= 31) ” 
  &&  “ (0 <= (32 - 8 )) ”
.

Definition gmp_clz_safety_wit_5 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : ((c % ( 8 ) ) = 0)) (PreH3 : (0 <= c)) (PreH4 : (c <= 24)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ ((32 - 8 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (32 - 8 )) ”
.

Definition gmp_clz_safety_wit_6 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : ((c % ( 8 ) ) = 0)) (PreH3 : (0 <= c)) (PreH4 : (c <= 24)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition gmp_clz_safety_wit_7 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : ((c % ( 8 ) ) = 0)) (PreH3 : (0 <= c)) (PreH4 : (c <= 24)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition gmp_clz_safety_wit_8 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : ((c % ( 8 ) ) = 0)) (PreH3 : (0 <= c)) (PreH4 : (c <= 24)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gmp_clz_safety_wit_9 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 255 (32 - 8 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : ((c % ( 8 ) ) = 0)) (PreH4 : (0 <= c)) (PreH5 : (c <= 24)) (PreH6 : (0 < x)) (PreH7 : (x < (Z.pow (2) (32)))) (PreH8 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition gmp_clz_safety_wit_10 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 255 (32 - 8 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : ((c % ( 8 ) ) = 0)) (PreH4 : (0 <= c)) (PreH5 : (c <= 24)) (PreH6 : (0 < x)) (PreH7 : (x < (Z.pow (2) (32)))) (PreH8 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> (c + 8 ))
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (LOCAL_SHIFT_BITS <= 31) ” 
  &&  “ (0 <= LOCAL_SHIFT_BITS) ”
.

Definition gmp_clz_safety_wit_11 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : (0 <= c)) (PreH3 : (c <= 31)) (PreH4 : (0 < x)) (PreH5 : (x < (Z.pow (2) (32)))) (PreH6 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ ((32 - 1 ) <= 31) ” 
  &&  “ (0 <= (32 - 1 )) ”
.

Definition gmp_clz_safety_wit_12 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : (0 <= c)) (PreH3 : (c <= 31)) (PreH4 : (0 < x)) (PreH5 : (x < (Z.pow (2) (32)))) (PreH6 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ ((32 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (32 - 1 )) ”
.

Definition gmp_clz_safety_wit_13 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : (0 <= c)) (PreH3 : (c <= 31)) (PreH4 : (0 < x)) (PreH5 : (x < (Z.pow (2) (32)))) (PreH6 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition gmp_clz_safety_wit_14 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : (0 <= c)) (PreH3 : (c <= 31)) (PreH4 : (0 < x)) (PreH5 : (x < (Z.pow (2) (32)))) (PreH6 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gmp_clz_safety_wit_15 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : (0 <= c)) (PreH3 : (c <= 31)) (PreH4 : (0 < x)) (PreH5 : (x < (Z.pow (2) (32)))) (PreH6 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gmp_clz_safety_wit_16 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> c)
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gmp_clz_safety_wit_17 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> (c + 1 ))
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (1 <= 31) ” 
  &&  “ (0 <= 1) ”
.

Definition gmp_clz_safety_wit_18 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((( &( "x" ) )) # UInt  |-> x)
  **  ((( &( "c" ) )) # UInt  |-> (c + 1 ))
  **  ((( &( "LOCAL_SHIFT_BITS" ) )) # Int  |-> LOCAL_SHIFT_BITS)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition gmp_clz_entail_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= UINT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (x_pre * (Z.pow (2) (0)) )) ” 
  &&  “ ((0 % ( 8 ) ) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 24) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (x_pre < (Z.pow (2) (32))) ” 
  &&  “ (8 = 8) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= UINT_MAX)) ,
  TT && emp 
|--
  “ (x_pre < (Z.pow (2) (32))) ” 
  &&  “ (x_pre = (x_pre * (Z.pow (2) (0)) )) ”
  &&  emp
).

Definition gmp_clz_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= UINT_MAX)) ,
  (x_pre < (Z.pow (2) (32)))
.

Definition gmp_clz_entail_wit_1_split_goal_2 := 
forall (x_pre: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= UINT_MAX)) ,
  (x_pre = (x_pre * (Z.pow (2) (0)) ))
.

Definition gmp_clz_entail_wit_2 := 
(
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 255 (32 - 8 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : ((c % ( 8 ) ) = 0)) (PreH4 : (0 <= c)) (PreH5 : (c <= 24)) (PreH6 : (0 < x)) (PreH7 : (x < (Z.pow (2) (32)))) (PreH8 : (LOCAL_SHIFT_BITS = 8)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((Z.shiftl x LOCAL_SHIFT_BITS)) (32)) = (x_pre * (Z.pow (2) ((c + 8 ))) )) ” 
  &&  “ (((c + 8 ) % ( 8 ) ) = 0) ” 
  &&  “ (0 <= (c + 8 )) ” 
  &&  “ ((c + 8 ) <= 24) ” 
  &&  “ (0 < (unsigned_last_nbits ((Z.shiftl x LOCAL_SHIFT_BITS)) (32))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl x LOCAL_SHIFT_BITS)) (32)) < (Z.pow (2) (32))) ” 
  &&  “ (LOCAL_SHIFT_BITS = 8) ”
  &&  emp
) \/
(
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 255 (32 - 8 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : ((c % ( 8 ) ) = 0)) (PreH4 : (0 <= c)) (PreH5 : (c <= 24)) (PreH6 : (0 < x)) (PreH7 : (x < (Z.pow (2) (32)))) (PreH8 : (LOCAL_SHIFT_BITS = 8)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((Z.shiftl x LOCAL_SHIFT_BITS)) (32)) < (Z.pow (2) (32))) ” 
  &&  “ (0 < (unsigned_last_nbits ((Z.shiftl x LOCAL_SHIFT_BITS)) (32))) ” 
  &&  “ ((c + 8 ) <= 24) ” 
  &&  “ (((c + 8 ) % ( 8 ) ) = 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl x LOCAL_SHIFT_BITS)) (32)) = (x_pre * (Z.pow (2) ((c + 8 ))) )) ”
  &&  emp
).

Definition gmp_clz_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 255 (32 - 8 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : ((c % ( 8 ) ) = 0)) (PreH4 : (0 <= c)) (PreH5 : (c <= 24)) (PreH6 : (0 < x)) (PreH7 : (x < (Z.pow (2) (32)))) (PreH8 : (LOCAL_SHIFT_BITS = 8)) ,
  ((unsigned_last_nbits ((Z.shiftl x LOCAL_SHIFT_BITS)) (32)) < (Z.pow (2) (32)))
.

Definition gmp_clz_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 255 (32 - 8 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : ((c % ( 8 ) ) = 0)) (PreH4 : (0 <= c)) (PreH5 : (c <= 24)) (PreH6 : (0 < x)) (PreH7 : (x < (Z.pow (2) (32)))) (PreH8 : (LOCAL_SHIFT_BITS = 8)) ,
  (0 < (unsigned_last_nbits ((Z.shiftl x LOCAL_SHIFT_BITS)) (32)))
.

Definition gmp_clz_entail_wit_2_split_goal_3 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 255 (32 - 8 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : ((c % ( 8 ) ) = 0)) (PreH4 : (0 <= c)) (PreH5 : (c <= 24)) (PreH6 : (0 < x)) (PreH7 : (x < (Z.pow (2) (32)))) (PreH8 : (LOCAL_SHIFT_BITS = 8)) ,
  ((c + 8 ) <= 24)
.

Definition gmp_clz_entail_wit_2_split_goal_4 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 255 (32 - 8 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : ((c % ( 8 ) ) = 0)) (PreH4 : (0 <= c)) (PreH5 : (c <= 24)) (PreH6 : (0 < x)) (PreH7 : (x < (Z.pow (2) (32)))) (PreH8 : (LOCAL_SHIFT_BITS = 8)) ,
  (((c + 8 ) % ( 8 ) ) = 0)
.

Definition gmp_clz_entail_wit_2_split_goal_5 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 255 (32 - 8 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : ((c % ( 8 ) ) = 0)) (PreH4 : (0 <= c)) (PreH5 : (c <= 24)) (PreH6 : (0 < x)) (PreH7 : (x < (Z.pow (2) (32)))) (PreH8 : (LOCAL_SHIFT_BITS = 8)) ,
  ((unsigned_last_nbits ((Z.shiftl x LOCAL_SHIFT_BITS)) (32)) = (x_pre * (Z.pow (2) ((c + 8 ))) ))
.

Definition gmp_clz_entail_wit_3 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 255 (32 - 8 ))) <> 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : ((c % ( 8 ) ) = 0)) (PreH4 : (0 <= c)) (PreH5 : (c <= 24)) (PreH6 : (0 < x)) (PreH7 : (x < (Z.pow (2) (32)))) (PreH8 : (LOCAL_SHIFT_BITS = 8)) ,
  TT && emp 
|--
  “ (x = (x_pre * (Z.pow (2) (c)) )) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= 31) ” 
  &&  “ (0 < x) ” 
  &&  “ (x < (Z.pow (2) (32))) ” 
  &&  “ (LOCAL_SHIFT_BITS = 8) ”
  &&  emp
.

Definition gmp_clz_entail_wit_4 := 
forall (x_pre: Z) (x: Z) (c: Z) (LOCAL_SHIFT_BITS: Z) (PreH1 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH2 : (0 <= c)) (PreH3 : (c <= 31)) (PreH4 : (0 < x)) (PreH5 : (x < (Z.pow (2) (32)))) (PreH6 : (LOCAL_SHIFT_BITS = 8)) ,
  TT && emp 
|--
  “ (x = (x_pre * (Z.pow (2) (c)) )) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= 31) ” 
  &&  “ (0 < x) ” 
  &&  “ (x < (Z.pow (2) (32))) ” 
  &&  “ (LOCAL_SHIFT_BITS = 8) ”
  &&  emp
.

Definition gmp_clz_entail_wit_5 := 
(
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((Z.shiftl x 1)) (32)) = (x_pre * (Z.pow (2) ((c + 1 ))) )) ” 
  &&  “ (0 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= 31) ” 
  &&  “ (0 < (unsigned_last_nbits ((Z.shiftl x 1)) (32))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl x 1)) (32)) < (Z.pow (2) (32))) ” 
  &&  “ (LOCAL_SHIFT_BITS = 8) ”
  &&  emp
) \/
(
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((Z.shiftl x 1)) (32)) < (Z.pow (2) (32))) ” 
  &&  “ (0 < (unsigned_last_nbits ((Z.shiftl x 1)) (32))) ” 
  &&  “ ((c + 1 ) <= 31) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl x 1)) (32)) = (x_pre * (Z.pow (2) ((c + 1 ))) )) ”
  &&  emp
).

Definition gmp_clz_entail_wit_5_split_goal_1 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((unsigned_last_nbits ((Z.shiftl x 1)) (32)) < (Z.pow (2) (32)))
.

Definition gmp_clz_entail_wit_5_split_goal_2 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  (0 < (unsigned_last_nbits ((Z.shiftl x 1)) (32)))
.

Definition gmp_clz_entail_wit_5_split_goal_3 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((c + 1 ) <= 31)
.

Definition gmp_clz_entail_wit_5_split_goal_4 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) = 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((unsigned_last_nbits ((Z.shiftl x 1)) (32)) = (x_pre * (Z.pow (2) ((c + 1 ))) ))
.

Definition gmp_clz_return_wit_1 := 
(
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) <> 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  TT && emp 
|--
  “ (0 <= c) ” 
  &&  “ (c < 32) ” 
  &&  “ ((Z.pow (2) (31)) <= (x_pre * (Z.pow (2) (c)) )) ” 
  &&  “ ((x_pre * (Z.pow (2) (c)) ) < (Z.pow (2) (32))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) <> 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  TT && emp 
|--
  “ ((Z.pow (2) (31)) <= (x_pre * (Z.pow (2) (c)) )) ”
  &&  emp
).

Definition gmp_clz_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (LOCAL_SHIFT_BITS: Z) (c: Z) (x: Z) (PreH1 : ((Z.land x (Z.shiftl 1 (32 - 1 ))) <> 0)) (PreH2 : (x = (x_pre * (Z.pow (2) (c)) ))) (PreH3 : (0 <= c)) (PreH4 : (c <= 31)) (PreH5 : (0 < x)) (PreH6 : (x < (Z.pow (2) (32)))) (PreH7 : (LOCAL_SHIFT_BITS = 8)) ,
  ((Z.pow (2) (31)) <= (x_pre * (Z.pow (2) (c)) ))
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_gmp_clz_safety_wit_1 : gmp_clz_safety_wit_1.
Axiom proof_of_gmp_clz_safety_wit_2 : gmp_clz_safety_wit_2.
Axiom proof_of_gmp_clz_safety_wit_3 : gmp_clz_safety_wit_3.
Axiom proof_of_gmp_clz_safety_wit_4 : gmp_clz_safety_wit_4.
Axiom proof_of_gmp_clz_safety_wit_5 : gmp_clz_safety_wit_5.
Axiom proof_of_gmp_clz_safety_wit_6 : gmp_clz_safety_wit_6.
Axiom proof_of_gmp_clz_safety_wit_7 : gmp_clz_safety_wit_7.
Axiom proof_of_gmp_clz_safety_wit_8 : gmp_clz_safety_wit_8.
Axiom proof_of_gmp_clz_safety_wit_9 : gmp_clz_safety_wit_9.
Axiom proof_of_gmp_clz_safety_wit_10 : gmp_clz_safety_wit_10.
Axiom proof_of_gmp_clz_safety_wit_11 : gmp_clz_safety_wit_11.
Axiom proof_of_gmp_clz_safety_wit_12 : gmp_clz_safety_wit_12.
Axiom proof_of_gmp_clz_safety_wit_13 : gmp_clz_safety_wit_13.
Axiom proof_of_gmp_clz_safety_wit_14 : gmp_clz_safety_wit_14.
Axiom proof_of_gmp_clz_safety_wit_15 : gmp_clz_safety_wit_15.
Axiom proof_of_gmp_clz_safety_wit_16 : gmp_clz_safety_wit_16.
Axiom proof_of_gmp_clz_safety_wit_17 : gmp_clz_safety_wit_17.
Axiom proof_of_gmp_clz_safety_wit_18 : gmp_clz_safety_wit_18.
Axiom proof_of_gmp_clz_entail_wit_1 : gmp_clz_entail_wit_1.
Axiom proof_of_gmp_clz_entail_wit_2 : gmp_clz_entail_wit_2.
Axiom proof_of_gmp_clz_entail_wit_3 : gmp_clz_entail_wit_3.
Axiom proof_of_gmp_clz_entail_wit_4 : gmp_clz_entail_wit_4.
Axiom proof_of_gmp_clz_entail_wit_5 : gmp_clz_entail_wit_5.
Axiom proof_of_gmp_clz_return_wit_1 : gmp_clz_return_wit_1.

End VC_Correct.
