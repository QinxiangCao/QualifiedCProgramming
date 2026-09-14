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
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib.
Local Open Scope sac.

(*----- Function modular_mul -----*)

Definition modular_mul_safety_wit_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((0 - modulus_pre ) < a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (0 < modulus_pre)) (PreH6 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  ((( &( "res" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition modular_mul_safety_wit_2 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((0 - modulus_pre ) < a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (0 < modulus_pre)) (PreH6 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  ((( &( "flag" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modular_mul_safety_wit_3 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((0 - modulus_pre ) < a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (0 < modulus_pre)) (PreH6 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  ((( &( "flag" ) )) # Int  |-> 1)
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition modular_mul_safety_wit_4 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre < 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  ((( &( "flag" ) )) # Int  |-> 1)
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (b_pre <> (INT_MIN)) ”
.

Definition modular_mul_safety_wit_5 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre < 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  ((( &( "flag" ) )) # Int  |-> 1)
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> (-b_pre))
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition modular_mul_safety_wit_6 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre < 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  ((( &( "flag" ) )) # Int  |-> 1)
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> (-b_pre))
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modular_mul_safety_wit_7 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((0 - modulus_pre ) < a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (0 < modulus_pre)) (PreH6 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH7 : (0 <= b)) (PreH8 : (b <= INT_MAX)) (PreH9 : (flag = (0 - 1 ))) (PreH10 : ((0 - modulus_pre ) < a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 - modulus_pre ) < res)) (PreH13 : (res < modulus_pre)) (PreH14 : (INT_MIN <= (res + a ))) (PreH15 : ((res + a ) <= INT_MAX)) (PreH16 : (INT_MIN <= (a + a ))) (PreH17 : ((a + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (res * flag ))) (PreH19 : ((res * flag ) <= INT_MAX)) (PreH20 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition modular_mul_safety_wit_8 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((0 - modulus_pre ) < a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (0 < modulus_pre)) (PreH6 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH7 : (0 <= b)) (PreH8 : (b <= INT_MAX)) (PreH9 : (flag = 1)) (PreH10 : ((0 - modulus_pre ) < a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 - modulus_pre ) < res)) (PreH13 : (res < modulus_pre)) (PreH14 : (INT_MIN <= (res + a ))) (PreH15 : ((res + a ) <= INT_MAX)) (PreH16 : (INT_MIN <= (a + a ))) (PreH17 : ((a + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (res * flag ))) (PreH19 : ((res * flag ) <= INT_MAX)) (PreH20 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition modular_mul_safety_wit_9 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b > 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = 1)) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((b <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_mul_safety_wit_10 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b > 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = (0 - 1 ))) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((b <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_mul_safety_wit_11 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b > 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = (0 - 1 ))) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_mul_safety_wit_12 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b > 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = 1)) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_mul_safety_wit_13 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b > 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = (0 - 1 ))) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modular_mul_safety_wit_14 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b > 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = 1)) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modular_mul_safety_wit_15 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (((res + a ) <> (INT_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_mul_safety_wit_16 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((res + a ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (res + a )) ”
.

Definition modular_mul_safety_wit_17 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (((res + a ) <> (INT_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_mul_safety_wit_18 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((res + a ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (res + a )) ”
.

Definition modular_mul_safety_wit_19 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> ((res + a ) % ( modulus_pre ) ))
|--
  “ ((b <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_mul_safety_wit_20 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> ((res + a ) % ( modulus_pre ) ))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_mul_safety_wit_21 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> ((res + a ) % ( modulus_pre ) ))
|--
  “ ((b <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_mul_safety_wit_22 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> ((res + a ) % ( modulus_pre ) ))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_mul_safety_wit_23 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((b <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_mul_safety_wit_24 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_mul_safety_wit_25 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((b <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_mul_safety_wit_26 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_mul_safety_wit_27 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> (b ÷ 2 ))
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> ((res + a ) % ( modulus_pre ) ))
|--
  “ (((a + a ) <> (INT_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_mul_safety_wit_28 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> (b ÷ 2 ))
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> ((res + a ) % ( modulus_pre ) ))
|--
  “ ((a + a ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a + a )) ”
.

Definition modular_mul_safety_wit_29 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> (b ÷ 2 ))
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> ((res + a ) % ( modulus_pre ) ))
|--
  “ (((a + a ) <> (INT_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_mul_safety_wit_30 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> (b ÷ 2 ))
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> ((res + a ) % ( modulus_pre ) ))
|--
  “ ((a + a ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a + a )) ”
.

Definition modular_mul_safety_wit_31 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> (b ÷ 2 ))
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (((a + a ) <> (INT_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_mul_safety_wit_32 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> (b ÷ 2 ))
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((a + a ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a + a )) ”
.

Definition modular_mul_safety_wit_33 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> (b ÷ 2 ))
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ (((a + a ) <> (INT_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_mul_safety_wit_34 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> (b ÷ 2 ))
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((a + a ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a + a )) ”
.

Definition modular_mul_safety_wit_35 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b <= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = 1)) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((res * flag ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (res * flag )) ”
.

Definition modular_mul_safety_wit_36 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b <= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = (0 - 1 ))) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((res * flag ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (res * flag )) ”
.

Definition modular_mul_entail_wit_1_1 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre < 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 - modulus_pre ) < a_pre) ” 
  &&  “ (a_pre < modulus_pre) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (0 < modulus_pre) ” 
  &&  “ ((modulus_pre * 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (-b_pre)) ” 
  &&  “ ((-b_pre) <= INT_MAX) ” 
  &&  “ ((-1) = (0 - 1 )) ” 
  &&  “ ((0 - modulus_pre ) < a_pre) ” 
  &&  “ (a_pre < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < 0) ” 
  &&  “ (0 < modulus_pre) ” 
  &&  “ (INT_MIN <= (0 + a_pre )) ” 
  &&  “ ((0 + a_pre ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (a_pre + a_pre )) ” 
  &&  “ ((a_pre + a_pre ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (0 * (-1) )) ” 
  &&  “ ((0 * (-1) ) <= INT_MAX) ” 
  &&  “ (ModularMulProgress a_pre b_pre modulus_pre a_pre (-b_pre) 0 (-1) ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre < 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre a_pre (-b_pre) 0 (-1) ) ”
  &&  emp
).

Definition modular_mul_entail_wit_1_1_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre < 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  (ModularMulProgress a_pre b_pre modulus_pre a_pre (-b_pre) 0 (-1) )
.

Definition modular_mul_entail_wit_1_2 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre >= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 - modulus_pre ) < a_pre) ” 
  &&  “ (a_pre < modulus_pre) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (0 < modulus_pre) ” 
  &&  “ ((modulus_pre * 2 ) <= INT_MAX) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((0 - modulus_pre ) < a_pre) ” 
  &&  “ (a_pre < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < 0) ” 
  &&  “ (0 < modulus_pre) ” 
  &&  “ (INT_MIN <= (0 + a_pre )) ” 
  &&  “ ((0 + a_pre ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (a_pre + a_pre )) ” 
  &&  “ ((a_pre + a_pre ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (0 * 1 )) ” 
  &&  “ ((0 * 1 ) <= INT_MAX) ” 
  &&  “ (ModularMulProgress a_pre b_pre modulus_pre a_pre b_pre 0 1 ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre >= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre a_pre b_pre 0 1 ) ”
  &&  emp
).

Definition modular_mul_entail_wit_1_2_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre >= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) ,
  (ModularMulProgress a_pre b_pre modulus_pre a_pre b_pre 0 1 )
.

Definition modular_mul_entail_wit_2_1 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ ((0 - modulus_pre ) < a_pre) ” 
  &&  “ (a_pre < modulus_pre) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (0 < modulus_pre) ” 
  &&  “ ((modulus_pre * 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (b ÷ 2 )) ” 
  &&  “ ((b ÷ 2 ) <= INT_MAX) ” 
  &&  “ (flag = (0 - 1 )) ” 
  &&  “ ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) )) ” 
  &&  “ (((a + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < ((res + a ) % ( modulus_pre ) )) ” 
  &&  “ (((res + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ (INT_MIN <= (((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((res + a ) % ( modulus_pre ) ) * flag )) ” 
  &&  “ ((((res + a ) % ( modulus_pre ) ) * flag ) <= INT_MAX) ” 
  &&  “ (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) ((res + a ) % ( modulus_pre ) ) flag ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) ((res + a ) % ( modulus_pre ) ) (0 - 1 ) ) ” 
  &&  “ ((((res + a ) % ( modulus_pre ) ) * (0 - 1 ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((res + a ) % ( modulus_pre ) ) * (0 - 1 ) )) ” 
  &&  “ ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ (((res + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < ((res + a ) % ( modulus_pre ) )) ” 
  &&  “ (((a + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) )) ” 
  &&  “ ((b ÷ 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (b ÷ 2 )) ”
  &&  emp
).

Definition modular_mul_entail_wit_2_1_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) ((res + a ) % ( modulus_pre ) ) (0 - 1 ) )
.

Definition modular_mul_entail_wit_2_1_split_goal_2 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((((res + a ) % ( modulus_pre ) ) * (0 - 1 ) ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_1_split_goal_3 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (INT_MIN <= (((res + a ) % ( modulus_pre ) ) * (0 - 1 ) ))
.

Definition modular_mul_entail_wit_2_1_split_goal_4 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_1_split_goal_5 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ))
.

Definition modular_mul_entail_wit_2_1_split_goal_6 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_1_split_goal_7 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (INT_MIN <= (((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ))
.

Definition modular_mul_entail_wit_2_1_split_goal_8 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (((res + a ) % ( modulus_pre ) ) < modulus_pre)
.

Definition modular_mul_entail_wit_2_1_split_goal_9 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((0 - modulus_pre ) < ((res + a ) % ( modulus_pre ) ))
.

Definition modular_mul_entail_wit_2_1_split_goal_10 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (((a + a ) % ( modulus_pre ) ) < modulus_pre)
.

Definition modular_mul_entail_wit_2_1_split_goal_11 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) ))
.

Definition modular_mul_entail_wit_2_1_split_goal_12 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((b ÷ 2 ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_1_split_goal_13 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (0 <= (b ÷ 2 ))
.

Definition modular_mul_entail_wit_2_2 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ ((0 - modulus_pre ) < a_pre) ” 
  &&  “ (a_pre < modulus_pre) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (0 < modulus_pre) ” 
  &&  “ ((modulus_pre * 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (b ÷ 2 )) ” 
  &&  “ ((b ÷ 2 ) <= INT_MAX) ” 
  &&  “ (flag = 1) ” 
  &&  “ ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) )) ” 
  &&  “ (((a + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < ((res + a ) % ( modulus_pre ) )) ” 
  &&  “ (((res + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ (INT_MIN <= (((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((res + a ) % ( modulus_pre ) ) * flag )) ” 
  &&  “ ((((res + a ) % ( modulus_pre ) ) * flag ) <= INT_MAX) ” 
  &&  “ (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) ((res + a ) % ( modulus_pre ) ) flag ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) ((res + a ) % ( modulus_pre ) ) 1 ) ” 
  &&  “ ((((res + a ) % ( modulus_pre ) ) * 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((res + a ) % ( modulus_pre ) ) * 1 )) ” 
  &&  “ ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ (((res + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < ((res + a ) % ( modulus_pre ) )) ” 
  &&  “ (((a + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) )) ” 
  &&  “ ((b ÷ 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (b ÷ 2 )) ”
  &&  emp
).

Definition modular_mul_entail_wit_2_2_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) ((res + a ) % ( modulus_pre ) ) 1 )
.

Definition modular_mul_entail_wit_2_2_split_goal_2 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((((res + a ) % ( modulus_pre ) ) * 1 ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_2_split_goal_3 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (INT_MIN <= (((res + a ) % ( modulus_pre ) ) * 1 ))
.

Definition modular_mul_entail_wit_2_2_split_goal_4 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_2_split_goal_5 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ))
.

Definition modular_mul_entail_wit_2_2_split_goal_6 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_2_split_goal_7 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (INT_MIN <= (((res + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ))
.

Definition modular_mul_entail_wit_2_2_split_goal_8 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (((res + a ) % ( modulus_pre ) ) < modulus_pre)
.

Definition modular_mul_entail_wit_2_2_split_goal_9 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((0 - modulus_pre ) < ((res + a ) % ( modulus_pre ) ))
.

Definition modular_mul_entail_wit_2_2_split_goal_10 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (((a + a ) % ( modulus_pre ) ) < modulus_pre)
.

Definition modular_mul_entail_wit_2_2_split_goal_11 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) ))
.

Definition modular_mul_entail_wit_2_2_split_goal_12 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((b ÷ 2 ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_2_split_goal_13 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (0 <= (b ÷ 2 ))
.

Definition modular_mul_entail_wit_2_3 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ ((0 - modulus_pre ) < a_pre) ” 
  &&  “ (a_pre < modulus_pre) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (0 < modulus_pre) ” 
  &&  “ ((modulus_pre * 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (b ÷ 2 )) ” 
  &&  “ ((b ÷ 2 ) <= INT_MAX) ” 
  &&  “ (flag = (0 - 1 )) ” 
  &&  “ ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) )) ” 
  &&  “ (((a + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < res) ” 
  &&  “ (res < modulus_pre) ” 
  &&  “ (INT_MIN <= (res + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((res + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (res * flag )) ” 
  &&  “ ((res * flag ) <= INT_MAX) ” 
  &&  “ (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) res flag ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) res (0 - 1 ) ) ” 
  &&  “ ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((res + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (res + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ (((a + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) )) ” 
  &&  “ ((b ÷ 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (b ÷ 2 )) ”
  &&  emp
).

Definition modular_mul_entail_wit_2_3_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) res (0 - 1 ) )
.

Definition modular_mul_entail_wit_2_3_split_goal_2 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_3_split_goal_3 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ))
.

Definition modular_mul_entail_wit_2_3_split_goal_4 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((res + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_3_split_goal_5 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (INT_MIN <= (res + ((a + a ) % ( modulus_pre ) ) ))
.

Definition modular_mul_entail_wit_2_3_split_goal_6 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (((a + a ) % ( modulus_pre ) ) < modulus_pre)
.

Definition modular_mul_entail_wit_2_3_split_goal_7 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) ))
.

Definition modular_mul_entail_wit_2_3_split_goal_8 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((b ÷ 2 ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_3_split_goal_9 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = (0 - 1 ))) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (0 <= (b ÷ 2 ))
.

Definition modular_mul_entail_wit_2_4 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ ((0 - modulus_pre ) < a_pre) ” 
  &&  “ (a_pre < modulus_pre) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (0 < modulus_pre) ” 
  &&  “ ((modulus_pre * 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (b ÷ 2 )) ” 
  &&  “ ((b ÷ 2 ) <= INT_MAX) ” 
  &&  “ (flag = 1) ” 
  &&  “ ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) )) ” 
  &&  “ (((a + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < res) ” 
  &&  “ (res < modulus_pre) ” 
  &&  “ (INT_MIN <= (res + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((res + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (res * flag )) ” 
  &&  “ ((res * flag ) <= INT_MAX) ” 
  &&  “ (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) res flag ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) res 1 ) ” 
  &&  “ ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ ((res + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (res + ((a + a ) % ( modulus_pre ) ) )) ” 
  &&  “ (((a + a ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) )) ” 
  &&  “ ((b ÷ 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (b ÷ 2 )) ”
  &&  emp
).

Definition modular_mul_entail_wit_2_4_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (ModularMulProgress a_pre b_pre modulus_pre ((a + a ) % ( modulus_pre ) ) (b ÷ 2 ) res 1 )
.

Definition modular_mul_entail_wit_2_4_split_goal_2 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_4_split_goal_3 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (INT_MIN <= (((a + a ) % ( modulus_pre ) ) + ((a + a ) % ( modulus_pre ) ) ))
.

Definition modular_mul_entail_wit_2_4_split_goal_4 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((res + ((a + a ) % ( modulus_pre ) ) ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_4_split_goal_5 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (INT_MIN <= (res + ((a + a ) % ( modulus_pre ) ) ))
.

Definition modular_mul_entail_wit_2_4_split_goal_6 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (((a + a ) % ( modulus_pre ) ) < modulus_pre)
.

Definition modular_mul_entail_wit_2_4_split_goal_7 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((0 - modulus_pre ) < ((a + a ) % ( modulus_pre ) ))
.

Definition modular_mul_entail_wit_2_4_split_goal_8 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  ((b ÷ 2 ) <= INT_MAX)
.

Definition modular_mul_entail_wit_2_4_split_goal_9 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : ((0 - modulus_pre ) < a_pre)) (PreH4 : (a_pre < modulus_pre)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (0 < modulus_pre)) (PreH8 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH9 : (0 <= b)) (PreH10 : (b <= INT_MAX)) (PreH11 : (flag = 1)) (PreH12 : ((0 - modulus_pre ) < a)) (PreH13 : (a < modulus_pre)) (PreH14 : ((0 - modulus_pre ) < res)) (PreH15 : (res < modulus_pre)) (PreH16 : (INT_MIN <= (res + a ))) (PreH17 : ((res + a ) <= INT_MAX)) (PreH18 : (INT_MIN <= (a + a ))) (PreH19 : ((a + a ) <= INT_MAX)) (PreH20 : (INT_MIN <= (res * flag ))) (PreH21 : ((res * flag ) <= INT_MAX)) (PreH22 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (0 <= (b ÷ 2 ))
.

Definition modular_mul_return_wit_1 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b <= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = (0 - 1 ))) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ (ModularMul a_pre b_pre modulus_pre (res * flag ) ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b <= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = (0 - 1 ))) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ (ModularMul a_pre b_pre modulus_pre (res * (0 - 1 ) ) ) ”
  &&  emp
).

Definition modular_mul_return_wit_1_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b <= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = (0 - 1 ))) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (ModularMul a_pre b_pre modulus_pre (res * (0 - 1 ) ) )
.

Definition modular_mul_return_wit_2 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b <= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = 1)) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ (ModularMul a_pre b_pre modulus_pre (res * flag ) ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b <= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = 1)) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  TT && emp 
|--
  “ (ModularMul a_pre b_pre modulus_pre (res * 1 ) ) ”
  &&  emp
).

Definition modular_mul_return_wit_2_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (res: Z) (a: Z) (flag: Z) (b: Z) (PreH1 : (b <= 0)) (PreH2 : ((0 - modulus_pre ) < a_pre)) (PreH3 : (a_pre < modulus_pre)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (0 < modulus_pre)) (PreH7 : ((modulus_pre * 2 ) <= INT_MAX)) (PreH8 : (0 <= b)) (PreH9 : (b <= INT_MAX)) (PreH10 : (flag = 1)) (PreH11 : ((0 - modulus_pre ) < a)) (PreH12 : (a < modulus_pre)) (PreH13 : ((0 - modulus_pre ) < res)) (PreH14 : (res < modulus_pre)) (PreH15 : (INT_MIN <= (res + a ))) (PreH16 : ((res + a ) <= INT_MAX)) (PreH17 : (INT_MIN <= (a + a ))) (PreH18 : ((a + a ) <= INT_MAX)) (PreH19 : (INT_MIN <= (res * flag ))) (PreH20 : ((res * flag ) <= INT_MAX)) (PreH21 : (ModularMulProgress a_pre b_pre modulus_pre a b res flag )) ,
  (ModularMul a_pre b_pre modulus_pre (res * 1 ) )
.

Module Type VC_Correct.


Axiom proof_of_modular_mul_safety_wit_1 : modular_mul_safety_wit_1.
Axiom proof_of_modular_mul_safety_wit_2 : modular_mul_safety_wit_2.
Axiom proof_of_modular_mul_safety_wit_3 : modular_mul_safety_wit_3.
Axiom proof_of_modular_mul_safety_wit_4 : modular_mul_safety_wit_4.
Axiom proof_of_modular_mul_safety_wit_5 : modular_mul_safety_wit_5.
Axiom proof_of_modular_mul_safety_wit_6 : modular_mul_safety_wit_6.
Axiom proof_of_modular_mul_safety_wit_7 : modular_mul_safety_wit_7.
Axiom proof_of_modular_mul_safety_wit_8 : modular_mul_safety_wit_8.
Axiom proof_of_modular_mul_safety_wit_9 : modular_mul_safety_wit_9.
Axiom proof_of_modular_mul_safety_wit_10 : modular_mul_safety_wit_10.
Axiom proof_of_modular_mul_safety_wit_11 : modular_mul_safety_wit_11.
Axiom proof_of_modular_mul_safety_wit_12 : modular_mul_safety_wit_12.
Axiom proof_of_modular_mul_safety_wit_13 : modular_mul_safety_wit_13.
Axiom proof_of_modular_mul_safety_wit_14 : modular_mul_safety_wit_14.
Axiom proof_of_modular_mul_safety_wit_15 : modular_mul_safety_wit_15.
Axiom proof_of_modular_mul_safety_wit_16 : modular_mul_safety_wit_16.
Axiom proof_of_modular_mul_safety_wit_17 : modular_mul_safety_wit_17.
Axiom proof_of_modular_mul_safety_wit_18 : modular_mul_safety_wit_18.
Axiom proof_of_modular_mul_safety_wit_19 : modular_mul_safety_wit_19.
Axiom proof_of_modular_mul_safety_wit_20 : modular_mul_safety_wit_20.
Axiom proof_of_modular_mul_safety_wit_21 : modular_mul_safety_wit_21.
Axiom proof_of_modular_mul_safety_wit_22 : modular_mul_safety_wit_22.
Axiom proof_of_modular_mul_safety_wit_23 : modular_mul_safety_wit_23.
Axiom proof_of_modular_mul_safety_wit_24 : modular_mul_safety_wit_24.
Axiom proof_of_modular_mul_safety_wit_25 : modular_mul_safety_wit_25.
Axiom proof_of_modular_mul_safety_wit_26 : modular_mul_safety_wit_26.
Axiom proof_of_modular_mul_safety_wit_27 : modular_mul_safety_wit_27.
Axiom proof_of_modular_mul_safety_wit_28 : modular_mul_safety_wit_28.
Axiom proof_of_modular_mul_safety_wit_29 : modular_mul_safety_wit_29.
Axiom proof_of_modular_mul_safety_wit_30 : modular_mul_safety_wit_30.
Axiom proof_of_modular_mul_safety_wit_31 : modular_mul_safety_wit_31.
Axiom proof_of_modular_mul_safety_wit_32 : modular_mul_safety_wit_32.
Axiom proof_of_modular_mul_safety_wit_33 : modular_mul_safety_wit_33.
Axiom proof_of_modular_mul_safety_wit_34 : modular_mul_safety_wit_34.
Axiom proof_of_modular_mul_safety_wit_35 : modular_mul_safety_wit_35.
Axiom proof_of_modular_mul_safety_wit_36 : modular_mul_safety_wit_36.
Axiom proof_of_modular_mul_entail_wit_1_1 : modular_mul_entail_wit_1_1.
Axiom proof_of_modular_mul_entail_wit_1_2 : modular_mul_entail_wit_1_2.
Axiom proof_of_modular_mul_entail_wit_2_1 : modular_mul_entail_wit_2_1.
Axiom proof_of_modular_mul_entail_wit_2_2 : modular_mul_entail_wit_2_2.
Axiom proof_of_modular_mul_entail_wit_2_3 : modular_mul_entail_wit_2_3.
Axiom proof_of_modular_mul_entail_wit_2_4 : modular_mul_entail_wit_2_4.
Axiom proof_of_modular_mul_return_wit_1 : modular_mul_return_wit_1.
Axiom proof_of_modular_mul_return_wit_2 : modular_mul_return_wit_2.

End VC_Correct.
