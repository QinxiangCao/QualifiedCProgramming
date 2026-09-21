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
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib.
Local Open Scope sac.

(*----- Function modular_power -----*)

Definition modular_power_safety_wit_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (0 <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modular_power_safety_wit_2 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : (2 <= modulus_pre)) (PreH2 : (modulus_pre <= 100000)) (PreH3 : (0 <= a)) (PreH4 : (a < modulus_pre)) (PreH5 : (0 <= b)) (PreH6 : (0 <= result)) (PreH7 : (result < modulus_pre)) (PreH8 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition modular_power_safety_wit_3 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : (b > 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : (0 <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : (0 <= b)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((b <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_power_safety_wit_4 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : (b > 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : (0 <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : (0 <= b)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_power_safety_wit_5 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : (b > 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : (0 <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : (0 <= b)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modular_power_safety_wit_6 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((result * a ) <> (INT64_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_power_safety_wit_7 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result * a ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (result * a )) ”
.

Definition modular_power_safety_wit_8 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> (signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)))
|--
  “ (((a * a ) <> (INT64_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_power_safety_wit_9 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> (signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)))
|--
  “ ((a * a ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (a * a )) ”
.

Definition modular_power_safety_wit_10 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((a * a ) <> (INT64_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_power_safety_wit_11 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((a * a ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (a * a )) ”
.

Definition modular_power_safety_wit_12 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)))
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> (signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)))
|--
  “ ((b <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_power_safety_wit_13 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)))
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> (signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_power_safety_wit_14 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)))
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((b <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_power_safety_wit_15 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "a" ) )) # Int  |-> (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)))
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_power_entail_wit_1 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (0 <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000)) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 100000) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (a_pre < modulus_pre) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < modulus_pre) ” 
  &&  “ (ModularPowerProgress a_pre b_pre modulus_pre a_pre b_pre 1 ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (0 <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000)) ,
  TT && emp 
|--
  “ (ModularPowerProgress a_pre b_pre modulus_pre a_pre b_pre 1 ) ”
  &&  emp
).

Definition modular_power_entail_wit_1_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < modulus_pre)) (PreH3 : (0 <= b_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000)) ,
  (ModularPowerProgress a_pre b_pre modulus_pre a_pre b_pre 1 )
.

Definition modular_power_entail_wit_2_1 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 100000) ” 
  &&  “ (0 <= (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32))) ” 
  &&  “ ((signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) < modulus_pre) ” 
  &&  “ (0 <= (b ÷ 2 )) ” 
  &&  “ (0 <= (signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32))) ” 
  &&  “ ((signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)) < modulus_pre) ” 
  &&  “ (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) (b ÷ 2 ) (signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)) ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  TT && emp 
|--
  “ (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) (b ÷ 2 ) (signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)) ) ” 
  &&  “ ((signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)) < modulus_pre) ” 
  &&  “ (0 <= (signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32))) ” 
  &&  “ (0 <= (b ÷ 2 )) ” 
  &&  “ ((signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) < modulus_pre) ” 
  &&  “ (0 <= (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32))) ”
  &&  emp
).

Definition modular_power_entail_wit_2_1_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) (b ÷ 2 ) (signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)) )
.

Definition modular_power_entail_wit_2_1_split_goal_2 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)) < modulus_pre)
.

Definition modular_power_entail_wit_2_1_split_goal_3 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  (0 <= (signed_last_nbits (((result * a ) % ( modulus_pre ) )) (32)))
.

Definition modular_power_entail_wit_2_1_split_goal_4 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  (0 <= (b ÷ 2 ))
.

Definition modular_power_entail_wit_2_1_split_goal_5 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) < modulus_pre)
.

Definition modular_power_entail_wit_2_1_split_goal_6 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) = 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  (0 <= (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)))
.

Definition modular_power_entail_wit_2_2 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 100000) ” 
  &&  “ (0 <= (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32))) ” 
  &&  “ ((signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) < modulus_pre) ” 
  &&  “ (0 <= (b ÷ 2 )) ” 
  &&  “ (0 <= result) ” 
  &&  “ (result < modulus_pre) ” 
  &&  “ (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) (b ÷ 2 ) result ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  TT && emp 
|--
  “ (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) (b ÷ 2 ) result ) ” 
  &&  “ (0 <= (b ÷ 2 )) ” 
  &&  “ ((signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) < modulus_pre) ” 
  &&  “ (0 <= (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32))) ”
  &&  emp
).

Definition modular_power_entail_wit_2_2_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  (ModularPowerProgress a_pre b_pre modulus_pre (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) (b ÷ 2 ) result )
.

Definition modular_power_entail_wit_2_2_split_goal_2 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  (0 <= (b ÷ 2 ))
.

Definition modular_power_entail_wit_2_2_split_goal_3 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  ((signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)) < modulus_pre)
.

Definition modular_power_entail_wit_2_2_split_goal_4 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : ((b % ( 2 ) ) <> 1)) (PreH2 : (b > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 100000)) (PreH5 : (0 <= a)) (PreH6 : (a < modulus_pre)) (PreH7 : (0 <= b)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  (0 <= (signed_last_nbits (((a * a ) % ( modulus_pre ) )) (32)))
.

Definition modular_power_return_wit_1 := 
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : (b <= 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : (0 <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : (0 <= b)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  TT && emp 
|--
  “ (ModularPower a_pre b_pre modulus_pre result ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : (b <= 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : (0 <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : (0 <= b)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  TT && emp 
|--
  “ (ModularPower a_pre b_pre modulus_pre result ) ”
  &&  emp
).

Definition modular_power_return_wit_1_split_goal_1 := 
forall (modulus_pre: Z) (b_pre: Z) (a_pre: Z) (result: Z) (b: Z) (a: Z) (PreH1 : (b <= 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 100000)) (PreH4 : (0 <= a)) (PreH5 : (a < modulus_pre)) (PreH6 : (0 <= b)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (ModularPowerProgress a_pre b_pre modulus_pre a b result )) ,
  (ModularPower a_pre b_pre modulus_pre result )
.

Module Type VC_Correct.


Axiom proof_of_modular_power_safety_wit_1 : modular_power_safety_wit_1.
Axiom proof_of_modular_power_safety_wit_2 : modular_power_safety_wit_2.
Axiom proof_of_modular_power_safety_wit_3 : modular_power_safety_wit_3.
Axiom proof_of_modular_power_safety_wit_4 : modular_power_safety_wit_4.
Axiom proof_of_modular_power_safety_wit_5 : modular_power_safety_wit_5.
Axiom proof_of_modular_power_safety_wit_6 : modular_power_safety_wit_6.
Axiom proof_of_modular_power_safety_wit_7 : modular_power_safety_wit_7.
Axiom proof_of_modular_power_safety_wit_8 : modular_power_safety_wit_8.
Axiom proof_of_modular_power_safety_wit_9 : modular_power_safety_wit_9.
Axiom proof_of_modular_power_safety_wit_10 : modular_power_safety_wit_10.
Axiom proof_of_modular_power_safety_wit_11 : modular_power_safety_wit_11.
Axiom proof_of_modular_power_safety_wit_12 : modular_power_safety_wit_12.
Axiom proof_of_modular_power_safety_wit_13 : modular_power_safety_wit_13.
Axiom proof_of_modular_power_safety_wit_14 : modular_power_safety_wit_14.
Axiom proof_of_modular_power_safety_wit_15 : modular_power_safety_wit_15.
Axiom proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1.
Axiom proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1.
Axiom proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2.
Axiom proof_of_modular_power_return_wit_1 : modular_power_return_wit_1.

End VC_Correct.
