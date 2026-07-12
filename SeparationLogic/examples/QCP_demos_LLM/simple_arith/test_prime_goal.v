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
Require Import SimpleC.EE.QCP_demos_LLM.simple_arith.test_prime_lib.
Local Open Scope sac.

(*----- Function test_prime -----*)

Definition test_prime_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= 1000000000)) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition test_prime_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre < 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition test_prime_safety_wit_3 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition test_prime_safety_wit_4 := 
forall (x_pre: Z) (d: Z) (PreH1 : (d < x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (d <> 0) ”
.

Definition test_prime_safety_wit_5 := 
forall (x_pre: Z) (d: Z) (PreH1 : (d < x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition test_prime_safety_wit_6 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) = 0)) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition test_prime_safety_wit_7 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) <> 0)) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition test_prime_safety_wit_8 := 
forall (x_pre: Z) (d: Z) (PreH1 : (d >= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition test_prime_entail_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (x_pre >= 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (2 <= 2) ” 
  &&  “ (2 <= x_pre) ” 
  &&  “ (2 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ ~((HasFactorBetween x_pre 2 2 )) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ~((HasFactorBetween x_pre 2 2 )) ”
  &&  emp
).

Definition test_prime_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ~((HasFactorBetween x_pre 2 2 ))
.

Definition test_prime_entail_wit_2 := 
(
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) <> 0)) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ (2 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= x_pre) ” 
  &&  “ (2 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ ~((HasFactorBetween x_pre 2 (d + 1 ) )) ”
  &&  emp
) \/
(
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) <> 0)) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ ~((HasFactorBetween x_pre 2 (d + 1 ) )) ”
  &&  emp
).

Definition test_prime_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) <> 0)) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  ~((HasFactorBetween x_pre 2 (d + 1 ) ))
.

Definition test_prime_return_wit_1 := 
(
forall (x_pre: Z) (d: Z) (PreH1 : (d >= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (prime x_pre ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (d: Z) (PreH1 : (d >= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ (prime x_pre ) ”
  &&  emp
).

Definition test_prime_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (d: Z) (PreH1 : (d >= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  (prime x_pre )
.

Definition test_prime_return_wit_2 := 
(
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) = 0)) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ ~((prime x_pre )) ”
  &&  emp
) \/
(
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) = 0)) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ ~((prime x_pre )) ”
  &&  emp
).

Definition test_prime_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) = 0)) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  ~((prime x_pre ))
.

Definition test_prime_return_wit_3 := 
(
forall (x_pre: Z) (PreH1 : (x_pre < 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ ~((prime x_pre )) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ~((prime x_pre )) ”
  &&  emp
).

Definition test_prime_return_wit_3_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ~((prime x_pre ))
.

(*----- Function test_prime_sqrt -----*)

Definition test_prime_sqrt_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= 1000000000)) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition test_prime_sqrt_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre < 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition test_prime_sqrt_safety_wit_3 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition test_prime_sqrt_safety_wit_4 := 
forall (x_pre: Z) (d: Z) (PreH1 : (2 <= d)) (PreH2 : (d <= 31624)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 1000000000)) (PreH5 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ ((d * d ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d * d )) ”
.

Definition test_prime_sqrt_safety_wit_5 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((d * d ) <= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (d <> 0) ”
.

Definition test_prime_sqrt_safety_wit_6 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((d * d ) <= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition test_prime_sqrt_safety_wit_7 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) = 0)) (PreH2 : ((d * d ) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition test_prime_sqrt_safety_wit_8 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition test_prime_sqrt_safety_wit_9 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((d * d ) > x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition test_prime_sqrt_entail_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (x_pre >= 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (2 <= 2) ” 
  &&  “ (2 <= 31624) ” 
  &&  “ (2 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ ~((HasFactorBetween x_pre 2 2 )) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ~((HasFactorBetween x_pre 2 2 )) ”
  &&  emp
).

Definition test_prime_sqrt_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ~((HasFactorBetween x_pre 2 2 ))
.

Definition test_prime_sqrt_entail_wit_2 := 
(
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ (2 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= 31624) ” 
  &&  “ (2 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ ~((HasFactorBetween x_pre 2 (d + 1 ) )) ”
  &&  emp
) \/
(
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ ~((HasFactorBetween x_pre 2 (d + 1 ) )) ”
  &&  emp
).

Definition test_prime_sqrt_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) <> 0)) (PreH2 : ((d * d ) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  ~((HasFactorBetween x_pre 2 (d + 1 ) ))
.

Definition test_prime_sqrt_return_wit_1 := 
(
forall (x_pre: Z) (d: Z) (PreH1 : ((d * d ) > x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (prime x_pre ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (d: Z) (PreH1 : ((d * d ) > x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ (prime x_pre ) ”
  &&  emp
).

Definition test_prime_sqrt_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((d * d ) > x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ~((HasFactorBetween x_pre 2 d ))) ,
  (prime x_pre )
.

Definition test_prime_sqrt_return_wit_2 := 
(
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) = 0)) (PreH2 : ((d * d ) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ ~((prime x_pre )) ”
  &&  emp
) \/
(
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) = 0)) (PreH2 : ((d * d ) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  TT && emp 
|--
  “ ~((prime x_pre )) ”
  &&  emp
).

Definition test_prime_sqrt_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (d: Z) (PreH1 : ((x_pre % ( d ) ) = 0)) (PreH2 : ((d * d ) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ~((HasFactorBetween x_pre 2 d ))) ,
  ~((prime x_pre ))
.

Definition test_prime_sqrt_return_wit_3 := 
(
forall (x_pre: Z) (PreH1 : (x_pre < 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ ~((prime x_pre )) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ~((prime x_pre )) ”
  &&  emp
).

Definition test_prime_sqrt_return_wit_3_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 2)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ~((prime x_pre ))
.

Module Type VC_Correct.


Axiom proof_of_test_prime_safety_wit_1 : test_prime_safety_wit_1.
Axiom proof_of_test_prime_safety_wit_2 : test_prime_safety_wit_2.
Axiom proof_of_test_prime_safety_wit_3 : test_prime_safety_wit_3.
Axiom proof_of_test_prime_safety_wit_4 : test_prime_safety_wit_4.
Axiom proof_of_test_prime_safety_wit_5 : test_prime_safety_wit_5.
Axiom proof_of_test_prime_safety_wit_6 : test_prime_safety_wit_6.
Axiom proof_of_test_prime_safety_wit_7 : test_prime_safety_wit_7.
Axiom proof_of_test_prime_safety_wit_8 : test_prime_safety_wit_8.
Axiom proof_of_test_prime_entail_wit_1 : test_prime_entail_wit_1.
Axiom proof_of_test_prime_entail_wit_2 : test_prime_entail_wit_2.
Axiom proof_of_test_prime_return_wit_1 : test_prime_return_wit_1.
Axiom proof_of_test_prime_return_wit_2 : test_prime_return_wit_2.
Axiom proof_of_test_prime_return_wit_3 : test_prime_return_wit_3.
Axiom proof_of_test_prime_sqrt_safety_wit_1 : test_prime_sqrt_safety_wit_1.
Axiom proof_of_test_prime_sqrt_safety_wit_2 : test_prime_sqrt_safety_wit_2.
Axiom proof_of_test_prime_sqrt_safety_wit_3 : test_prime_sqrt_safety_wit_3.
Axiom proof_of_test_prime_sqrt_safety_wit_4 : test_prime_sqrt_safety_wit_4.
Axiom proof_of_test_prime_sqrt_safety_wit_5 : test_prime_sqrt_safety_wit_5.
Axiom proof_of_test_prime_sqrt_safety_wit_6 : test_prime_sqrt_safety_wit_6.
Axiom proof_of_test_prime_sqrt_safety_wit_7 : test_prime_sqrt_safety_wit_7.
Axiom proof_of_test_prime_sqrt_safety_wit_8 : test_prime_sqrt_safety_wit_8.
Axiom proof_of_test_prime_sqrt_safety_wit_9 : test_prime_sqrt_safety_wit_9.
Axiom proof_of_test_prime_sqrt_entail_wit_1 : test_prime_sqrt_entail_wit_1.
Axiom proof_of_test_prime_sqrt_entail_wit_2 : test_prime_sqrt_entail_wit_2.
Axiom proof_of_test_prime_sqrt_return_wit_1 : test_prime_sqrt_return_wit_1.
Axiom proof_of_test_prime_sqrt_return_wit_2 : test_prime_sqrt_return_wit_2.
Axiom proof_of_test_prime_sqrt_return_wit_3 : test_prime_sqrt_return_wit_3.

End VC_Correct.
