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
Local Open Scope sac.

(*----- Function example -----*)

Definition example_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre < 50)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (50 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 50) ”
.

Definition example_safety_wit_2_neq := 
forall (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x <= 50)) (PreH2 : (y = 50)) (PreH3 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition example_safety_wit_3_neq := 
forall (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= 100)) (PreH2 : (x <= 50)) (PreH3 : (y = 50)) (PreH4 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ False ”
.

Definition example_safety_wit_4_neq := 
forall (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= INT_MIN)) (PreH2 : (y <= INT_MAX)) (PreH3 : (y >= INT_MIN)) (PreH4 : (x < 100)) (PreH5 : (x <= 50)) (PreH6 : (y = 50)) (PreH7 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ (50 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 50) ”
.

Definition example_safety_wit_5_neq := 
forall (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x < 50)) (PreH2 : (x >= INT_MIN)) (PreH3 : (y <= INT_MAX)) (PreH4 : (y >= INT_MIN)) (PreH5 : (x < 100)) (PreH6 : (x <= 50)) (PreH7 : (y = 50)) (PreH8 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ ((x + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + 1 )) ”
.

Definition example_safety_wit_6_neq := 
forall (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= 50)) (PreH2 : (x >= INT_MIN)) (PreH3 : (y <= INT_MAX)) (PreH4 : (y >= INT_MIN)) (PreH5 : (x < 100)) (PreH6 : (x <= 50)) (PreH7 : (y = 50)) (PreH8 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ ((x + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + 1 )) ”
.

Definition example_safety_wit_7_neq := 
forall (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= 50)) (PreH2 : (x >= INT_MIN)) (PreH3 : (y <= INT_MAX)) (PreH4 : (y >= INT_MIN)) (PreH5 : (x < 100)) (PreH6 : (x <= 50)) (PreH7 : (y = 50)) (PreH8 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> (x + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ ((y + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y + 1 )) ”
.

Definition example_safety_wit_8_eq := 
forall (x_pre: Z) (y_2: Z) (x: Z) (y: Z) (x_2: Z) (PreH1 : (x_2 >= 50)) (PreH2 : (x_2 < 100)) (PreH3 : (x_2 > 50)) (PreH4 : (x_2 = y)) (PreH5 : (x >= 50)) (PreH6 : (x >= INT_MIN)) (PreH7 : (y_2 <= INT_MAX)) (PreH8 : (y_2 >= INT_MIN)) (PreH9 : (x < 100)) (PreH10 : (x <= 50)) (PreH11 : (y_2 = 50)) (PreH12 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> (x_2 + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ ((y + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y + 1 )) ”
.

Definition example_safety_wit_9_eq := 
forall (x_pre: Z) (y: Z) (x_2: Z) (y_2: Z) (x: Z) (PreH1 : (x >= 50)) (PreH2 : (x < 100)) (PreH3 : (x > 50)) (PreH4 : (x = y_2)) (PreH5 : (x_2 >= 50)) (PreH6 : (x_2 >= INT_MIN)) (PreH7 : (y <= INT_MAX)) (PreH8 : (y >= INT_MIN)) (PreH9 : (x_2 < 100)) (PreH10 : (x_2 <= 50)) (PreH11 : (y = 50)) (PreH12 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y_2)
|--
  “ ((x + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + 1 )) ”
.

Definition example_safety_wit_10_eq := 
forall (x_pre: Z) (y: Z) (x: Z) (y_2: Z) (x_2: Z) (PreH1 : (x_2 > 50)) (PreH2 : (x_2 = y_2)) (PreH3 : (x >= 50)) (PreH4 : (x >= INT_MIN)) (PreH5 : (y <= INT_MAX)) (PreH6 : (y >= INT_MIN)) (PreH7 : (x < 100)) (PreH8 : (x <= 50)) (PreH9 : (y = 50)) (PreH10 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x_2)
  **  ((( &( "y" ) )) # Int  |-> y_2)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition example_safety_wit_11_eq := 
forall (x_pre: Z) (y: Z) (x: Z) (y_2: Z) (x_2: Z) (PreH1 : (x_2 < 100)) (PreH2 : (x_2 > 50)) (PreH3 : (x_2 = y_2)) (PreH4 : (x >= 50)) (PreH5 : (x >= INT_MIN)) (PreH6 : (y <= INT_MAX)) (PreH7 : (y >= INT_MIN)) (PreH8 : (x < 100)) (PreH9 : (x <= 50)) (PreH10 : (y = 50)) (PreH11 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x_2)
  **  ((( &( "y" ) )) # Int  |-> y_2)
|--
  “ (50 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 50) ”
.

Definition example_safety_wit_12_eq := 
forall (x_pre: Z) (y: Z) (x: Z) (y_2: Z) (x_2: Z) (PreH1 : (x_2 < 50)) (PreH2 : (x_2 < 100)) (PreH3 : (x_2 > 50)) (PreH4 : (x_2 = y_2)) (PreH5 : (x >= 50)) (PreH6 : (x >= INT_MIN)) (PreH7 : (y <= INT_MAX)) (PreH8 : (y >= INT_MIN)) (PreH9 : (x < 100)) (PreH10 : (x <= 50)) (PreH11 : (y = 50)) (PreH12 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x_2)
  **  ((( &( "y" ) )) # Int  |-> y_2)
|--
  “ False ”
.

Definition example_safety_wit_13_eq := 
forall (x_pre: Z) (y: Z) (x: Z) (y_2: Z) (x_2: Z) (PreH1 : (x_2 <> y_2)) (PreH2 : (x_2 >= 100)) (PreH3 : (x_2 > 50)) (PreH4 : (x_2 = y_2)) (PreH5 : (x >= 50)) (PreH6 : (x >= INT_MIN)) (PreH7 : (y <= INT_MAX)) (PreH8 : (y >= INT_MIN)) (PreH9 : (x < 100)) (PreH10 : (x <= 50)) (PreH11 : (y = 50)) (PreH12 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x_2)
  **  ((( &( "y" ) )) # Int  |-> y_2)
|--
  “ False ”
.

Definition example_entail_wit_1_neq := 
forall (x_pre: Z) (PreH1 : (x_pre < 50)) ,
  TT && emp 
|--
  “ (x_pre <= 50) ” 
  &&  “ (50 = 50) ” 
  &&  “ (x_pre < 50) ”
  &&  emp
.

Definition example_entail_wit_2_neq := 
forall (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x < 100)) (PreH2 : (x <= 50)) (PreH3 : (y = 50)) (PreH4 : (x_pre < 50)) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ (x >= INT_MIN) ” 
  &&  “ (y <= INT_MAX) ” 
  &&  “ (y >= INT_MIN) ” 
  &&  “ (x < 100) ” 
  &&  “ (x <= 50) ” 
  &&  “ (y = 50) ” 
  &&  “ (x_pre < 50) ”
  &&  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
.

Definition example_entail_wit_3_eq := 
forall (x_pre: Z) (y: Z) (x: Z) (y_2: Z) (x_2: Z) (PreH1 : (x_2 >= 50)) (PreH2 : (x_2 < 100)) (PreH3 : (x_2 > 50)) (PreH4 : (x_2 = y_2)) (PreH5 : (x >= 50)) (PreH6 : (x >= INT_MIN)) (PreH7 : (y <= INT_MAX)) (PreH8 : (y >= INT_MIN)) (PreH9 : (x < 100)) (PreH10 : (x <= 50)) (PreH11 : (y = 50)) (PreH12 : (x_pre < 50)) ,
  TT && emp 
|--
  “ ((x_2 + 1 ) > 50) ” 
  &&  “ ((x_2 + 1 ) = (y_2 + 1 )) ” 
  &&  “ (x >= 50) ” 
  &&  “ (x >= INT_MIN) ” 
  &&  “ (y <= INT_MAX) ” 
  &&  “ (y >= INT_MIN) ” 
  &&  “ (x < 100) ” 
  &&  “ (x <= 50) ” 
  &&  “ (y = 50) ” 
  &&  “ (x_pre < 50) ”
  &&  emp
.

Definition example_entail_wit_4_neq := 
forall (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x < 50)) (PreH2 : (x >= INT_MIN)) (PreH3 : (y <= INT_MAX)) (PreH4 : (y >= INT_MIN)) (PreH5 : (x < 100)) (PreH6 : (x <= 50)) (PreH7 : (y = 50)) (PreH8 : (x_pre < 50)) ,
  TT && emp 
|--
  “ ((x + 1 ) <= 50) ” 
  &&  “ (y = 50) ” 
  &&  “ (x_pre < 50) ”
  &&  emp
.

Definition example_entail_wit_5_eq := 
forall (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= 50)) (PreH2 : (x >= INT_MIN)) (PreH3 : (y <= INT_MAX)) (PreH4 : (y >= INT_MIN)) (PreH5 : (x < 100)) (PreH6 : (x <= 50)) (PreH7 : (y = 50)) (PreH8 : (x_pre < 50)) ,
  TT && emp 
|--
  “ ((x + 1 ) > 50) ” 
  &&  “ ((x + 1 ) = (y + 1 )) ” 
  &&  “ (x >= 50) ” 
  &&  “ (x >= INT_MIN) ” 
  &&  “ (y <= INT_MAX) ” 
  &&  “ (y >= INT_MIN) ” 
  &&  “ (x < 100) ” 
  &&  “ (x <= 50) ” 
  &&  “ (y = 50) ” 
  &&  “ (x_pre < 50) ”
  &&  emp
.

Definition example_return_wit_1_eq := 
forall (x_pre: Z) (y: Z) (x: Z) (y_2: Z) (x_2: Z) (PreH1 : (x_2 = y_2)) (PreH2 : (x_2 >= 100)) (PreH3 : (x_2 > 50)) (PreH4 : (x_2 = y_2)) (PreH5 : (x >= 50)) (PreH6 : (x >= INT_MIN)) (PreH7 : (y <= INT_MAX)) (PreH8 : (y >= INT_MIN)) (PreH9 : (x < 100)) (PreH10 : (x <= 50)) (PreH11 : (y = 50)) (PreH12 : (x_pre < 50)) ,
  TT && emp 
|--
  “ (1 = 1) ”
  &&  emp
.

(*----- Function unmatched -----*)

Definition unmatched_safety_wit_1_skip := 
forall (x_pre: Z) (PreH1 : (x_pre = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unmatched_safety_wit_2_skip := 
forall (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (x_pre = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ False ”
.

Definition unmatched_safety_wit_3_enter := 
forall (x_pre: Z) (x: Z) (PreH1 : (x = 0)) (PreH2 : (x_pre = 0)) ,
  ((( &( "x" ) )) # Int  |-> x)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unmatched_safety_wit_4_enter := 
forall (x_pre: Z) (x: Z) (PreH1 : (x <> 0)) (PreH2 : (x = 0)) (PreH3 : (x_pre = 0)) ,
  ((( &( "x" ) )) # Int  |-> x)
|--
  “ False ”
.

Definition unmatched_safety_wit_5_enter := 
forall (x_pre: Z) (x: Z) (PreH1 : (x = 0)) (PreH2 : (x = 0)) (PreH3 : (x_pre = 0)) ,
  ((( &( "x" ) )) # Int  |-> x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition unmatched_safety_wit_6_skip := 
forall (x_pre: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (x_pre = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition unmatched_entail_wit_1_enter := 
forall (x_pre: Z) (PreH1 : (x_pre = 0)) ,
  TT && emp 
|--
  “ (x_pre = 0) ” 
  &&  “ (x_pre = 0) ”
  &&  emp
.

Definition unmatched_return_wit_1_skip := 
forall (x_pre: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (x_pre = 1)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (x_pre = 1) ”
  &&  emp
.

Definition unmatched_return_wit_2_enter := 
forall (x_pre: Z) (x: Z) (PreH1 : (x = 0)) (PreH2 : (x = 0)) (PreH3 : (x_pre = 0)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (x_pre = 0) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_example_safety_wit_1 : example_safety_wit_1.
Axiom proof_of_example_safety_wit_2_neq : example_safety_wit_2_neq.
Axiom proof_of_example_safety_wit_3_neq : example_safety_wit_3_neq.
Axiom proof_of_example_safety_wit_4_neq : example_safety_wit_4_neq.
Axiom proof_of_example_safety_wit_5_neq : example_safety_wit_5_neq.
Axiom proof_of_example_safety_wit_6_neq : example_safety_wit_6_neq.
Axiom proof_of_example_safety_wit_7_neq : example_safety_wit_7_neq.
Axiom proof_of_example_safety_wit_8_eq : example_safety_wit_8_eq.
Axiom proof_of_example_safety_wit_9_eq : example_safety_wit_9_eq.
Axiom proof_of_example_safety_wit_10_eq : example_safety_wit_10_eq.
Axiom proof_of_example_safety_wit_11_eq : example_safety_wit_11_eq.
Axiom proof_of_example_safety_wit_12_eq : example_safety_wit_12_eq.
Axiom proof_of_example_safety_wit_13_eq : example_safety_wit_13_eq.
Axiom proof_of_example_entail_wit_1_neq : example_entail_wit_1_neq.
Axiom proof_of_example_entail_wit_2_neq : example_entail_wit_2_neq.
Axiom proof_of_example_entail_wit_3_eq : example_entail_wit_3_eq.
Axiom proof_of_example_entail_wit_4_neq : example_entail_wit_4_neq.
Axiom proof_of_example_entail_wit_5_eq : example_entail_wit_5_eq.
Axiom proof_of_example_return_wit_1_eq : example_return_wit_1_eq.
Axiom proof_of_unmatched_safety_wit_1_skip : unmatched_safety_wit_1_skip.
Axiom proof_of_unmatched_safety_wit_2_skip : unmatched_safety_wit_2_skip.
Axiom proof_of_unmatched_safety_wit_3_enter : unmatched_safety_wit_3_enter.
Axiom proof_of_unmatched_safety_wit_4_enter : unmatched_safety_wit_4_enter.
Axiom proof_of_unmatched_safety_wit_5_enter : unmatched_safety_wit_5_enter.
Axiom proof_of_unmatched_safety_wit_6_skip : unmatched_safety_wit_6_skip.
Axiom proof_of_unmatched_entail_wit_1_enter : unmatched_entail_wit_1_enter.
Axiom proof_of_unmatched_return_wit_1_skip : unmatched_return_wit_1_skip.
Axiom proof_of_unmatched_return_wit_2_enter : unmatched_return_wit_2_enter.

End VC_Correct.
