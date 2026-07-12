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
Require Import SimpleC.EE.QCP_demos_tutorial.branch_join_private_condition_lib.
Local Open Scope sac.

(*----- Function f -----*)

Definition f_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (x_pre > 0)) (PreH2 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((x_pre <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition f_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre > 0)) (PreH2 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition f_safety_wit_3 := 
forall (x_pre: Z) (PreH1 : (x_pre > 0)) (PreH2 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition f_safety_wit_4 := 
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) = 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((x_pre <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition f_safety_wit_5 := 
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) = 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition f_safety_wit_6 := 
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) <> 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (((3 * x_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((3 * x_pre ) + 1 )) ”
.

Definition f_safety_wit_7 := 
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) <> 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((3 * x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (3 * x_pre )) ”
.

Definition f_safety_wit_8 := 
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) <> 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition f_safety_wit_9 := 
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) <> 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition f_safety_wit_10 := 
forall (x_pre: Z) (PreH1 : ((step (x_pre)) = (step (x_pre)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> (step (x_pre)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition f_entail_wit_1_1 := 
(
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) = 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> (x_pre ÷ 2 ))
|--
  “ ((step (x_pre)) = (step (x_pre))) ” 
  &&  “ (x_pre > 0) ” 
  &&  “ (x_pre <= 715827882) ”
  &&  ((( &( "x" ) )) # Int  |-> (step (x_pre)))
) \/
(
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) = 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  TT && emp 
|--
  “ ((x_pre ÷ 2 ) = (step (x_pre))) ”
  &&  emp
).

Definition f_entail_wit_1_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) = 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  ((x_pre ÷ 2 ) = (step (x_pre)))
.

Definition f_entail_wit_1_2 := 
(
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) <> 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  ((( &( "x" ) )) # Int  |-> ((3 * x_pre ) + 1 ))
|--
  “ ((step (x_pre)) = (step (x_pre))) ” 
  &&  “ (x_pre > 0) ” 
  &&  “ (x_pre <= 715827882) ”
  &&  ((( &( "x" ) )) # Int  |-> (step (x_pre)))
) \/
(
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) <> 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  TT && emp 
|--
  “ (((3 * x_pre ) + 1 ) = (step (x_pre))) ”
  &&  emp
).

Definition f_entail_wit_1_2_split_goal_1 := 
forall (x_pre: Z) (PreH1 : ((x_pre % ( 2 ) ) <> 0)) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  (((3 * x_pre ) + 1 ) = (step (x_pre)))
.

Definition f_return_wit_1 := 
forall (x_pre: Z) (PreH1 : ((step (x_pre)) = (step (x_pre)))) (PreH2 : (x_pre > 0)) (PreH3 : (x_pre <= 715827882)) ,
  TT && emp 
|--
  “ (0 = 0) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_f_safety_wit_1 : f_safety_wit_1.
Axiom proof_of_f_safety_wit_2 : f_safety_wit_2.
Axiom proof_of_f_safety_wit_3 : f_safety_wit_3.
Axiom proof_of_f_safety_wit_4 : f_safety_wit_4.
Axiom proof_of_f_safety_wit_5 : f_safety_wit_5.
Axiom proof_of_f_safety_wit_6 : f_safety_wit_6.
Axiom proof_of_f_safety_wit_7 : f_safety_wit_7.
Axiom proof_of_f_safety_wit_8 : f_safety_wit_8.
Axiom proof_of_f_safety_wit_9 : f_safety_wit_9.
Axiom proof_of_f_safety_wit_10 : f_safety_wit_10.
Axiom proof_of_f_entail_wit_1_1 : f_entail_wit_1_1.
Axiom proof_of_f_entail_wit_1_2 : f_entail_wit_1_2.
Axiom proof_of_f_return_wit_1 : f_return_wit_1.

End VC_Correct.
