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

(*----- Function bounded_power_of_two -----*)

Definition bounded_power_of_two_safety_wit_1 := 
  TT && emp 
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition bounded_power_of_two_return_wit_1 := 
(
  TT && emp 
|--
  EX (t: Z) ,
  “ (0 < t) ” 
  &&  “ (t < 10) ” 
  &&  “ (32 = (Z.shiftl 1 (t + 2 ))) ”
  &&  emp
) \/
(
  TT && emp 
|--
  EX (t: Z) ,
  “ (0 < t) ” 
  &&  “ (t < 10) ” 
  &&  “ (32 = (Z.shiftl 1 (t + 2 ))) ”
  &&  emp
).

(*----- Function given_of_marked_call -----*)

Definition given_of_marked_call_entail_wit_1 := 
forall (retval: Z) (t: Z) (PreH1 : (0 < t)) (PreH2 : (t < 10)) (PreH3 : (retval = (Z.shiftl 1 (t + 2 )))) ,
  ((( &( "x" ) )) # Int  |-> retval)
|--
  “ ((Z.shiftl 1 (t + 2 )) = (Z.shiftl 1 (t + 2 ))) ” 
  &&  “ (0 < t) ” 
  &&  “ (t < 10) ” 
  &&  “ (retval = (Z.shiftl 1 (t + 2 ))) ”
  &&  ((( &( "x" ) )) # Int  |-> (Z.shiftl 1 (t + 2 )))
.

Definition given_of_marked_call_entail_wit_2 := 
(
forall (retval: Z) (t: Z) (PreH1 : ((Z.shiftl 1 (t + 2 )) = (Z.shiftl 1 (t + 2 )))) (PreH2 : (0 < t)) (PreH3 : (t < 10)) (PreH4 : (retval = (Z.shiftl 1 (t + 2 )))) ,
  ((( &( "x" ) )) # Int  |-> (Z.shiftl 1 (t + 2 )))
|--
  EX (u: Z) ,
  “ ((Z.shiftl 1 u) = (Z.shiftl 1 u)) ” 
  &&  “ (u >= 2) ” 
  &&  “ (0 < t) ” 
  &&  “ (t < 10) ” 
  &&  “ (retval = (Z.shiftl 1 (t + 2 ))) ”
  &&  ((( &( "x" ) )) # Int  |-> (Z.shiftl 1 u))
) \/
(
forall (retval: Z) (t: Z) (PreH1 : (0 < t)) (PreH2 : (t < 10)) (PreH3 : (retval = (Z.shiftl 1 (t + 2 )))) ,
  TT && emp 
|--
  EX (u: Z) ,
  “ ((Z.shiftl 1 (t + 2 )) = (Z.shiftl 1 u)) ” 
  &&  “ (u >= 2) ” 
  &&  “ (0 < t) ” 
  &&  “ (t < 10) ” 
  &&  “ (retval = (Z.shiftl 1 (t + 2 ))) ”
  &&  emp
).

Definition given_of_marked_call_return_wit_1 := 
forall (retval: Z) (t: Z) (u_2: Z) (PreH1 : ((Z.shiftl 1 u_2) = (Z.shiftl 1 u_2))) (PreH2 : (u_2 >= 2)) (PreH3 : (0 < t)) (PreH4 : (t < 10)) (PreH5 : (retval = (Z.shiftl 1 (t + 2 )))) ,
  TT && emp 
|--
  EX (u: Z) ,
  “ ((Z.shiftl 1 u_2) = (Z.shiftl 1 u)) ” 
  &&  “ (u >= 2) ”
  &&  emp
.

Definition given_of_marked_call_partial_solve_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

(*----- Function given_from_of_two_marked_calls -----*)

Definition given_from_of_two_marked_calls_safety_wit_1 := 
(
forall (retval: Z) (retval_2: Z) (first_t: Z) (second_t: Z) (PreH1 : ((Z.shiftl 1 (second_t + 2 )) = (Z.shiftl 1 (second_t + 2 )))) (PreH2 : (0 < second_t)) (PreH3 : (second_t < 10)) (PreH4 : (retval_2 = (Z.shiftl 1 (second_t + 2 )))) (PreH5 : (0 < first_t)) (PreH6 : (first_t < 10)) (PreH7 : (retval = (Z.shiftl 1 (first_t + 2 )))) ,
  ((( &( "second" ) )) # Int  |-> (Z.shiftl 1 (second_t + 2 )))
  **  ((( &( "first" ) )) # Int  |-> (Z.shiftl 1 (first_t + 2 )))
|--
  “ (((Z.shiftl 1 (first_t + 2 )) + (Z.shiftl 1 (second_t + 2 )) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Z.shiftl 1 (first_t + 2 )) + (Z.shiftl 1 (second_t + 2 )) )) ”
) \/
(
forall (retval: Z) (retval_2: Z) (first_t: Z) (second_t: Z) (PreH1 : ((Z.shiftl 1 (second_t + 2 )) = (Z.shiftl 1 (second_t + 2 )))) (PreH2 : (0 < second_t)) (PreH3 : (second_t < 10)) (PreH4 : (retval_2 = (Z.shiftl 1 (second_t + 2 )))) (PreH5 : (0 < first_t)) (PreH6 : (first_t < 10)) (PreH7 : (retval = (Z.shiftl 1 (first_t + 2 )))) ,
  ((( &( "second" ) )) # Int  |-> (Z.shiftl 1 (second_t + 2 )))
  **  ((( &( "first" ) )) # Int  |-> (Z.shiftl 1 (first_t + 2 )))
|--
  “ (((Z.shiftl 1 (first_t + 2 )) + (Z.shiftl 1 (second_t + 2 )) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Z.shiftl 1 (first_t + 2 )) + (Z.shiftl 1 (second_t + 2 )) )) ”
).

Definition given_from_of_two_marked_calls_safety_wit_1_split_goal_1 := 
forall (retval: Z) (retval_2: Z) (first_t: Z) (second_t: Z) (PreH1 : ((Z.shiftl 1 (second_t + 2 )) = (Z.shiftl 1 (second_t + 2 )))) (PreH2 : (0 < second_t)) (PreH3 : (second_t < 10)) (PreH4 : (retval_2 = (Z.shiftl 1 (second_t + 2 )))) (PreH5 : (0 < first_t)) (PreH6 : (first_t < 10)) (PreH7 : (retval = (Z.shiftl 1 (first_t + 2 )))) ,
  ((( &( "second" ) )) # Int  |-> (Z.shiftl 1 (second_t + 2 )))
  **  ((( &( "first" ) )) # Int  |-> (Z.shiftl 1 (first_t + 2 )))
|--
  “ (((Z.shiftl 1 (first_t + 2 )) + (Z.shiftl 1 (second_t + 2 )) ) <= INT_MAX) ”
.

Definition given_from_of_two_marked_calls_safety_wit_1_split_goal_2 := 
forall (retval: Z) (retval_2: Z) (first_t: Z) (second_t: Z) (PreH1 : ((Z.shiftl 1 (second_t + 2 )) = (Z.shiftl 1 (second_t + 2 )))) (PreH2 : (0 < second_t)) (PreH3 : (second_t < 10)) (PreH4 : (retval_2 = (Z.shiftl 1 (second_t + 2 )))) (PreH5 : (0 < first_t)) (PreH6 : (first_t < 10)) (PreH7 : (retval = (Z.shiftl 1 (first_t + 2 )))) ,
  ((( &( "second" ) )) # Int  |-> (Z.shiftl 1 (second_t + 2 )))
  **  ((( &( "first" ) )) # Int  |-> (Z.shiftl 1 (first_t + 2 )))
|--
  “ ((INT_MIN) <= ((Z.shiftl 1 (first_t + 2 )) + (Z.shiftl 1 (second_t + 2 )) )) ”
.

Definition given_from_of_two_marked_calls_entail_wit_1 := 
forall (retval: Z) (retval_2: Z) (first_t: Z) (second_t: Z) (PreH1 : (0 < second_t)) (PreH2 : (second_t < 10)) (PreH3 : (retval_2 = (Z.shiftl 1 (second_t + 2 )))) (PreH4 : (0 < first_t)) (PreH5 : (first_t < 10)) (PreH6 : (retval = (Z.shiftl 1 (first_t + 2 )))) ,
  ((( &( "first" ) )) # Int  |-> retval)
|--
  “ ((Z.shiftl 1 (first_t + 2 )) = (Z.shiftl 1 (first_t + 2 ))) ” 
  &&  “ (0 < second_t) ” 
  &&  “ (second_t < 10) ” 
  &&  “ (retval_2 = (Z.shiftl 1 (second_t + 2 ))) ” 
  &&  “ (0 < first_t) ” 
  &&  “ (first_t < 10) ” 
  &&  “ (retval = (Z.shiftl 1 (first_t + 2 ))) ”
  &&  ((( &( "first" ) )) # Int  |-> (Z.shiftl 1 (first_t + 2 )))
.

Definition given_from_of_two_marked_calls_entail_wit_2 := 
forall (retval: Z) (retval_2: Z) (first_t: Z) (second_t: Z) (PreH1 : ((Z.shiftl 1 (first_t + 2 )) = (Z.shiftl 1 (first_t + 2 )))) (PreH2 : (0 < second_t)) (PreH3 : (second_t < 10)) (PreH4 : (retval_2 = (Z.shiftl 1 (second_t + 2 )))) (PreH5 : (0 < first_t)) (PreH6 : (first_t < 10)) (PreH7 : (retval = (Z.shiftl 1 (first_t + 2 )))) ,
  ((( &( "second" ) )) # Int  |-> retval_2)
|--
  “ ((Z.shiftl 1 (second_t + 2 )) = (Z.shiftl 1 (second_t + 2 ))) ” 
  &&  “ (0 < second_t) ” 
  &&  “ (second_t < 10) ” 
  &&  “ (retval_2 = (Z.shiftl 1 (second_t + 2 ))) ” 
  &&  “ (0 < first_t) ” 
  &&  “ (first_t < 10) ” 
  &&  “ (retval = (Z.shiftl 1 (first_t + 2 ))) ”
  &&  ((( &( "second" ) )) # Int  |-> (Z.shiftl 1 (second_t + 2 )))
.

Definition given_from_of_two_marked_calls_return_wit_1 := 
forall (retval: Z) (retval_2: Z) (first_t: Z) (second_t: Z) (PreH1 : ((Z.shiftl 1 (second_t + 2 )) = (Z.shiftl 1 (second_t + 2 )))) (PreH2 : (0 < second_t)) (PreH3 : (second_t < 10)) (PreH4 : (retval_2 = (Z.shiftl 1 (second_t + 2 )))) (PreH5 : (0 < first_t)) (PreH6 : (first_t < 10)) (PreH7 : (retval = (Z.shiftl 1 (first_t + 2 )))) ,
  TT && emp 
|--
  TT && emp 
.

Definition given_from_of_two_marked_calls_partial_solve_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition given_from_of_two_marked_calls_partial_solve_wit_2 := 
forall (t: Z) (retval: Z) (PreH1 : (0 < t)) (PreH2 : (t < 10)) (PreH3 : (retval = (Z.shiftl 1 (t + 2 )))) ,
  TT && emp 
|--
  “ (0 < t) ” 
  &&  “ (t < 10) ” 
  &&  “ (retval = (Z.shiftl 1 (t + 2 ))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_bounded_power_of_two_safety_wit_1 : bounded_power_of_two_safety_wit_1.
Axiom proof_of_bounded_power_of_two_return_wit_1 : bounded_power_of_two_return_wit_1.
Axiom proof_of_given_of_marked_call_entail_wit_1 : given_of_marked_call_entail_wit_1.
Axiom proof_of_given_of_marked_call_entail_wit_2 : given_of_marked_call_entail_wit_2.
Axiom proof_of_given_of_marked_call_return_wit_1 : given_of_marked_call_return_wit_1.
Axiom proof_of_given_of_marked_call_partial_solve_wit_1 : given_of_marked_call_partial_solve_wit_1.
Axiom proof_of_given_from_of_two_marked_calls_safety_wit_1 : given_from_of_two_marked_calls_safety_wit_1.
Axiom proof_of_given_from_of_two_marked_calls_entail_wit_1 : given_from_of_two_marked_calls_entail_wit_1.
Axiom proof_of_given_from_of_two_marked_calls_entail_wit_2 : given_from_of_two_marked_calls_entail_wit_2.
Axiom proof_of_given_from_of_two_marked_calls_return_wit_1 : given_from_of_two_marked_calls_return_wit_1.
Axiom proof_of_given_from_of_two_marked_calls_partial_solve_wit_1 : given_from_of_two_marked_calls_partial_solve_wit_1.
Axiom proof_of_given_from_of_two_marked_calls_partial_solve_wit_2 : given_from_of_two_marked_calls_partial_solve_wit_2.

End VC_Correct.
