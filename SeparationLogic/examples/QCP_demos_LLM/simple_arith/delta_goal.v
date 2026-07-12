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

(*----- Function delta -----*)

Definition delta_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre < y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((y_pre - x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y_pre - x_pre )) ”
.

Definition delta_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre >= y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((x_pre - y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre - y_pre )) ”
.

Definition delta_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre >= y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((x_pre - y_pre ) = (Z.abs ((x_pre - y_pre )))) ”
  &&  emp
) \/
(
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre >= y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((x_pre - y_pre ) = (Z.abs ((x_pre - y_pre )))) ”
  &&  emp
).

Definition delta_return_wit_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre >= y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  ((x_pre - y_pre ) = (Z.abs ((x_pre - y_pre ))))
.

Definition delta_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre < y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((y_pre - x_pre ) = (Z.abs ((x_pre - y_pre )))) ”
  &&  emp
) \/
(
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre < y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((y_pre - x_pre ) = (Z.abs ((x_pre - y_pre )))) ”
  &&  emp
).

Definition delta_return_wit_2_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre < y_pre)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 100)) (PreH4 : (0 <= y_pre)) (PreH5 : (y_pre <= 100)) ,
  ((y_pre - x_pre ) = (Z.abs ((x_pre - y_pre ))))
.

Module Type VC_Correct.


Axiom proof_of_delta_safety_wit_1 : delta_safety_wit_1.
Axiom proof_of_delta_safety_wit_2 : delta_safety_wit_2.
Axiom proof_of_delta_return_wit_1 : delta_return_wit_1.
Axiom proof_of_delta_return_wit_2 : delta_return_wit_2.

End VC_Correct.
