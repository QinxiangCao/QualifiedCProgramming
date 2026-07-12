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
  “ (((False \/ (True /\ (x_pre < y_pre))) \/ (True /\ (x_pre = y_pre))) \/ (True /\ (x_pre > y_pre))) ”
.

Definition example_safety_wit_2_Less := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre < 50)) (PreH2 : (x_pre < y_pre)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((False \/ (True /\ (x_pre < 25))) \/ (True /\ (x_pre < 50))) ”
.

Definition example_safety_wit_3_Less25 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_pre < 50)) (PreH3 : (x_pre < y_pre)) (PreH4 : (x_pre < 25)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ False ”
.

Definition example_safety_wit_4_Less50 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_pre < 50)) (PreH3 : (x_pre < y_pre)) (PreH4 : (x_pre < 50)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ False ”
.

Definition example_safety_wit_5_Eq := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <> y_pre)) (PreH2 : (x_pre < 50)) (PreH3 : (x_pre = y_pre)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ False ”
.

Definition example_safety_wit_6_Greater := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_pre < 50)) (PreH3 : (x_pre > y_pre)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ False ”
.

Definition example_return_wit_1_Less25 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <> y_pre)) (PreH2 : (x_pre < 50)) (PreH3 : (x_pre < y_pre)) (PreH4 : (x_pre < 25)) ,
  TT && emp 
|--
  “ (x_pre <> y_pre) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Definition example_return_wit_2_Less50 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <> y_pre)) (PreH2 : (x_pre < 50)) (PreH3 : (x_pre < y_pre)) (PreH4 : (x_pre < 50)) ,
  TT && emp 
|--
  “ (x_pre <> y_pre) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Definition example_return_wit_3_Eq := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (x_pre < 50)) (PreH3 : (x_pre = y_pre)) ,
  TT && emp 
|--
  “ (x_pre = y_pre) ” 
  &&  “ (1 = 1) ”
  &&  emp
.

Definition example_return_wit_4_Greater := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <> y_pre)) (PreH2 : (x_pre < 50)) (PreH3 : (x_pre > y_pre)) ,
  TT && emp 
|--
  “ (x_pre <> y_pre) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_example_safety_wit_1 : example_safety_wit_1.
Axiom proof_of_example_safety_wit_2_Less : example_safety_wit_2_Less.
Axiom proof_of_example_safety_wit_3_Less25 : example_safety_wit_3_Less25.
Axiom proof_of_example_safety_wit_4_Less50 : example_safety_wit_4_Less50.
Axiom proof_of_example_safety_wit_5_Eq : example_safety_wit_5_Eq.
Axiom proof_of_example_safety_wit_6_Greater : example_safety_wit_6_Greater.
Axiom proof_of_example_return_wit_1_Less25 : example_return_wit_1_Less25.
Axiom proof_of_example_return_wit_2_Less50 : example_return_wit_2_Less50.
Axiom proof_of_example_return_wit_3_Eq : example_return_wit_3_Eq.
Axiom proof_of_example_return_wit_4_Greater : example_return_wit_4_Greater.

End VC_Correct.
