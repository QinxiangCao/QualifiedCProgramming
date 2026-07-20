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

(*----- Function add -----*)

Definition add_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= 100)) (PreH3 : (0 <= y_pre)) (PreH4 : (y_pre <= 100)) ,
  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ ((x_pre + y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre + y_pre )) ”
.

Definition add_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= 100)) (PreH3 : (0 <= y_pre)) (PreH4 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ ((x_pre + y_pre ) = (x_pre + y_pre )) ”
  &&  emp
.

(*----- Function slow_add -----*)

Definition slow_add_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) (PreH1 : (0 <= x)) (PreH2 : (x <= 100)) (PreH3 : (0 <= y)) (PreH4 : (y <= 200)) (PreH5 : ((x + y ) = (x_pre + y_pre ))) (PreH6 : (0 <= x_pre)) (PreH7 : (x_pre <= 100)) (PreH8 : (0 <= y_pre)) (PreH9 : (y_pre <= 100)) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition slow_add_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 <= x)) (PreH3 : (x <= 100)) (PreH4 : (0 <= y)) (PreH5 : (y <= 200)) (PreH6 : ((x + y ) = (x_pre + y_pre ))) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 100)) (PreH9 : (0 <= y_pre)) (PreH10 : (y_pre <= 100)) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ ((x - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x - 1 )) ”
.

Definition slow_add_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 <= x)) (PreH3 : (x <= 100)) (PreH4 : (0 <= y)) (PreH5 : (y <= 200)) (PreH6 : ((x + y ) = (x_pre + y_pre ))) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 100)) (PreH9 : (0 <= y_pre)) (PreH10 : (y_pre <= 100)) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition slow_add_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 <= x)) (PreH3 : (x <= 100)) (PreH4 : (0 <= y)) (PreH5 : (y <= 200)) (PreH6 : ((x + y ) = (x_pre + y_pre ))) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 100)) (PreH9 : (0 <= y_pre)) (PreH10 : (y_pre <= 100)) ,
  ((( &( "x" ) )) # Int  |-> (x - 1 ))
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ ((y + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y + 1 )) ”
.

Definition slow_add_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 <= x)) (PreH3 : (x <= 100)) (PreH4 : (0 <= y)) (PreH5 : (y <= 200)) (PreH6 : ((x + y ) = (x_pre + y_pre ))) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 100)) (PreH9 : (0 <= y_pre)) (PreH10 : (y_pre <= 100)) ,
  ((( &( "x" ) )) # Int  |-> (x - 1 ))
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition slow_add_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= 100)) (PreH3 : (0 <= y_pre)) (PreH4 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 100) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre <= 200) ” 
  &&  “ ((x_pre + y_pre ) = (x_pre + y_pre )) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 100) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre <= 100) ”
  &&  emp
.

Definition slow_add_entail_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 <= x)) (PreH3 : (x <= 100)) (PreH4 : (0 <= y)) (PreH5 : (y <= 200)) (PreH6 : ((x + y ) = (x_pre + y_pre ))) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 100)) (PreH9 : (0 <= y_pre)) (PreH10 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ (0 <= (x - 1 )) ” 
  &&  “ ((x - 1 ) <= 100) ” 
  &&  “ (0 <= (y + 1 )) ” 
  &&  “ ((y + 1 ) <= 200) ” 
  &&  “ (((x - 1 ) + (y + 1 ) ) = (x_pre + y_pre )) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= 100) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre <= 100) ”
  &&  emp
.

Definition slow_add_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 <= x)) (PreH3 : (x <= 100)) (PreH4 : (0 <= y)) (PreH5 : (y <= 200)) (PreH6 : ((x + y ) = (x_pre + y_pre ))) (PreH7 : (0 <= x_pre)) (PreH8 : (x_pre <= 100)) (PreH9 : (0 <= y_pre)) (PreH10 : (y_pre <= 100)) ,
  TT && emp 
|--
  “ (y = (x_pre + y_pre )) ”
  &&  emp
.

(*----- Function add1_1 -----*)

Definition add1_1_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre < INT_MAX)) ,
  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((x_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre + 1 )) ”
.

Definition add1_1_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre < INT_MAX)) ,
  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add1_1_return_wit_1 := 
forall (x_pre: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((x_pre + 1 ) = (x_pre + 1 )) ”
  &&  emp
.

(*----- Function add1_2 -----*)

Definition add1_2_safety_wit_1 := 
forall (x_pre: Z) (v: Z) (PreH1 : (INT_MIN <= v)) (PreH2 : (v < INT_MAX)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((x_pre) # Int  |-> v)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition add1_2_return_wit_1 := 
forall (x_pre: Z) (v: Z) (PreH1 : (INT_MIN <= v)) (PreH2 : (v < INT_MAX)) ,
  ((x_pre) # Int  |-> (v + 1 ))
|--
  EX (x_pre_v: Z) ,
  “ (x_pre_v = (v + 1 )) ”
  &&  ((x_pre) # Int  |-> x_pre_v)
.

(*----- Function add1_3 -----*)

Definition add1_3_safety_wit_1 := 
forall (x_pre: Z) (v: Z) (x_pre_v: Z) (PreH1 : (INT_MIN <= v)) (PreH2 : (v < INT_MAX)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((x_pre) # Ptr  |-> x_pre_v)
  **  ((x_pre_v) # Int  |-> v)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition add1_3_safety_wit_2 := 
forall (x_pre: Z) (v: Z) (x_pre_v: Z) (PreH1 : (INT_MIN <= v)) (PreH2 : (v < INT_MAX)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((x_pre) # Ptr  |-> x_pre_v)
  **  ((x_pre_v) # Int  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add1_3_return_wit_1 := 
forall (x_pre: Z) (v: Z) (x_pre_v_2: Z) (PreH1 : (INT_MIN <= v)) (PreH2 : (v < INT_MAX)) ,
  ((x_pre) # Ptr  |-> x_pre_v_2)
  **  ((x_pre_v_2) # Int  |-> (v + 1 ))
|--
  EX (x_pre_v_v: Z)  (x_pre_v: Z) ,
  “ (x_pre_v_v = (v + 1 )) ”
  &&  ((x_pre) # Ptr  |-> x_pre_v)
  **  ((x_pre_v) # Int  |-> x_pre_v_v)
.

Module Type VC_Correct.


Axiom proof_of_add_safety_wit_1 : add_safety_wit_1.
Axiom proof_of_add_return_wit_1 : add_return_wit_1.
Axiom proof_of_slow_add_safety_wit_1 : slow_add_safety_wit_1.
Axiom proof_of_slow_add_safety_wit_2 : slow_add_safety_wit_2.
Axiom proof_of_slow_add_safety_wit_3 : slow_add_safety_wit_3.
Axiom proof_of_slow_add_safety_wit_4 : slow_add_safety_wit_4.
Axiom proof_of_slow_add_safety_wit_5 : slow_add_safety_wit_5.
Axiom proof_of_slow_add_entail_wit_1 : slow_add_entail_wit_1.
Axiom proof_of_slow_add_entail_wit_2 : slow_add_entail_wit_2.
Axiom proof_of_slow_add_return_wit_1 : slow_add_return_wit_1.
Axiom proof_of_add1_1_safety_wit_1 : add1_1_safety_wit_1.
Axiom proof_of_add1_1_safety_wit_2 : add1_1_safety_wit_2.
Axiom proof_of_add1_1_return_wit_1 : add1_1_return_wit_1.
Axiom proof_of_add1_2_safety_wit_1 : add1_2_safety_wit_1.
Axiom proof_of_add1_2_return_wit_1 : add1_2_return_wit_1.
Axiom proof_of_add1_3_safety_wit_1 : add1_3_safety_wit_1.
Axiom proof_of_add1_3_safety_wit_2 : add1_3_safety_wit_2.
Axiom proof_of_add1_3_return_wit_1 : add1_3_return_wit_1.

End VC_Correct.
