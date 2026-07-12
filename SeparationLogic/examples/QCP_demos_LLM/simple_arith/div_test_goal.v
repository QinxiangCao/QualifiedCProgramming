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
Require Import SimpleC.EE.QCP_demos_LLM.simple_arith.PDiv_lib.
Local Open Scope sac.

(*----- Function div_test -----*)

Definition div_test_safety_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (INT_MIN < c_pre)) (PreH6 : (c_pre <= INT_MAX)) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_test_safety_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_test_safety_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre * b_pre ) <> (-9223372036854775808)) \/ (c_pre <> (-1))) ” 
  &&  “ (c_pre <> 0) ”
.

Definition div_test_safety_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre * b_pre ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (a_pre * b_pre )) ”
.

Definition div_test_safety_wit_5 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int64  |-> ((a_pre * b_pre ) ÷ c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_test_safety_wit_6 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * b_pre ) ÷ c_pre ) < 0)) (PreH2 : (c_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int64  |-> ((a_pre * b_pre ) ÷ c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_test_return_wit_1 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * b_pre ) ÷ c_pre ) >= 0)) (PreH2 : (c_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (((a_pre * b_pre ) ÷ c_pre ) = (Pos_Div ((a_pre * b_pre )) (c_pre) (0))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * b_pre ) ÷ c_pre ) >= 0)) (PreH2 : (c_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (((a_pre * b_pre ) ÷ c_pre ) = (Pos_Div ((a_pre * b_pre )) (c_pre) (0))) ”
  &&  emp
).

Definition div_test_return_wit_1_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * b_pre ) ÷ c_pre ) >= 0)) (PreH2 : (c_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  (((a_pre * b_pre ) ÷ c_pre ) = (Pos_Div ((a_pre * b_pre )) (c_pre) (0)))
.

Definition div_test_return_wit_2 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * b_pre ) ÷ c_pre ) < 0)) (PreH2 : (c_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Pos_Div ((a_pre * b_pre )) (c_pre) (0))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * b_pre ) ÷ c_pre ) < 0)) (PreH2 : (c_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Pos_Div ((a_pre * b_pre )) (c_pre) (0))) ”
  &&  emp
).

Definition div_test_return_wit_2_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * b_pre ) ÷ c_pre ) < 0)) (PreH2 : (c_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  (0 = (Pos_Div ((a_pre * b_pre )) (c_pre) (0)))
.

Definition div_test_return_wit_3 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Pos_Div ((a_pre * b_pre )) (c_pre) (0))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Pos_Div ((a_pre * b_pre )) (c_pre) (0))) ”
  &&  emp
).

Definition div_test_return_wit_3_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  (0 = (Pos_Div ((a_pre * b_pre )) (c_pre) (0)))
.

Module Type VC_Correct.


Axiom proof_of_div_test_safety_wit_1 : div_test_safety_wit_1.
Axiom proof_of_div_test_safety_wit_2 : div_test_safety_wit_2.
Axiom proof_of_div_test_safety_wit_3 : div_test_safety_wit_3.
Axiom proof_of_div_test_safety_wit_4 : div_test_safety_wit_4.
Axiom proof_of_div_test_safety_wit_5 : div_test_safety_wit_5.
Axiom proof_of_div_test_safety_wit_6 : div_test_safety_wit_6.
Axiom proof_of_div_test_return_wit_1 : div_test_return_wit_1.
Axiom proof_of_div_test_return_wit_2 : div_test_return_wit_2.
Axiom proof_of_div_test_return_wit_3 : div_test_return_wit_3.

End VC_Correct.
