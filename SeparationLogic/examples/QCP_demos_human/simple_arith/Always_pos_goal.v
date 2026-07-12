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
Require Import SimpleC.EE.QCP_demos_human.simple_arith.Apos_lib.
Local Open Scope sac.

(*----- Function Always_positive_simple -----*)

Definition Always_positive_simple_safety_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (INT_MIN < c_pre)) (PreH6 : (c_pre <= INT_MAX)) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_simple_safety_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_simple_safety_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((b_pre * b_pre ) <> (-9223372036854775808)) \/ (4 <> (-1))) ” 
  &&  “ (4 <> 0) ”
.

Definition Always_positive_simple_safety_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre * b_pre ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (b_pre * b_pre )) ”
.

Definition Always_positive_simple_safety_wit_5 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition Always_positive_simple_safety_wit_6 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre * c_pre ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (a_pre * c_pre )) ”
.

Definition Always_positive_simple_safety_wit_7 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) ÷ 4 ) >= (a_pre * c_pre ))) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_simple_safety_wit_8 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre ))) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_simple_safety_wit_9 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre ))) (PreH3 : (a_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition Always_positive_simple_safety_wit_10 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre ))) (PreH3 : (a_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_simple_return_wit_1 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre ))) (PreH3 : (a_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre ))) (PreH3 : (a_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
).

Definition Always_positive_simple_return_wit_1_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre ))) (PreH3 : (a_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  (0 = (Always_pos (a_pre) (b_pre) (c_pre)))
.

Definition Always_positive_simple_return_wit_2 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre ))) (PreH3 : (a_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre ))) (PreH3 : (a_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
).

Definition Always_positive_simple_return_wit_2_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre ))) (PreH3 : (a_pre <> 0)) (PreH4 : (INT_MIN < a_pre)) (PreH5 : (a_pre <= INT_MAX)) (PreH6 : (INT_MIN < b_pre)) (PreH7 : (b_pre <= INT_MAX)) (PreH8 : (INT_MIN < c_pre)) (PreH9 : (c_pre <= INT_MAX)) ,
  (1 = (Always_pos (a_pre) (b_pre) (c_pre)))
.

Definition Always_positive_simple_return_wit_3 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) ÷ 4 ) >= (a_pre * c_pre ))) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) ÷ 4 ) >= (a_pre * c_pre ))) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
).

Definition Always_positive_simple_return_wit_3_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) ÷ 4 ) >= (a_pre * c_pre ))) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  (0 = (Always_pos (a_pre) (b_pre) (c_pre)))
.

Definition Always_positive_simple_return_wit_4 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
).

Definition Always_positive_simple_return_wit_4_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  (0 = (Always_pos (a_pre) (b_pre) (c_pre)))
.

(*----- Function Always_positive -----*)

Definition Always_positive_safety_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) (PreH5 : (INT_MIN < c_pre)) (PreH6 : (c_pre <= INT_MAX)) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |->_)
  **  ((( &( "delta0" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre * b_pre ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (b_pre * b_pre )) ”
.

Definition Always_positive_safety_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre * c_pre ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (a_pre * c_pre )) ”
.

Definition Always_positive_safety_wit_5 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_6 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre * c_pre ) <= 0)) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_7 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre * c_pre ) > 0)) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition Always_positive_safety_wit_8 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (delta2 <= delta1)) (PreH2 : (0 < d)) (PreH3 : (d <= 4)) (PreH4 : (delta0 = (b_pre * b_pre ))) (PreH5 : (delta2 = (a_pre * c_pre ))) (PreH6 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH7 : ((a_pre * c_pre ) > 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (INT_MIN < a_pre)) (PreH10 : (a_pre <= INT_MAX)) (PreH11 : (INT_MIN < b_pre)) (PreH12 : (b_pre <= INT_MAX)) (PreH13 : (INT_MIN < c_pre)) (PreH14 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((delta1 - delta2 ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (delta1 - delta2 )) ”
.

Definition Always_positive_safety_wit_9 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (delta2 <= delta1)) (PreH2 : (0 < d)) (PreH3 : (d <= 4)) (PreH4 : (delta0 = (b_pre * b_pre ))) (PreH5 : (delta2 = (a_pre * c_pre ))) (PreH6 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH7 : ((a_pre * c_pre ) > 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (INT_MIN < a_pre)) (PreH10 : (a_pre <= INT_MAX)) (PreH11 : (INT_MIN < b_pre)) (PreH12 : (b_pre <= INT_MAX)) (PreH13 : (INT_MIN < c_pre)) (PreH14 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((d - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d - 1 )) ”
.

Definition Always_positive_safety_wit_10 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (delta2 <= delta1)) (PreH2 : (0 < d)) (PreH3 : (d <= 4)) (PreH4 : (delta0 = (b_pre * b_pre ))) (PreH5 : (delta2 = (a_pre * c_pre ))) (PreH6 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH7 : ((a_pre * c_pre ) > 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (INT_MIN < a_pre)) (PreH10 : (a_pre <= INT_MAX)) (PreH11 : (INT_MIN < b_pre)) (PreH12 : (b_pre <= INT_MAX)) (PreH13 : (INT_MIN < c_pre)) (PreH14 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition Always_positive_safety_wit_11 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (delta2 <= delta1)) (PreH2 : (0 < d)) (PreH3 : (d <= 4)) (PreH4 : (delta0 = (b_pre * b_pre ))) (PreH5 : (delta2 = (a_pre * c_pre ))) (PreH6 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH7 : ((a_pre * c_pre ) > 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (INT_MIN < a_pre)) (PreH10 : (a_pre <= INT_MAX)) (PreH11 : (INT_MIN < b_pre)) (PreH12 : (b_pre <= INT_MAX)) (PreH13 : (INT_MIN < c_pre)) (PreH14 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (d - 1 ))
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_12 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((d - 1 ) = 0)) (PreH2 : (delta2 <= delta1)) (PreH3 : (0 < d)) (PreH4 : (d <= 4)) (PreH5 : (delta0 = (b_pre * b_pre ))) (PreH6 : (delta2 = (a_pre * c_pre ))) (PreH7 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH8 : ((a_pre * c_pre ) > 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (INT_MIN < a_pre)) (PreH11 : (a_pre <= INT_MAX)) (PreH12 : (INT_MIN < b_pre)) (PreH13 : (b_pre <= INT_MAX)) (PreH14 : (INT_MIN < c_pre)) (PreH15 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (d - 1 ))
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_13 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((delta1 - delta2 ) < 0)) (PreH2 : ((d - 1 ) = 0)) (PreH3 : (delta2 <= delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (d - 1 ))
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ False ”
.

Definition Always_positive_safety_wit_14 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((delta1 - delta2 ) >= 0)) (PreH2 : ((d - 1 ) = 0)) (PreH3 : (delta2 <= delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (d - 1 ))
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_15 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre * c_pre ) <= 0)) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_16 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (delta2 > delta1)) (PreH2 : (0 < d)) (PreH3 : (d <= 4)) (PreH4 : (delta0 = (b_pre * b_pre ))) (PreH5 : (delta2 = (a_pre * c_pre ))) (PreH6 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH7 : ((a_pre * c_pre ) > 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (INT_MIN < a_pre)) (PreH10 : (a_pre <= INT_MAX)) (PreH11 : (INT_MIN < b_pre)) (PreH12 : (b_pre <= INT_MAX)) (PreH13 : (INT_MIN < c_pre)) (PreH14 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_17 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((delta1 - delta2 ) >= 0)) (PreH2 : ((d - 1 ) = 0)) (PreH3 : (delta2 <= delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_18 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (d = 0)) (PreH2 : (delta2 > delta1)) (PreH3 : (0 < d)) (PreH4 : (d <= 4)) (PreH5 : (delta0 = (b_pre * b_pre ))) (PreH6 : (delta2 = (a_pre * c_pre ))) (PreH7 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH8 : ((a_pre * c_pre ) > 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (INT_MIN < a_pre)) (PreH11 : (a_pre <= INT_MAX)) (PreH12 : (INT_MIN < b_pre)) (PreH13 : (b_pre <= INT_MAX)) (PreH14 : (INT_MIN < c_pre)) (PreH15 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ False ”
.

Definition Always_positive_safety_wit_19 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre * c_pre ) <= 0)) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_20 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((delta1 - delta2 ) >= 0)) (PreH2 : ((d - 1 ) = 0)) (PreH3 : (delta2 <= delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_21 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (d <> 0)) (PreH2 : (delta2 > delta1)) (PreH3 : (0 < d)) (PreH4 : (d <= 4)) (PreH5 : (delta0 = (b_pre * b_pre ))) (PreH6 : (delta2 = (a_pre * c_pre ))) (PreH7 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH8 : ((a_pre * c_pre ) > 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (INT_MIN < a_pre)) (PreH11 : (a_pre <= INT_MAX)) (PreH12 : (INT_MIN < b_pre)) (PreH13 : (b_pre <= INT_MAX)) (PreH14 : (INT_MIN < c_pre)) (PreH15 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_safety_wit_22 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (a_pre > 0)) (PreH2 : (d <> 0)) (PreH3 : (delta2 > delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition Always_positive_safety_wit_23 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (d <> 0)) (PreH3 : (delta2 > delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Always_positive_entail_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre * c_pre ) > 0)) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 < 4) ” 
  &&  “ (4 <= 4) ” 
  &&  “ ((b_pre * b_pre ) = (b_pre * b_pre )) ” 
  &&  “ ((a_pre * c_pre ) = (a_pre * c_pre )) ” 
  &&  “ ((b_pre * b_pre ) = ((b_pre * b_pre ) + ((4 - 4 ) * (a_pre * c_pre ) ) )) ” 
  &&  “ ((a_pre * c_pre ) > 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < c_pre) ” 
  &&  “ (c_pre <= INT_MAX) ”
  &&  emp
.

Definition Always_positive_entail_wit_2 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((d - 1 ) <> 0)) (PreH2 : (delta2 <= delta1)) (PreH3 : (0 < d)) (PreH4 : (d <= 4)) (PreH5 : (delta0 = (b_pre * b_pre ))) (PreH6 : (delta2 = (a_pre * c_pre ))) (PreH7 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH8 : ((a_pre * c_pre ) > 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (INT_MIN < a_pre)) (PreH11 : (a_pre <= INT_MAX)) (PreH12 : (INT_MIN < b_pre)) (PreH13 : (b_pre <= INT_MAX)) (PreH14 : (INT_MIN < c_pre)) (PreH15 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 < (d - 1 )) ” 
  &&  “ ((d - 1 ) <= 4) ” 
  &&  “ (delta0 = (b_pre * b_pre )) ” 
  &&  “ (delta2 = (a_pre * c_pre )) ” 
  &&  “ (delta0 = ((delta1 - delta2 ) + ((4 - (d - 1 ) ) * delta2 ) )) ” 
  &&  “ ((a_pre * c_pre ) > 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < c_pre) ” 
  &&  “ (c_pre <= INT_MAX) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((d - 1 ) <> 0)) (PreH2 : (delta2 <= delta1)) (PreH3 : (0 < d)) (PreH4 : (d <= 4)) (PreH5 : (delta0 = (b_pre * b_pre ))) (PreH6 : (delta2 = (a_pre * c_pre ))) (PreH7 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH8 : ((a_pre * c_pre ) > 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (INT_MIN < a_pre)) (PreH11 : (a_pre <= INT_MAX)) (PreH12 : (INT_MIN < b_pre)) (PreH13 : (b_pre <= INT_MAX)) (PreH14 : (INT_MIN < c_pre)) (PreH15 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (delta0 = ((delta1 - delta2 ) + ((4 - (d - 1 ) ) * delta2 ) )) ”
  &&  emp
).

Definition Always_positive_entail_wit_2_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((d - 1 ) <> 0)) (PreH2 : (delta2 <= delta1)) (PreH3 : (0 < d)) (PreH4 : (d <= 4)) (PreH5 : (delta0 = (b_pre * b_pre ))) (PreH6 : (delta2 = (a_pre * c_pre ))) (PreH7 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH8 : ((a_pre * c_pre ) > 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (INT_MIN < a_pre)) (PreH11 : (a_pre <= INT_MAX)) (PreH12 : (INT_MIN < b_pre)) (PreH13 : (b_pre <= INT_MAX)) (PreH14 : (INT_MIN < c_pre)) (PreH15 : (c_pre <= INT_MAX)) ,
  (delta0 = ((delta1 - delta2 ) + ((4 - (d - 1 ) ) * delta2 ) ))
.

Definition Always_positive_return_wit_1 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (d <> 0)) (PreH3 : (delta2 > delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (d <> 0)) (PreH3 : (delta2 > delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
).

Definition Always_positive_return_wit_1_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (d <> 0)) (PreH3 : (delta2 > delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  (0 = (Always_pos (a_pre) (b_pre) (c_pre)))
.

Definition Always_positive_return_wit_2 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (a_pre > 0)) (PreH2 : (d <> 0)) (PreH3 : (delta2 > delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (a_pre > 0)) (PreH2 : (d <> 0)) (PreH3 : (delta2 > delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
).

Definition Always_positive_return_wit_2_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : (a_pre > 0)) (PreH2 : (d <> 0)) (PreH3 : (delta2 > delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  (1 = (Always_pos (a_pre) (b_pre) (c_pre)))
.

Definition Always_positive_return_wit_3 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre * c_pre ) <= 0)) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre * c_pre ) <= 0)) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
).

Definition Always_positive_return_wit_3_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre * c_pre ) <= 0)) (PreH2 : (a_pre <> 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (INT_MIN < c_pre)) (PreH8 : (c_pre <= INT_MAX)) ,
  (0 = (Always_pos (a_pre) (b_pre) (c_pre)))
.

Definition Always_positive_return_wit_4 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((delta1 - delta2 ) >= 0)) (PreH2 : ((d - 1 ) = 0)) (PreH3 : (delta2 <= delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((delta1 - delta2 ) >= 0)) (PreH2 : ((d - 1 ) = 0)) (PreH3 : (delta2 <= delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
).

Definition Always_positive_return_wit_4_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) (PreH1 : ((delta1 - delta2 ) >= 0)) (PreH2 : ((d - 1 ) = 0)) (PreH3 : (delta2 <= delta1)) (PreH4 : (0 < d)) (PreH5 : (d <= 4)) (PreH6 : (delta0 = (b_pre * b_pre ))) (PreH7 : (delta2 = (a_pre * c_pre ))) (PreH8 : (delta0 = (delta1 + ((4 - d ) * delta2 ) ))) (PreH9 : ((a_pre * c_pre ) > 0)) (PreH10 : (a_pre <> 0)) (PreH11 : (INT_MIN < a_pre)) (PreH12 : (a_pre <= INT_MAX)) (PreH13 : (INT_MIN < b_pre)) (PreH14 : (b_pre <= INT_MAX)) (PreH15 : (INT_MIN < c_pre)) (PreH16 : (c_pre <= INT_MAX)) ,
  (0 = (Always_pos (a_pre) (b_pre) (c_pre)))
.

Definition Always_positive_return_wit_5 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (Always_pos (a_pre) (b_pre) (c_pre))) ”
  &&  emp
).

Definition Always_positive_return_wit_5_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  (0 = (Always_pos (a_pre) (b_pre) (c_pre)))
.

Module Type VC_Correct.


Axiom proof_of_Always_positive_simple_safety_wit_1 : Always_positive_simple_safety_wit_1.
Axiom proof_of_Always_positive_simple_safety_wit_2 : Always_positive_simple_safety_wit_2.
Axiom proof_of_Always_positive_simple_safety_wit_3 : Always_positive_simple_safety_wit_3.
Axiom proof_of_Always_positive_simple_safety_wit_4 : Always_positive_simple_safety_wit_4.
Axiom proof_of_Always_positive_simple_safety_wit_5 : Always_positive_simple_safety_wit_5.
Axiom proof_of_Always_positive_simple_safety_wit_6 : Always_positive_simple_safety_wit_6.
Axiom proof_of_Always_positive_simple_safety_wit_7 : Always_positive_simple_safety_wit_7.
Axiom proof_of_Always_positive_simple_safety_wit_8 : Always_positive_simple_safety_wit_8.
Axiom proof_of_Always_positive_simple_safety_wit_9 : Always_positive_simple_safety_wit_9.
Axiom proof_of_Always_positive_simple_safety_wit_10 : Always_positive_simple_safety_wit_10.
Axiom proof_of_Always_positive_simple_return_wit_1 : Always_positive_simple_return_wit_1.
Axiom proof_of_Always_positive_simple_return_wit_2 : Always_positive_simple_return_wit_2.
Axiom proof_of_Always_positive_simple_return_wit_3 : Always_positive_simple_return_wit_3.
Axiom proof_of_Always_positive_simple_return_wit_4 : Always_positive_simple_return_wit_4.
Axiom proof_of_Always_positive_safety_wit_1 : Always_positive_safety_wit_1.
Axiom proof_of_Always_positive_safety_wit_2 : Always_positive_safety_wit_2.
Axiom proof_of_Always_positive_safety_wit_3 : Always_positive_safety_wit_3.
Axiom proof_of_Always_positive_safety_wit_4 : Always_positive_safety_wit_4.
Axiom proof_of_Always_positive_safety_wit_5 : Always_positive_safety_wit_5.
Axiom proof_of_Always_positive_safety_wit_6 : Always_positive_safety_wit_6.
Axiom proof_of_Always_positive_safety_wit_7 : Always_positive_safety_wit_7.
Axiom proof_of_Always_positive_safety_wit_8 : Always_positive_safety_wit_8.
Axiom proof_of_Always_positive_safety_wit_9 : Always_positive_safety_wit_9.
Axiom proof_of_Always_positive_safety_wit_10 : Always_positive_safety_wit_10.
Axiom proof_of_Always_positive_safety_wit_11 : Always_positive_safety_wit_11.
Axiom proof_of_Always_positive_safety_wit_12 : Always_positive_safety_wit_12.
Axiom proof_of_Always_positive_safety_wit_13 : Always_positive_safety_wit_13.
Axiom proof_of_Always_positive_safety_wit_14 : Always_positive_safety_wit_14.
Axiom proof_of_Always_positive_safety_wit_15 : Always_positive_safety_wit_15.
Axiom proof_of_Always_positive_safety_wit_16 : Always_positive_safety_wit_16.
Axiom proof_of_Always_positive_safety_wit_17 : Always_positive_safety_wit_17.
Axiom proof_of_Always_positive_safety_wit_18 : Always_positive_safety_wit_18.
Axiom proof_of_Always_positive_safety_wit_19 : Always_positive_safety_wit_19.
Axiom proof_of_Always_positive_safety_wit_20 : Always_positive_safety_wit_20.
Axiom proof_of_Always_positive_safety_wit_21 : Always_positive_safety_wit_21.
Axiom proof_of_Always_positive_safety_wit_22 : Always_positive_safety_wit_22.
Axiom proof_of_Always_positive_safety_wit_23 : Always_positive_safety_wit_23.
Axiom proof_of_Always_positive_entail_wit_1 : Always_positive_entail_wit_1.
Axiom proof_of_Always_positive_entail_wit_2 : Always_positive_entail_wit_2.
Axiom proof_of_Always_positive_return_wit_1 : Always_positive_return_wit_1.
Axiom proof_of_Always_positive_return_wit_2 : Always_positive_return_wit_2.
Axiom proof_of_Always_positive_return_wit_3 : Always_positive_return_wit_3.
Axiom proof_of_Always_positive_return_wit_4 : Always_positive_return_wit_4.
Axiom proof_of_Always_positive_return_wit_5 : Always_positive_return_wit_5.

End VC_Correct.
