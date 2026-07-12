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

(*----- Function arr_sum -----*)

Definition arr_sum_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_safety_wit_3 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
) \/
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
).

Definition arr_sum_safety_wit_3_split_goal_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ”
.

Definition arr_sum_safety_wit_3_split_goal_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
.

Definition arr_sum_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition arr_sum_entail_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  TT && emp 
|--
  “ (0 = (sum ((sublist (0) (0) (l))))) ”
  &&  emp
).

Definition arr_sum_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (0 = (sum ((sublist (0) (0) (l)))))
.

Definition arr_sum_entail_wit_2 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  emp
).

Definition arr_sum_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l)))))
.

Definition arr_sum_return_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (ret = (sum (l))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
).

Definition arr_sum_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (ret = (sum (l)))
.

Definition arr_sum_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (i_2 < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (ret = (sum ((sublist (0) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

(*----- Function arr_sum_do_while -----*)

Definition arr_sum_do_while_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_do_while_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_do_while_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((0 + (Znth 0 l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + (Znth 0 l 0) )) ”
.

Definition arr_sum_do_while_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "ret" ) )) # Int  |-> (0 + (Znth 0 l 0) ))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition arr_sum_do_while_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition arr_sum_do_while_safety_wit_6 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
) \/
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
).

Definition arr_sum_do_while_safety_wit_6_split_goal_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ”
.

Definition arr_sum_do_while_safety_wit_6_split_goal_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
.

Definition arr_sum_do_while_entail_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 <> n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 <> n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  emp
).

Definition arr_sum_do_while_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 <> n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l)))))
.

Definition arr_sum_do_while_entail_wit_2 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ ((0 + (Znth 0 l 0) ) = (sum ((sublist (0) ((0 + 1 )) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  TT && emp 
|--
  “ ((0 + (Znth 0 l 0) ) = (sum ((sublist (0) ((0 + 1 )) (l))))) ”
  &&  emp
).

Definition arr_sum_do_while_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  ((0 + (Znth 0 l 0) ) = (sum ((sublist (0) ((0 + 1 )) (l)))))
.

Definition arr_sum_do_while_return_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 = n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (ret = (sum (l))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 = n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
).

Definition arr_sum_do_while_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 = n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (ret = (sum (l)))
.

Definition arr_sum_do_while_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ”
  &&  (((a_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition arr_sum_do_while_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 <> n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (i_2 <> n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (ret = (sum ((sublist (0) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

(*----- Function arr_sum_for -----*)

Definition arr_sum_for_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_for_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_for_safety_wit_3 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
) \/
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
).

Definition arr_sum_for_safety_wit_3_split_goal_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ”
.

Definition arr_sum_for_safety_wit_3_split_goal_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
.

Definition arr_sum_for_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition arr_sum_for_entail_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  TT && emp 
|--
  “ (0 = (sum ((sublist (0) (0) (l))))) ”
  &&  emp
).

Definition arr_sum_for_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (0 = (sum ((sublist (0) (0) (l)))))
.

Definition arr_sum_for_entail_wit_2 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  emp
).

Definition arr_sum_for_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l)))))
.

Definition arr_sum_for_return_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (ret = (sum (l))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
).

Definition arr_sum_for_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (ret = (sum (l)))
.

Definition arr_sum_for_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (i_2 < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (ret = (sum ((sublist (0) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

(*----- Function arr_sum_which_implies -----*)

Definition arr_sum_which_implies_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_which_implies_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_which_implies_safety_wit_3 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
) \/
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
).

Definition arr_sum_which_implies_safety_wit_3_split_goal_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ”
.

Definition arr_sum_which_implies_safety_wit_3_split_goal_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
.

Definition arr_sum_which_implies_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition arr_sum_which_implies_entail_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  TT && emp 
|--
  “ (0 = (sum ((sublist (0) (0) (l))))) ”
  &&  emp
).

Definition arr_sum_which_implies_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (0 = (sum ((sublist (0) (0) (l)))))
.

Definition arr_sum_which_implies_entail_wit_2 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  emp
).

Definition arr_sum_which_implies_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l)))))
.

Definition arr_sum_which_implies_return_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (ret = (sum (l))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
).

Definition arr_sum_which_implies_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (ret = (sum (l)))
.

Definition arr_sum_which_implies_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (i_2 < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (ret = (sum ((sublist (0) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

(*----- Function arr_sum_update -----*)

Definition arr_sum_update_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_update_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_update_safety_wit_3 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) 0) )) ”
) \/
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) 0) )) ”
).

Definition arr_sum_update_safety_wit_3_split_goal_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) 0) ) <= INT_MAX) ”
.

Definition arr_sum_update_safety_wit_3_split_goal_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((INT_MIN) <= (ret + (Znth i (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) 0) )) ”
.

Definition arr_sum_update_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i_2 (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) 0) ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_update_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre (replace_Znth (i) (0) ((app ((zeros (i))) ((sublist (i) (n_pre) (l)))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition arr_sum_update_entail_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre = (Zlength (l))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (l))))) ”
  &&  (IntArray.full a_pre n_pre (app ((zeros (0))) ((sublist (0) (n_pre) (l)))) )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  TT && emp 
|--
  “ (0 = (sum ((sublist (0) (0) (l))))) ” 
  &&  “ (n_pre = (Zlength (l))) ” 
  &&  “ (l = (app ((zeros (0))) ((sublist (0) (n_pre) (l))))) ”
  &&  emp
).

Definition arr_sum_update_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (0 = (sum ((sublist (0) (0) (l)))))
.

Definition arr_sum_update_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (n_pre = (Zlength (l)))
.

Definition arr_sum_update_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (l = (app ((zeros (0))) ((sublist (0) (n_pre) (l)))))
.

Definition arr_sum_update_entail_wit_2 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre (replace_Znth (i_2) (0) ((app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))))) )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ (n_pre = (Zlength (l))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ ((ret + (Znth i_2 (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  (IntArray.full a_pre n_pre (app ((zeros ((i_2 + 1 )))) ((sublist ((i_2 + 1 )) (n_pre) (l)))) )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ” 
  &&  “ ((replace_Znth (i_2) (0) ((app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))))) = (app ((zeros ((i_2 + 1 )))) ((sublist ((i_2 + 1 )) (n_pre) (l))))) ”
  &&  emp
).

Definition arr_sum_update_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  ((ret + (Znth i_2 (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l)))))
.

Definition arr_sum_update_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  ((replace_Znth (i_2) (0) ((app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))))) = (app ((zeros ((i_2 + 1 )))) ((sublist ((i_2 + 1 )) (n_pre) (l)))))
.

Definition arr_sum_update_return_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
|--
  “ (ret = (sum (l))) ”
  &&  (IntArray.full a_pre n_pre (zeros (n_pre)) )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ” 
  &&  “ ((app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) = (zeros (n_pre))) ”
  &&  emp
).

Definition arr_sum_update_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (ret = (sum (l)))
.

Definition arr_sum_update_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  ((app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) = (zeros (n_pre)))
.

Definition arr_sum_update_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
|--
  “ (i_2 < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (n_pre = (Zlength (l))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (ret = (sum ((sublist (0) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
.

Definition arr_sum_update_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
|--
  “ (i_2 < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ (n_pre = (Zlength (l))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (ret = (sum ((sublist (0) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre i_2 0 n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
.

(*----- Function arr_sum_pointer -----*)

Definition arr_sum_pointer_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_pointer_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_pointer_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (endp: Z) (i_2: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH8 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "endp" ) )) # Ptr  |-> endp)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_pointer_safety_wit_4 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (endp: Z) (ret: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (endp <> (a_pre + (i * sizeof(INT))))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "endp" ) )) # Ptr  |-> endp)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
) \/
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (endp: Z) (ret: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (endp <> (a_pre + (i * sizeof(INT))))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "endp" ) )) # Ptr  |-> endp)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
).

Definition arr_sum_pointer_safety_wit_4_split_goal_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (endp: Z) (ret: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (endp <> (a_pre + (i * sizeof(INT))))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "endp" ) )) # Ptr  |-> endp)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((ret + (Znth i l 0) ) <= INT_MAX) ”
.

Definition arr_sum_pointer_safety_wit_4_split_goal_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (endp: Z) (ret: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (endp <> (a_pre + (i * sizeof(INT))))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "endp" ) )) # Ptr  |-> endp)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  “ ((INT_MIN) <= (ret + (Znth i l 0) )) ”
.

Definition arr_sum_pointer_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (endp: Z) (ret: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (endp <> (a_pre + (i * sizeof(INT))))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "endp" ) )) # Ptr  |-> endp)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition arr_sum_pointer_entail_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (n_pre = (Zlength (l))) ” 
  &&  “ ((a_pre + (n_pre * sizeof(INT))) = (a_pre + (n_pre * sizeof(INT)))) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  TT && emp 
|--
  “ (0 = (sum ((sublist (0) (0) (l))))) ” 
  &&  “ (n_pre = (Zlength (l))) ”
  &&  emp
).

Definition arr_sum_pointer_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (0 = (sum ((sublist (0) (0) (l)))))
.

Definition arr_sum_pointer_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (n_pre = (Zlength (l)))
.

Definition arr_sum_pointer_entail_wit_2 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (endp: Z) (i: Z) (PreH1 : (((endp - (a_pre + (i * sizeof(INT))) ) ÷ sizeof(INT) ) <> 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 l 0)) /\ ((Znth i_3 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (endp <> (a_pre + (i * sizeof(INT)))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) ” 
  &&  “ (n_pre = (Zlength (l))) ” 
  &&  “ (endp = (a_pre + (n_pre * sizeof(INT)))) ” 
  &&  “ (ret = (sum ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (endp: Z) (i: Z) (PreH1 : (((endp - (a_pre + (i * sizeof(INT))) ) ÷ sizeof(INT) ) <> 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 l 0)) /\ ((Znth i_3 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  TT && emp 
|--
  “ (endp <> (a_pre + (i * sizeof(INT)))) ” 
  &&  “ (i < n_pre) ”
  &&  emp
).

Definition arr_sum_pointer_entail_wit_2_split_goal_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (endp: Z) (i: Z) (PreH1 : (((endp - (a_pre + (i * sizeof(INT))) ) ÷ sizeof(INT) ) <> 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 l 0)) /\ ((Znth i_3 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (endp <> (a_pre + (i * sizeof(INT))))
.

Definition arr_sum_pointer_entail_wit_2_split_goal_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (endp: Z) (i: Z) (PreH1 : (((endp - (a_pre + (i * sizeof(INT))) ) ÷ sizeof(INT) ) <> 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 l 0)) /\ ((Znth i_3 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (i < n_pre)
.

Definition arr_sum_pointer_entail_wit_3 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (endp: Z) (ret: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < n_pre)) (PreH5 : (endp <> (a_pre + (i_2 * sizeof(INT))))) (PreH6 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 l 0)) /\ ((Znth i_3 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (n_pre = (Zlength (l))) ” 
  &&  “ (endp = (a_pre + (n_pre * sizeof(INT)))) ” 
  &&  “ ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (endp: Z) (ret: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < n_pre)) (PreH5 : (endp <> (a_pre + (i_2 * sizeof(INT))))) (PreH6 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 l 0)) /\ ((Znth i_3 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  emp
).

Definition arr_sum_pointer_entail_wit_3_split_goal_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (endp: Z) (ret: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < n_pre)) (PreH5 : (endp <> (a_pre + (i_2 * sizeof(INT))))) (PreH6 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 l 0)) /\ ((Znth i_3 l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l)))))
.

Definition arr_sum_pointer_return_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (endp: Z) (i_2: Z) (PreH1 : (((endp - (a_pre + (i_2 * sizeof(INT))) ) ÷ sizeof(INT) ) = 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (ret = (sum (l))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (endp: Z) (i_2: Z) (PreH1 : (((endp - (a_pre + (i_2 * sizeof(INT))) ) ÷ sizeof(INT) ) = 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
).

Definition arr_sum_pointer_return_wit_1_split_goal_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (endp: Z) (i_2: Z) (PreH1 : (((endp - (a_pre + (i_2 * sizeof(INT))) ) ÷ sizeof(INT) ) = 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (ret = (sum (l)))
.

Definition arr_sum_pointer_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (endp: Z) (ret: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < n_pre)) (PreH5 : (endp <> (a_pre + (i_2 * sizeof(INT))))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ (endp <> (a_pre + (i_2 * sizeof(INT)))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (n_pre = (Zlength (l))) ” 
  &&  “ (endp = (a_pre + (n_pre * sizeof(INT)))) ” 
  &&  “ (ret = (sum ((sublist (0) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Module Type VC_Correct.


Axiom proof_of_arr_sum_safety_wit_1 : arr_sum_safety_wit_1.
Axiom proof_of_arr_sum_safety_wit_2 : arr_sum_safety_wit_2.
Axiom proof_of_arr_sum_safety_wit_3 : arr_sum_safety_wit_3.
Axiom proof_of_arr_sum_safety_wit_4 : arr_sum_safety_wit_4.
Axiom proof_of_arr_sum_entail_wit_1 : arr_sum_entail_wit_1.
Axiom proof_of_arr_sum_entail_wit_2 : arr_sum_entail_wit_2.
Axiom proof_of_arr_sum_return_wit_1 : arr_sum_return_wit_1.
Axiom proof_of_arr_sum_partial_solve_wit_1 : arr_sum_partial_solve_wit_1.
Axiom proof_of_arr_sum_do_while_safety_wit_1 : arr_sum_do_while_safety_wit_1.
Axiom proof_of_arr_sum_do_while_safety_wit_2 : arr_sum_do_while_safety_wit_2.
Axiom proof_of_arr_sum_do_while_safety_wit_3 : arr_sum_do_while_safety_wit_3.
Axiom proof_of_arr_sum_do_while_safety_wit_4 : arr_sum_do_while_safety_wit_4.
Axiom proof_of_arr_sum_do_while_safety_wit_5 : arr_sum_do_while_safety_wit_5.
Axiom proof_of_arr_sum_do_while_safety_wit_6 : arr_sum_do_while_safety_wit_6.
Axiom proof_of_arr_sum_do_while_entail_wit_1 : arr_sum_do_while_entail_wit_1.
Axiom proof_of_arr_sum_do_while_entail_wit_2 : arr_sum_do_while_entail_wit_2.
Axiom proof_of_arr_sum_do_while_return_wit_1 : arr_sum_do_while_return_wit_1.
Axiom proof_of_arr_sum_do_while_partial_solve_wit_1 : arr_sum_do_while_partial_solve_wit_1.
Axiom proof_of_arr_sum_do_while_partial_solve_wit_2 : arr_sum_do_while_partial_solve_wit_2.
Axiom proof_of_arr_sum_for_safety_wit_1 : arr_sum_for_safety_wit_1.
Axiom proof_of_arr_sum_for_safety_wit_2 : arr_sum_for_safety_wit_2.
Axiom proof_of_arr_sum_for_safety_wit_3 : arr_sum_for_safety_wit_3.
Axiom proof_of_arr_sum_for_safety_wit_4 : arr_sum_for_safety_wit_4.
Axiom proof_of_arr_sum_for_entail_wit_1 : arr_sum_for_entail_wit_1.
Axiom proof_of_arr_sum_for_entail_wit_2 : arr_sum_for_entail_wit_2.
Axiom proof_of_arr_sum_for_return_wit_1 : arr_sum_for_return_wit_1.
Axiom proof_of_arr_sum_for_partial_solve_wit_1 : arr_sum_for_partial_solve_wit_1.
Axiom proof_of_arr_sum_which_implies_safety_wit_1 : arr_sum_which_implies_safety_wit_1.
Axiom proof_of_arr_sum_which_implies_safety_wit_2 : arr_sum_which_implies_safety_wit_2.
Axiom proof_of_arr_sum_which_implies_safety_wit_3 : arr_sum_which_implies_safety_wit_3.
Axiom proof_of_arr_sum_which_implies_safety_wit_4 : arr_sum_which_implies_safety_wit_4.
Axiom proof_of_arr_sum_which_implies_entail_wit_1 : arr_sum_which_implies_entail_wit_1.
Axiom proof_of_arr_sum_which_implies_entail_wit_2 : arr_sum_which_implies_entail_wit_2.
Axiom proof_of_arr_sum_which_implies_return_wit_1 : arr_sum_which_implies_return_wit_1.
Axiom proof_of_arr_sum_which_implies_partial_solve_wit_1 : arr_sum_which_implies_partial_solve_wit_1.
Axiom proof_of_arr_sum_update_safety_wit_1 : arr_sum_update_safety_wit_1.
Axiom proof_of_arr_sum_update_safety_wit_2 : arr_sum_update_safety_wit_2.
Axiom proof_of_arr_sum_update_safety_wit_3 : arr_sum_update_safety_wit_3.
Axiom proof_of_arr_sum_update_safety_wit_4 : arr_sum_update_safety_wit_4.
Axiom proof_of_arr_sum_update_safety_wit_5 : arr_sum_update_safety_wit_5.
Axiom proof_of_arr_sum_update_entail_wit_1 : arr_sum_update_entail_wit_1.
Axiom proof_of_arr_sum_update_entail_wit_2 : arr_sum_update_entail_wit_2.
Axiom proof_of_arr_sum_update_return_wit_1 : arr_sum_update_return_wit_1.
Axiom proof_of_arr_sum_update_partial_solve_wit_1 : arr_sum_update_partial_solve_wit_1.
Axiom proof_of_arr_sum_update_partial_solve_wit_2 : arr_sum_update_partial_solve_wit_2.
Axiom proof_of_arr_sum_pointer_safety_wit_1 : arr_sum_pointer_safety_wit_1.
Axiom proof_of_arr_sum_pointer_safety_wit_2 : arr_sum_pointer_safety_wit_2.
Axiom proof_of_arr_sum_pointer_safety_wit_3 : arr_sum_pointer_safety_wit_3.
Axiom proof_of_arr_sum_pointer_safety_wit_4 : arr_sum_pointer_safety_wit_4.
Axiom proof_of_arr_sum_pointer_safety_wit_5 : arr_sum_pointer_safety_wit_5.
Axiom proof_of_arr_sum_pointer_entail_wit_1 : arr_sum_pointer_entail_wit_1.
Axiom proof_of_arr_sum_pointer_entail_wit_2 : arr_sum_pointer_entail_wit_2.
Axiom proof_of_arr_sum_pointer_entail_wit_3 : arr_sum_pointer_entail_wit_3.
Axiom proof_of_arr_sum_pointer_return_wit_1 : arr_sum_pointer_return_wit_1.
Axiom proof_of_arr_sum_pointer_partial_solve_wit_1 : arr_sum_pointer_partial_solve_wit_1.

End VC_Correct.
