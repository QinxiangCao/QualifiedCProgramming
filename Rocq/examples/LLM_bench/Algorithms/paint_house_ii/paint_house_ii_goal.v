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
Require Import SimpleC.EE.LLM_bench.Algorithms.paint_house_ii.paint_house_ii_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.

(*----- Function paint_house_ii -----*)

Definition paint_house_ii_safety_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) ,
  ((( &( "min1" ) )) # Int  |->_)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition paint_house_ii_safety_wit_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) ,
  ((( &( "min2" ) )) # Int  |->_)
  **  ((( &( "min1" ) )) # Int  |-> 0)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition paint_house_ii_safety_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) ,
  ((( &( "min1_color" ) )) # Int  |->_)
  **  ((( &( "min2" ) )) # Int  |-> 0)
  **  ((( &( "min1" ) )) # Int  |-> 0)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition paint_house_ii_safety_wit_4 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) ,
  ((( &( "min1_color" ) )) # Int  |->_)
  **  ((( &( "min2" ) )) # Int  |-> 0)
  **  ((( &( "min1" ) )) # Int  |-> 0)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition paint_house_ii_safety_wit_5 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "min1_color" ) )) # Int  |-> (-1))
  **  ((( &( "min2" ) )) # Int  |-> 0)
  **  ((( &( "min1" ) )) # Int  |-> 0)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition paint_house_ii_safety_wit_6 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  ((( &( "new_min1" ) )) # Int  |->_)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min1_color" ) )) # Int  |-> min1_color)
  **  ((( &( "min1" ) )) # Int  |-> min1)
  **  ((( &( "min2" ) )) # Int  |-> min2)
  **  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition paint_house_ii_safety_wit_7 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  ((( &( "new_min2" ) )) # Int  |->_)
  **  ((( &( "new_min1" ) )) # Int  |-> 1000000000)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min1_color" ) )) # Int  |-> min1_color)
  **  ((( &( "min1" ) )) # Int  |-> min1)
  **  ((( &( "min2" ) )) # Int  |-> min2)
  **  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1000000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition paint_house_ii_safety_wit_8 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  ((( &( "new_min1_color" ) )) # Int  |->_)
  **  ((( &( "new_min2" ) )) # Int  |-> 1000000000)
  **  ((( &( "new_min1" ) )) # Int  |-> 1000000000)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min1_color" ) )) # Int  |-> min1_color)
  **  ((( &( "min1" ) )) # Int  |-> min1)
  **  ((( &( "min2" ) )) # Int  |-> min2)
  **  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition paint_house_ii_safety_wit_9 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  ((( &( "new_min1_color" ) )) # Int  |->_)
  **  ((( &( "new_min2" ) )) # Int  |-> 1000000000)
  **  ((( &( "new_min1" ) )) # Int  |-> 1000000000)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min1_color" ) )) # Int  |-> min1_color)
  **  ((( &( "min1" ) )) # Int  |-> min1)
  **  ((( &( "min2" ) )) # Int  |-> min2)
  **  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition paint_house_ii_safety_wit_10 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (i: Z) (min1_color: Z) (min1: Z) (min2: Z) (new_min1: Z) (new_min2: Z) (new_min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((-1) <= min1_color)) (PreH12 : (min1_color < k_pre)) (PreH13 : (0 <= min1)) (PreH14 : (min1 <= 1000000000)) (PreH15 : (0 <= min2)) (PreH16 : (min2 <= 1000000000)) (PreH17 : (new_min1 = 1000000000)) (PreH18 : (new_min2 = 1000000000)) (PreH19 : (new_min1_color = (-1))) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH21 : (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min1_color" ) )) # Int  |-> min1_color)
  **  ((( &( "min1" ) )) # Int  |-> min1)
  **  ((( &( "min2" ) )) # Int  |-> min2)
  **  ((( &( "new_min1" ) )) # Int  |-> new_min1)
  **  ((( &( "new_min2" ) )) # Int  |-> new_min2)
  **  ((( &( "new_min1_color" ) )) # Int  |-> new_min1_color)
  **  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition paint_house_ii_safety_wit_11 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH17 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH18 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH21 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
  **  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  ((( &( "min1_color" ) )) # Int  |-> min1_color)
  **  ((( &( "min2" ) )) # Int  |-> min2)
  **  ((( &( "min1" ) )) # Int  |-> min1)
  **  ((( &( "new_min1_color" ) )) # Int  |-> new_min1_color)
  **  ((( &( "new_min2" ) )) # Int  |-> new_min2)
  **  ((( &( "new_min1" ) )) # Int  |-> new_min1)
|--
  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ”
.

Definition paint_house_ii_safety_wit_12 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (i: Z) (c: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "min1_color" ) )) # Int  |-> min1_color)
  **  ((( &( "min2" ) )) # Int  |-> min2)
  **  ((( &( "min1" ) )) # Int  |-> min1)
  **  ((( &( "new_min1_color" ) )) # Int  |-> new_min1_color)
  **  ((( &( "new_min1" ) )) # Int  |-> new_min1)
  **  ((( &( "new_min2" ) )) # Int  |-> new_min2)
  **  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  “ ((c + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition paint_house_ii_safety_wit_13 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (new_min1: Z) (min1: Z) (new_min2: Z) (min2: Z) (new_min1_color: Z) (min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (new_min1 = min1)) (PreH12 : (new_min2 = min2)) (PreH13 : (new_min1_color = min1_color)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (0 <= min1_color)) (PreH19 : (min1_color < k_pre)) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre (i + 1 ) min1 min2 min1_color )) ,
  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min1" ) )) # Int  |-> min1)
  **  ((( &( "min2" ) )) # Int  |-> min2)
  **  ((( &( "min1_color" ) )) # Int  |-> min1_color)
  **  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition paint_house_ii_entail_wit_1 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) < k_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre 0 0 0 (-1) ) ”
  &&  (IntPtrArray2.full costs_pre n_pre costs_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) ,
  TT && emp 
|--
  “ (PaintHouseIIDPState costs_l n_pre k_pre 0 0 0 (-1) ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) ,
  (PaintHouseIIDPState costs_l n_pre k_pre 0 0 0 (-1) )
.

Definition paint_house_ii_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) ,
  forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_1_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_entail_wit_2 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-1) <= min1_color) ” 
  &&  “ (min1_color < k_pre) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ” 
  &&  “ (0 <= min2) ” 
  &&  “ (min2 <= 1000000000) ” 
  &&  “ (1000000000 = 1000000000) ” 
  &&  “ (1000000000 = 1000000000) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color 1000000000 1000000000 (-1) ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  TT && emp 
|--
  “ (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color 1000000000 1000000000 (-1) ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color 1000000000 1000000000 (-1) )
.

Definition paint_house_ii_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_entail_wit_3 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr_2: Z) (i: Z) (min1_color: Z) (min1: Z) (min2: Z) (new_min1: Z) (new_min2: Z) (new_min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((-1) <= min1_color)) (PreH12 : (min1_color < k_pre)) (PreH13 : (0 <= min1)) (PreH14 : (min1 <= 1000000000)) (PreH15 : (0 <= min2)) (PreH16 : (min2 <= 1000000000)) (PreH17 : (new_min1 = 1000000000)) (PreH18 : (new_min2 = 1000000000)) (PreH19 : (new_min1_color = (-1))) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH21 : (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr_2 costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ ((-1) <= min1_color) ” 
  &&  “ (min1_color < k_pre) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ” 
  &&  “ (0 <= min2) ” 
  &&  “ (min2 <= 1000000000) ” 
  &&  “ ((-1) <= new_min1_color) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= new_min2) ” 
  &&  “ (new_min2 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min1: Z) (min2: Z) (new_min1: Z) (new_min2: Z) (new_min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((-1) <= min1_color)) (PreH12 : (min1_color < k_pre)) (PreH13 : (0 <= min1)) (PreH14 : (min1 <= 1000000000)) (PreH15 : (0 <= min2)) (PreH16 : (min2 <= 1000000000)) (PreH17 : (new_min1 = 1000000000)) (PreH18 : (new_min2 = 1000000000)) (PreH19 : (new_min1_color = (-1))) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH21 : (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_3_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min1: Z) (min2: Z) (new_min1: Z) (new_min2: Z) (new_min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((-1) <= min1_color)) (PreH12 : (min1_color < k_pre)) (PreH13 : (0 <= min1)) (PreH14 : (min1 <= 1000000000)) (PreH15 : (0 <= min2)) (PreH16 : (min2 <= 1000000000)) (PreH17 : (new_min1 = 1000000000)) (PreH18 : (new_min2 = 1000000000)) (PreH19 : (new_min1_color = (-1))) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH21 : (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_3_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min1: Z) (min2: Z) (new_min1: Z) (new_min2: Z) (new_min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((-1) <= min1_color)) (PreH12 : (min1_color < k_pre)) (PreH13 : (0 <= min1)) (PreH14 : (min1 <= 1000000000)) (PreH15 : (0 <= min2)) (PreH16 : (min2 <= 1000000000)) (PreH17 : (new_min1 = 1000000000)) (PreH18 : (new_min2 = 1000000000)) (PreH19 : (new_min1_color = (-1))) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH21 : (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_entail_wit_4_1 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr_2: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c = min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr_2 costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= min2) ” 
  &&  “ (min2 <= 1000000000) ” 
  &&  “ (0 <= (Znth c (Znth i costs_l __default__List_Z) 0)) ” 
  &&  “ ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000) ” 
  &&  “ ((min2 + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c min2 ) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c = min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  TT && emp 
|--
  “ (PaintHouseIIPrevSelection min1 min2 min1_color min1_color min2 ) ” 
  &&  “ ((min2 + (Znth min1_color (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ ((Znth min1_color (Znth i costs_l __default__List_Z) 0) <= 10000) ” 
  &&  “ (0 <= (Znth min1_color (Znth i costs_l __default__List_Z) 0)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_4_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c = min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (PaintHouseIIPrevSelection min1 min2 min1_color min1_color min2 )
.

Definition paint_house_ii_entail_wit_4_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c = min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  ((min2 + (Znth min1_color (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)
.

Definition paint_house_ii_entail_wit_4_1_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c = min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  ((Znth min1_color (Znth i costs_l __default__List_Z) 0) <= 10000)
.

Definition paint_house_ii_entail_wit_4_1_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c = min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (0 <= (Znth min1_color (Znth i costs_l __default__List_Z) 0))
.

Definition paint_house_ii_entail_wit_4_1_split_goal_5 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c = min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_4_1_split_goal_6 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c = min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_entail_wit_4_2 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr_2: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c <> min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr_2 costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ” 
  &&  “ (0 <= (Znth c (Znth i costs_l __default__List_Z) 0)) ” 
  &&  “ ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000) ” 
  &&  “ ((min1 + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c min1 ) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c <> min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  TT && emp 
|--
  “ (PaintHouseIIPrevSelection min1 min2 min1_color c min1 ) ” 
  &&  “ ((min1 + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000) ” 
  &&  “ (0 <= (Znth c (Znth i costs_l __default__List_Z) 0)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_4_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c <> min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (PaintHouseIIPrevSelection min1 min2 min1_color c min1 )
.

Definition paint_house_ii_entail_wit_4_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c <> min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  ((min1 + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)
.

Definition paint_house_ii_entail_wit_4_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c <> min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)
.

Definition paint_house_ii_entail_wit_4_2_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c <> min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))
.

Definition paint_house_ii_entail_wit_4_2_split_goal_5 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c <> min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_4_2_split_goal_6 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c <> min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_entail_wit_5_1 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c < k_pre)) (PreH15 : (0 <= prev)) (PreH16 : (prev <= 1000000000)) (PreH17 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH18 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH19 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH20 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH21 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH22 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= prev) ” 
  &&  “ (prev <= 1000000000) ” 
  &&  “ (0 <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) = (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c prev ) ” 
  &&  “ ((-1) <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color (prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) new_min1 c ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c < k_pre)) (PreH15 : (0 <= prev)) (PreH16 : (prev <= 1000000000)) (PreH17 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH18 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH19 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH20 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH21 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH22 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  TT && emp 
|--
  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color (prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) new_min1 c ) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_5_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c < k_pre)) (PreH15 : (0 <= prev)) (PreH16 : (prev <= 1000000000)) (PreH17 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH18 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH19 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH20 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH21 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH22 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color (prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) new_min1 c )
.

Definition paint_house_ii_entail_wit_5_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c < k_pre)) (PreH15 : (0 <= prev)) (PreH16 : (prev <= 1000000000)) (PreH17 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH18 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH19 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH20 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH21 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH22 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (new_min1 <= 1000000000)
.

Definition paint_house_ii_entail_wit_5_1_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c < k_pre)) (PreH15 : (0 <= prev)) (PreH16 : (prev <= 1000000000)) (PreH17 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH18 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH19 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH20 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH21 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH22 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_5_1_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c < k_pre)) (PreH15 : (0 <= prev)) (PreH16 : (prev <= 1000000000)) (PreH17 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH18 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH19 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH20 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH21 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH22 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_entail_wit_5_2 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= prev) ” 
  &&  “ (prev <= 1000000000) ” 
  &&  “ (0 <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) = (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c prev ) ” 
  &&  “ ((-1) <= new_min1_color) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color new_min1 (prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  TT && emp 
|--
  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color new_min1 (prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) new_min1_color ) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ ((-1) <= new_min1_color) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_5_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color new_min1 (prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) new_min1_color )
.

Definition paint_house_ii_entail_wit_5_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (0 <= new_min1)
.

Definition paint_house_ii_entail_wit_5_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (new_min1_color < k_pre)
.

Definition paint_house_ii_entail_wit_5_2_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  ((-1) <= new_min1_color)
.

Definition paint_house_ii_entail_wit_5_2_split_goal_5 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_5_2_split_goal_6 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_entail_wit_5_3 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= prev) ” 
  &&  “ (prev <= 1000000000) ” 
  &&  “ (0 <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) = (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c prev ) ” 
  &&  “ ((-1) <= new_min1_color) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= new_min2) ” 
  &&  “ (new_min2 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  TT && emp 
|--
  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color ) ” 
  &&  “ (0 <= new_min2) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ ((-1) <= new_min1_color) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_5_3_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )
.

Definition paint_house_ii_entail_wit_5_3_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (0 <= new_min2)
.

Definition paint_house_ii_entail_wit_5_3_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (0 <= new_min1)
.

Definition paint_house_ii_entail_wit_5_3_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (new_min1_color < k_pre)
.

Definition paint_house_ii_entail_wit_5_3_split_goal_5 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  ((-1) <= new_min1_color)
.

Definition paint_house_ii_entail_wit_5_3_split_goal_6 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_5_3_split_goal_7 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_entail_wit_6 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr_2: Z) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr_2 costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (c_2 + 1 )) ” 
  &&  “ ((c_2 + 1 ) <= k_pre) ” 
  &&  “ ((-1) <= min1_color) ” 
  &&  “ (min1_color < k_pre) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ” 
  &&  “ (0 <= min2) ” 
  &&  “ (min2 <= 1000000000) ” 
  &&  “ ((-1) <= new_min1_color) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= new_min2) ” 
  &&  “ (new_min2 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  TT && emp 
|--
  “ (min2 <= 1000000000) ” 
  &&  “ (0 <= min2) ” 
  &&  “ (min1 <= 1000000000) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1_color < k_pre) ” 
  &&  “ ((-1) <= min1_color) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_6_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (min2 <= 1000000000)
.

Definition paint_house_ii_entail_wit_6_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (0 <= min2)
.

Definition paint_house_ii_entail_wit_6_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (min1 <= 1000000000)
.

Definition paint_house_ii_entail_wit_6_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (0 <= min1)
.

Definition paint_house_ii_entail_wit_6_split_goal_5 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (min1_color < k_pre)
.

Definition paint_house_ii_entail_wit_6_split_goal_6 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  ((-1) <= min1_color)
.

Definition paint_house_ii_entail_wit_6_split_goal_7 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_6_split_goal_8 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_entail_wit_7 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c_3: Z) (i: Z)  __default__List_Z (PreH1 : (c_3 >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c_3)) (PreH14 : (c_3 <= k_pre)) (PreH15 : ((-1) <= min1_color)) (PreH16 : (min1_color < k_pre)) (PreH17 : (0 <= min1)) (PreH18 : (min1 <= 1000000000)) (PreH19 : (0 <= min2)) (PreH20 : (min2 <= 1000000000)) (PreH21 : ((-1) <= new_min1_color)) (PreH22 : (new_min1_color < k_pre)) (PreH23 : (0 <= new_min1)) (PreH24 : (new_min1 <= 1000000000)) (PreH25 : (0 <= new_min2)) (PreH26 : (new_min2 <= 1000000000)) (PreH27 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH28 : (PaintHouseIIInnerState costs_l n_pre k_pre i c_3 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color ) ” 
  &&  “ (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.full costs_pre n_pre costs_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c_3: Z) (i: Z)  __default__List_Z (PreH1 : (c_3 >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c_3)) (PreH14 : (c_3 <= k_pre)) (PreH15 : ((-1) <= min1_color)) (PreH16 : (min1_color < k_pre)) (PreH17 : (0 <= min1)) (PreH18 : (min1 <= 1000000000)) (PreH19 : (0 <= min2)) (PreH20 : (min2 <= 1000000000)) (PreH21 : ((-1) <= new_min1_color)) (PreH22 : (new_min1_color < k_pre)) (PreH23 : (0 <= new_min1)) (PreH24 : (new_min1 <= 1000000000)) (PreH25 : (0 <= new_min2)) (PreH26 : (new_min2 <= 1000000000)) (PreH27 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH28 : (PaintHouseIIInnerState costs_l n_pre k_pre i c_3 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  “ (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color ) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  (IntPtrArray2.full costs_pre n_pre costs_l )
).

Definition paint_house_ii_entail_wit_7_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c_3: Z) (i: Z)  __default__List_Z (PreH1 : (c_3 >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c_3)) (PreH14 : (c_3 <= k_pre)) (PreH15 : ((-1) <= min1_color)) (PreH16 : (min1_color < k_pre)) (PreH17 : (0 <= min1)) (PreH18 : (min1 <= 1000000000)) (PreH19 : (0 <= min2)) (PreH20 : (min2 <= 1000000000)) (PreH21 : ((-1) <= new_min1_color)) (PreH22 : (new_min1_color < k_pre)) (PreH23 : (0 <= new_min1)) (PreH24 : (new_min1 <= 1000000000)) (PreH25 : (0 <= new_min2)) (PreH26 : (new_min2 <= 1000000000)) (PreH27 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH28 : (PaintHouseIIInnerState costs_l n_pre k_pre i c_3 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  “ (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
.

Definition paint_house_ii_entail_wit_7_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c_3: Z) (i: Z)  __default__List_Z (PreH1 : (c_3 >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c_3)) (PreH14 : (c_3 <= k_pre)) (PreH15 : ((-1) <= min1_color)) (PreH16 : (min1_color < k_pre)) (PreH17 : (0 <= min1)) (PreH18 : (min1 <= 1000000000)) (PreH19 : (0 <= min2)) (PreH20 : (min2 <= 1000000000)) (PreH21 : ((-1) <= new_min1_color)) (PreH22 : (new_min1_color < k_pre)) (PreH23 : (0 <= new_min1)) (PreH24 : (new_min1 <= 1000000000)) (PreH25 : (0 <= new_min2)) (PreH26 : (new_min2 <= 1000000000)) (PreH27 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH28 : (PaintHouseIIInnerState costs_l n_pre k_pre i c_3 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  “ (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
.

Definition paint_house_ii_entail_wit_7_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c_3: Z) (i: Z)  __default__List_Z (PreH1 : (c_3 >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c_3)) (PreH14 : (c_3 <= k_pre)) (PreH15 : ((-1) <= min1_color)) (PreH16 : (min1_color < k_pre)) (PreH17 : (0 <= min1)) (PreH18 : (min1 <= 1000000000)) (PreH19 : (0 <= min2)) (PreH20 : (min2 <= 1000000000)) (PreH21 : ((-1) <= new_min1_color)) (PreH22 : (new_min1_color < k_pre)) (PreH23 : (0 <= new_min1)) (PreH24 : (new_min1 <= 1000000000)) (PreH25 : (0 <= new_min2)) (PreH26 : (new_min2 <= 1000000000)) (PreH27 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH28 : (PaintHouseIIInnerState costs_l n_pre k_pre i c_3 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ”
.

Definition paint_house_ii_entail_wit_7_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c_3: Z) (i: Z)  __default__List_Z (PreH1 : (c_3 >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c_3)) (PreH14 : (c_3 <= k_pre)) (PreH15 : ((-1) <= min1_color)) (PreH16 : (min1_color < k_pre)) (PreH17 : (0 <= min1)) (PreH18 : (min1 <= 1000000000)) (PreH19 : (0 <= min2)) (PreH20 : (min2 <= 1000000000)) (PreH21 : ((-1) <= new_min1_color)) (PreH22 : (new_min1_color < k_pre)) (PreH23 : (0 <= new_min1)) (PreH24 : (new_min1 <= 1000000000)) (PreH25 : (0 <= new_min2)) (PreH26 : (new_min2 <= 1000000000)) (PreH27 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH28 : (PaintHouseIIInnerState costs_l n_pre k_pre i c_3 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
.

Definition paint_house_ii_entail_wit_7_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c_3: Z) (i: Z)  __default__List_Z (PreH1 : (c_3 >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c_3)) (PreH14 : (c_3 <= k_pre)) (PreH15 : ((-1) <= min1_color)) (PreH16 : (min1_color < k_pre)) (PreH17 : (0 <= min1)) (PreH18 : (min1 <= 1000000000)) (PreH19 : (0 <= min2)) (PreH20 : (min2 <= 1000000000)) (PreH21 : ((-1) <= new_min1_color)) (PreH22 : (new_min1_color < k_pre)) (PreH23 : (0 <= new_min1)) (PreH24 : (new_min1 <= 1000000000)) (PreH25 : (0 <= new_min2)) (PreH26 : (new_min2 <= 1000000000)) (PreH27 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH28 : (PaintHouseIIInnerState costs_l n_pre k_pre i c_3 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  (IntPtrArray2.full costs_pre n_pre costs_l )
.

Definition paint_house_ii_entail_wit_8 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (new_min1 = new_min1) ” 
  &&  “ (new_min2 = new_min2) ” 
  &&  “ (new_min1_color = new_min1_color) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= new_min2) ” 
  &&  “ (new_min2 <= 1000000000) ” 
  &&  “ (0 <= new_min1_color) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre (i + 1 ) new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.full costs_pre n_pre costs_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  TT && emp 
|--
  “ (PaintHouseIIDPState costs_l n_pre k_pre (i + 1 ) new_min1 new_min2 new_min1_color ) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (0 <= new_min1_color) ” 
  &&  “ (new_min2 <= 1000000000) ” 
  &&  “ (0 <= new_min2) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_8_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (PaintHouseIIDPState costs_l n_pre k_pre (i + 1 ) new_min1 new_min2 new_min1_color )
.

Definition paint_house_ii_entail_wit_8_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (new_min1_color < k_pre)
.

Definition paint_house_ii_entail_wit_8_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (0 <= new_min1_color)
.

Definition paint_house_ii_entail_wit_8_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (new_min2 <= 1000000000)
.

Definition paint_house_ii_entail_wit_8_split_goal_5 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (0 <= new_min2)
.

Definition paint_house_ii_entail_wit_8_split_goal_6 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (new_min1 <= 1000000000)
.

Definition paint_house_ii_entail_wit_8_split_goal_7 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (0 <= new_min1)
.

Definition paint_house_ii_entail_wit_8_split_goal_8 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_8_split_goal_9 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_entail_wit_9 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (new_min1: Z) (min1: Z) (new_min2: Z) (min2: Z) (new_min1_color: Z) (min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (new_min1 = min1)) (PreH12 : (new_min2 = min2)) (PreH13 : (new_min1_color = min1_color)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (0 <= min1_color)) (PreH19 : (min1_color < k_pre)) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre (i + 1 ) min1 min2 min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((-1) <= min1_color) ” 
  &&  “ (min1_color < k_pre) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ” 
  &&  “ (0 <= min2) ” 
  &&  “ (min2 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre (i + 1 ) min1 min2 min1_color ) ”
  &&  (IntPtrArray2.full costs_pre n_pre costs_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (new_min1: Z) (min1: Z) (new_min2: Z) (min2: Z) (new_min1_color: Z) (min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (new_min1 = min1)) (PreH12 : (new_min2 = min2)) (PreH13 : (new_min1_color = min1_color)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (0 <= min1_color)) (PreH19 : (min1_color < k_pre)) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre (i + 1 ) min1 min2 min1_color )) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ”
  &&  emp
).

Definition paint_house_ii_entail_wit_9_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (new_min1: Z) (min1: Z) (new_min2: Z) (min2: Z) (new_min1_color: Z) (min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (new_min1 = min1)) (PreH12 : (new_min2 = min2)) (PreH13 : (new_min1_color = min1_color)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (0 <= min1_color)) (PreH19 : (min1_color < k_pre)) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre (i + 1 ) min1 min2 min1_color )) ,
  forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))
.

Definition paint_house_ii_entail_wit_9_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (new_min1: Z) (min1: Z) (new_min2: Z) (min2: Z) (new_min1_color: Z) (min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (new_min1 = min1)) (PreH12 : (new_min2 = min2)) (PreH13 : (new_min1_color = min1_color)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (0 <= min1_color)) (PreH19 : (min1_color < k_pre)) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre (i + 1 ) min1 min2 min1_color )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))
.

Definition paint_house_ii_return_wit_1 := 
(
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (PaintHouseIIAnswer costs_l n_pre k_pre min1 ) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ”
  &&  (IntPtrArray2.full costs_pre n_pre costs_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  TT && emp 
|--
  “ (PaintHouseIIAnswer costs_l n_pre k_pre min1 ) ”
  &&  emp
).

Definition paint_house_ii_return_wit_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  (PaintHouseIIAnswer costs_l n_pre k_pre min1 )
.

Definition paint_house_ii_partial_solve_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH17 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH18 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH21 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= prev) ” 
  &&  “ (prev <= 1000000000) ” 
  &&  “ (0 <= (Znth c (Znth i costs_l __default__List_Z) 0)) ” 
  &&  “ ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c prev ) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (((row_ptr + (c * sizeof(INT)))) # Int  |-> (Znth c (Znth i costs_l __default__List_Z) 0))
  **  (IntArray.missing_i row_ptr c 0 (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
  **  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Module Type VC_Correct.

Include int_ptr_array2_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_paint_house_ii_safety_wit_1 : paint_house_ii_safety_wit_1.
Axiom proof_of_paint_house_ii_safety_wit_2 : paint_house_ii_safety_wit_2.
Axiom proof_of_paint_house_ii_safety_wit_3 : paint_house_ii_safety_wit_3.
Axiom proof_of_paint_house_ii_safety_wit_4 : paint_house_ii_safety_wit_4.
Axiom proof_of_paint_house_ii_safety_wit_5 : paint_house_ii_safety_wit_5.
Axiom proof_of_paint_house_ii_safety_wit_6 : paint_house_ii_safety_wit_6.
Axiom proof_of_paint_house_ii_safety_wit_7 : paint_house_ii_safety_wit_7.
Axiom proof_of_paint_house_ii_safety_wit_8 : paint_house_ii_safety_wit_8.
Axiom proof_of_paint_house_ii_safety_wit_9 : paint_house_ii_safety_wit_9.
Axiom proof_of_paint_house_ii_safety_wit_10 : paint_house_ii_safety_wit_10.
Axiom proof_of_paint_house_ii_safety_wit_11 : paint_house_ii_safety_wit_11.
Axiom proof_of_paint_house_ii_safety_wit_12 : paint_house_ii_safety_wit_12.
Axiom proof_of_paint_house_ii_safety_wit_13 : paint_house_ii_safety_wit_13.
Axiom proof_of_paint_house_ii_entail_wit_1 : paint_house_ii_entail_wit_1.
Axiom proof_of_paint_house_ii_entail_wit_2 : paint_house_ii_entail_wit_2.
Axiom proof_of_paint_house_ii_entail_wit_3 : paint_house_ii_entail_wit_3.
Axiom proof_of_paint_house_ii_entail_wit_4_1 : paint_house_ii_entail_wit_4_1.
Axiom proof_of_paint_house_ii_entail_wit_4_2 : paint_house_ii_entail_wit_4_2.
Axiom proof_of_paint_house_ii_entail_wit_5_1 : paint_house_ii_entail_wit_5_1.
Axiom proof_of_paint_house_ii_entail_wit_5_2 : paint_house_ii_entail_wit_5_2.
Axiom proof_of_paint_house_ii_entail_wit_5_3 : paint_house_ii_entail_wit_5_3.
Axiom proof_of_paint_house_ii_entail_wit_6 : paint_house_ii_entail_wit_6.
Axiom proof_of_paint_house_ii_entail_wit_7 : paint_house_ii_entail_wit_7.
Axiom proof_of_paint_house_ii_entail_wit_8 : paint_house_ii_entail_wit_8.
Axiom proof_of_paint_house_ii_entail_wit_9 : paint_house_ii_entail_wit_9.
Axiom proof_of_paint_house_ii_return_wit_1 : paint_house_ii_return_wit_1.
Axiom proof_of_paint_house_ii_partial_solve_wit_1 : paint_house_ii_partial_solve_wit_1.

End VC_Correct.
