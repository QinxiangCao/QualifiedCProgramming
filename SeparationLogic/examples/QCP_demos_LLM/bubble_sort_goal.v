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
Require Import SimpleC.EE.QCP_demos_LLM.bubble_sort_lib.
Local Open Scope sac.

(*----- Function bubble_sort -----*)

Definition bubble_sort_safety_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bubble_sort_safety_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n_pre - 1 ))) (PreH5 : (Permutation l a )) (PreH6 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH7 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition bubble_sort_safety_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (n_pre = 0)) (PreH2 : (i = 0)) (PreH3 : ((Zlength (l)) = n_pre)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition bubble_sort_safety_wit_4 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (n_pre = 0)) (PreH2 : (i = 0)) (PreH3 : ((Zlength (l)) = n_pre)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_safety_wit_5 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n_pre - 1 ))) (PreH5 : (Permutation l a )) (PreH6 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH7 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_safety_wit_6 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ False ”
.

Definition bubble_sort_safety_wit_7 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bubble_sort_safety_wit_8 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Zlength (a)) = n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < (n_pre - 1 ))) (PreH4 : (0 <= j)) (PreH5 : (j <= ((n_pre - 1 ) - i ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a )
|--
  “ (((n_pre - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre - 1 ) - i )) ”
.

Definition bubble_sort_safety_wit_9 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Zlength (a)) = n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < (n_pre - 1 ))) (PreH4 : (0 <= j)) (PreH5 : (j <= ((n_pre - 1 ) - i ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition bubble_sort_safety_wit_10 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Zlength (a)) = n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < (n_pre - 1 ))) (PreH4 : (0 <= j)) (PreH5 : (j <= ((n_pre - 1 ) - i ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_safety_wit_11 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH9 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_safety_wit_12 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH9 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_safety_wit_13 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Znth j a 0) > (Znth (j + 1 ) a 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_safety_wit_14 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Znth j a 0) > (Znth (j + 1 ) a 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_safety_wit_15 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Znth j a 0) > (Znth (j + 1 ) a 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) a 0)) (a)) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_safety_wit_16 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Znth j a 0) > (Znth (j + 1 ) a 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) a 0)) (a)) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_safety_wit_17 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Znth j a 0) > (Znth (j + 1 ) a 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre (replace_Znth ((j + 1 )) ((Znth j a 0)) ((replace_Znth (j) ((Znth (j + 1 ) a 0)) (a)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_safety_wit_18 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Znth j a 0) <= (Znth (j + 1 ) a 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_safety_wit_19 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH9 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition bubble_sort_entail_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) ,
  (IntArray.full arr_pre n_pre l )
|--
  (“ (n_pre = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full arr_pre n_pre l ))
  ||
  (EX (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - 0 )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - 0 ))) /\ ((n_pre - 0 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ”
  &&  (IntArray.full arr_pre n_pre a ))
.

Definition bubble_sort_entail_wit_2 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a_2: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a_2 )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH8 : forall (p_3: Z) , forall (q_2: Z) , (((((0 <= p_3) /\ (p_3 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  EX (a: (@list Z)) ,
  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < 0)) -> ((Znth (p_2) (a) (0)) <= (Znth (0) (a) (0)))) ”
  &&  (IntArray.full arr_pre n_pre a )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a_2: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a_2 )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH8 : forall (p_3: Z) , forall (q_2: Z) , (((((0 <= p_3) /\ (p_3 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) ,
  TT && emp 
|--
  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0)))) ”
  &&  emp
).

Definition bubble_sort_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a_2: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a_2 )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH8 : forall (p_3: Z) , forall (q_2: Z) , (((((0 <= p_3) /\ (p_3 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))
.

Definition bubble_sort_entail_wit_3_1 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  (IntArray.full arr_pre n_pre (replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)))) )
|--
  EX (a: (@list Z)) ,
  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < (j + 1 ))) -> ((Znth (p_2) (a) (0)) <= (Znth ((j + 1 )) (a) (0)))) ”
  &&  (IntArray.full arr_pre n_pre a )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  TT && emp 
|--
  “ (((Znth (0) ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2))))) (0))) /\ ((Znth (((j + 1 ) - 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2))))) (0)))) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)))))) ) ” 
  &&  “ (Permutation l (replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)))) ) ” 
  &&  “ ((Zlength ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)))))) = n_pre) ”
  &&  emp
).

Definition bubble_sort_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  (((Znth (0) ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2))))) (0))) /\ ((Znth (((j + 1 ) - 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2))))) (0))))
.

Definition bubble_sort_entail_wit_3_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  (increasing (sublist ((n_pre - i )) (n_pre) ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)))))) )
.

Definition bubble_sort_entail_wit_3_1_split_goal_3 := 
forall (n_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  (Permutation l (replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)))) )
.

Definition bubble_sort_entail_wit_3_1_split_goal_4 := 
forall (n_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  ((Zlength ((replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)))))) = n_pre)
.

Definition bubble_sort_entail_wit_3_2 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) <= (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  EX (a: (@list Z)) ,
  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < (j + 1 ))) -> ((Znth (p_2) (a) (0)) <= (Znth ((j + 1 )) (a) (0)))) ”
  &&  (IntArray.full arr_pre n_pre a )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) <= (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  TT && emp 
|--
  “ (((Znth (0) (a_2) (0)) <= (Znth ((j + 1 )) (a_2) (0))) /\ ((Znth (((j + 1 ) - 1 )) (a_2) (0)) <= (Znth ((j + 1 )) (a_2) (0)))) ”
  &&  emp
).

Definition bubble_sort_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) <= (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  (((Znth (0) (a_2) (0)) <= (Znth ((j + 1 )) (a_2) (0))) /\ ((Znth (((j + 1 ) - 1 )) (a_2) (0)) <= (Znth ((j + 1 )) (a_2) (0))))
.

Definition bubble_sort_entail_wit_4 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_2 )
|--
  EX (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - (i + 1 ) )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - (i + 1 ) ))) /\ ((n_pre - (i + 1 ) ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ”
  &&  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  TT && emp 
|--
  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - (i + 1 ) ))) /\ ((n_pre - (i + 1 ) ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0)))) ” 
  &&  “ (increasing (sublist ((n_pre - (i + 1 ) )) (n_pre) (a_2)) ) ”
  &&  emp
).

Definition bubble_sort_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - (i + 1 ) ))) /\ ((n_pre - (i + 1 ) ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))
.

Definition bubble_sort_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) ,
  (increasing (sublist ((n_pre - (i + 1 ) )) (n_pre) (a_2)) )
.

Definition bubble_sort_return_wit_1 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) ,
  TT && emp 
|--
  “ (increasing l ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition bubble_sort_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) ,
  (increasing l )
.

Definition bubble_sort_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) ,
  (Permutation l l )
.

Definition bubble_sort_return_wit_2 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) ,
  TT && emp 
|--
  “ (increasing a ) ”
  &&  emp
).

Definition bubble_sort_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) ,
  (increasing a )
.

Definition bubble_sort_partial_solve_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH9 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
|--
  “ (j < ((n_pre - 1 ) - i )) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0)))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j a 0))
  **  (IntArray.missing_i arr_pre j 0 n_pre a )
.

Definition bubble_sort_partial_solve_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH9 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
|--
  “ (j < ((n_pre - 1 ) - i )) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0)))) ”
  &&  (((arr_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth (j + 1 ) a 0))
  **  (IntArray.missing_i arr_pre (j + 1 ) 0 n_pre a )
.

Definition bubble_sort_partial_solve_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Znth j a 0) > (Znth (j + 1 ) a 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
|--
  “ ((Znth j a 0) > (Znth (j + 1 ) a 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i )) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0)))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j a 0))
  **  (IntArray.missing_i arr_pre j 0 n_pre a )
.

Definition bubble_sort_partial_solve_wit_4 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Znth j a 0) > (Znth (j + 1 ) a 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
|--
  “ ((Znth j a 0) > (Znth (j + 1 ) a 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i )) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0)))) ”
  &&  (((arr_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth (j + 1 ) a 0))
  **  (IntArray.missing_i arr_pre (j + 1 ) 0 n_pre a )
.

Definition bubble_sort_partial_solve_wit_5 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Znth j a 0) > (Znth (j + 1 ) a 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre a )
|--
  “ ((Znth j a 0) > (Znth (j + 1 ) a 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i )) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0)))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre j 0 n_pre a )
.

Definition bubble_sort_partial_solve_wit_6 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (a: (@list Z)) (PreH1 : ((Znth j a 0) > (Znth (j + 1 ) a 0))) (PreH2 : (j < ((n_pre - 1 ) - i ))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i ))) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0))))) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) a 0)) (a)) )
|--
  “ ((Znth j a 0) > (Znth (j + 1 ) a 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i )) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < j)) -> ((Znth (p_2) (a) (0)) <= (Znth (j) (a) (0)))) ”
  &&  (((arr_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre (j + 1 ) 0 n_pre (replace_Znth (j) ((Znth (j + 1 ) a 0)) (a)) )
.

(*----- Function bubble_sort_alter -----*)

Definition bubble_sort_alter_safety_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((False \/ (True /\ (n_pre = 0))) \/ (True /\ (n_pre > 0))) ”
.

Definition bubble_sort_alter_safety_wit_2_zero := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre = 0)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bubble_sort_alter_safety_wit_3_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bubble_sort_alter_safety_wit_4_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n_pre - 1 ))) (PreH5 : (Permutation l a )) (PreH6 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH7 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH8 : (n_pre >= 0)) (PreH9 : (n_pre <= 100000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition bubble_sort_alter_safety_wit_5_zero := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (n_pre = 0)) (PreH2 : (i = 0)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (n_pre = 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition bubble_sort_alter_safety_wit_6_zero := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (n_pre = 0)) (PreH2 : (i = 0)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (n_pre = 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter_safety_wit_7_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n_pre - 1 ))) (PreH5 : (Permutation l a )) (PreH6 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH7 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH8 : (n_pre >= 0)) (PreH9 : (n_pre <= 100000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter_safety_wit_8_zero := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ False ”
.

Definition bubble_sort_alter_safety_wit_9_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bubble_sort_alter_safety_wit_10_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i_2: Z) (a: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < (n_pre - 1 ))) (PreH4 : (0 <= j)) (PreH5 : (j <= ((n_pre - 1 ) - i ))) (PreH6 : (Permutation l a_2 )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH8 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH9 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH10 : (i_2 < (n_pre - 1 ))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : (0 <= i_2)) (PreH14 : (i_2 <= (n_pre - 1 ))) (PreH15 : (Permutation l a )) (PreH16 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a)) )) (PreH17 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH18 : (n_pre >= 0)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_2 )
|--
  “ (((n_pre - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre - 1 ) - i )) ”
.

Definition bubble_sort_alter_safety_wit_11_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 < (n_pre - 1 ))) (PreH4 : (0 <= j)) (PreH5 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH6 : (Permutation l a_2 )) (PreH7 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH8 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH9 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH10 : (i < (n_pre - 1 ))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (Permutation l a )) (PreH16 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH17 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH18 : (n_pre >= 0)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_2 )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition bubble_sort_alter_safety_wit_12_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 < (n_pre - 1 ))) (PreH4 : (0 <= j)) (PreH5 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH6 : (Permutation l a_2 )) (PreH7 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH8 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH9 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH10 : (i < (n_pre - 1 ))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (Permutation l a )) (PreH16 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH17 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH18 : (n_pre >= 0)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter_safety_wit_13_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i_2 ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH11 : (i < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (Permutation l a )) (PreH17 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_alter_safety_wit_14_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i_2 ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH11 : (i < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (Permutation l a )) (PreH17 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter_safety_wit_15_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a_2 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_alter_safety_wit_16_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a_2 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter_safety_wit_17_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a_2 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_alter_safety_wit_18_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a_2 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter_safety_wit_19_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre (replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_alter_safety_wit_20_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) <= (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_alter_safety_wit_21_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i_2: Z) (a: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH11 : (i_2 < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= (n_pre - 1 ))) (PreH16 : (Permutation l a )) (PreH17 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition bubble_sort_alter_entail_wit_1_zero := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre = 0)) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (n_pre = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre = 0) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition bubble_sort_alter_entail_wit_2_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - 0 )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - 0 ))) /\ ((n_pre - 0 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (IntArray.full arr_pre n_pre a )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  TT && emp 
|--
  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - 0 ))) /\ ((n_pre - 0 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (l) (0)) <= (Znth (q) (l) (0)))) ” 
  &&  “ (increasing (sublist ((n_pre - 0 )) (n_pre) (l)) ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition bubble_sort_alter_entail_wit_2_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - 0 ))) /\ ((n_pre - 0 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (l) (0)) <= (Znth (q) (l) (0))))
.

Definition bubble_sort_alter_entail_wit_2_normal_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  (increasing (sublist ((n_pre - 0 )) (n_pre) (l)) )
.

Definition bubble_sort_alter_entail_wit_2_normal_split_goal_3 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  (Permutation l l )
.

Definition bubble_sort_alter_entail_wit_3_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a )
|--
  EX (a_2: (@list Z)) ,
  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < 0)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (0) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (IntArray.full arr_pre n_pre a_2 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  TT && emp 
|--
  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a) (0)) <= (Znth (q_2) (a) (0)))) ”
  &&  emp
).

Definition bubble_sort_alter_entail_wit_3_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a) (0)) <= (Znth (q_2) (a) (0))))
.

Definition bubble_sort_alter_entail_wit_4_1_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre (replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))) )
|--
  EX (a_2: (@list Z)) ,
  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < (j + 1 ))) -> ((Znth (p_3) (a_2) (0)) <= (Znth ((j + 1 )) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (IntArray.full arr_pre n_pre a_2 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  TT && emp 
|--
  “ (((Znth (0) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0))) /\ ((Znth (((j + 1 ) - 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0)))) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))))) ) ” 
  &&  “ (Permutation l (replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))) ) ” 
  &&  “ ((Zlength ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))))) = n_pre) ”
  &&  emp
).

Definition bubble_sort_alter_entail_wit_4_1_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (((Znth (0) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0))) /\ ((Znth (((j + 1 ) - 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0))))
.

Definition bubble_sort_alter_entail_wit_4_1_normal_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (increasing (sublist ((n_pre - i_2 )) (n_pre) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))))) )
.

Definition bubble_sort_alter_entail_wit_4_1_normal_split_goal_3 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (Permutation l (replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))) )
.

Definition bubble_sort_alter_entail_wit_4_1_normal_split_goal_4 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  ((Zlength ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))))) = n_pre)
.

Definition bubble_sort_alter_entail_wit_4_2_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) <= (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_3 )
|--
  EX (a_2: (@list Z)) ,
  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < (j + 1 ))) -> ((Znth (p_3) (a_2) (0)) <= (Znth ((j + 1 )) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (IntArray.full arr_pre n_pre a_2 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) <= (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  TT && emp 
|--
  “ (((Znth (0) (a_3) (0)) <= (Znth ((j + 1 )) (a_3) (0))) /\ ((Znth (((j + 1 ) - 1 )) (a_3) (0)) <= (Znth ((j + 1 )) (a_3) (0)))) ”
  &&  emp
).

Definition bubble_sort_alter_entail_wit_4_2_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) <= (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (((Znth (0) (a_3) (0)) <= (Znth ((j + 1 )) (a_3) (0))) /\ ((Znth (((j + 1 ) - 1 )) (a_3) (0)) <= (Znth ((j + 1 )) (a_3) (0))))
.

Definition bubble_sort_alter_entail_wit_5_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i_2: Z) (a_2: (@list Z)) (j: Z) (i: Z) (a_3: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_3 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_3)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH11 : (i_2 < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= (n_pre - 1 ))) (PreH16 : (Permutation l a_2 )) (PreH17 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_3 )
|--
  EX (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - (i + 1 ) )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - (i + 1 ) ))) /\ ((n_pre - (i + 1 ) ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i_2: Z) (a_2: (@list Z)) (j: Z) (i: Z) (a_3: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_3 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_3)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH11 : (i_2 < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= (n_pre - 1 ))) (PreH16 : (Permutation l a_2 )) (PreH17 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  TT && emp 
|--
  “ (increasing (sublist ((n_pre - (i + 1 ) )) (n_pre) (a_3)) ) ”
  &&  emp
).

Definition bubble_sort_alter_entail_wit_5_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i_2: Z) (a_2: (@list Z)) (j: Z) (i: Z) (a_3: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_3 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_3)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH11 : (i_2 < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= (n_pre - 1 ))) (PreH16 : (Permutation l a_2 )) (PreH17 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  (increasing (sublist ((n_pre - (i + 1 ) )) (n_pre) (a_3)) )
.

Definition bubble_sort_alter_return_wit_1_zero := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = 0)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = 0)) ,
  TT && emp 
|--
  “ (increasing l ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition bubble_sort_alter_return_wit_1_zero_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = 0)) ,
  (increasing l )
.

Definition bubble_sort_alter_return_wit_1_zero_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = 0)) ,
  (Permutation l l )
.

Definition bubble_sort_alter_return_wit_2_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  TT && emp 
|--
  “ (increasing a ) ”
  &&  emp
).

Definition bubble_sort_alter_return_wit_2_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  (increasing a )
.

Definition bubble_sort_alter_partial_solve_wit_1_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i_2 ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH11 : (i < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (Permutation l a )) (PreH17 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j a_2 0))
  **  (IntArray.missing_i arr_pre j 0 n_pre a_2 )
.

Definition bubble_sort_alter_partial_solve_wit_2_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i_2 ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH11 : (i < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (Permutation l a )) (PreH17 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth (j + 1 ) a_2 0))
  **  (IntArray.missing_i arr_pre (j + 1 ) 0 n_pre a_2 )
.

Definition bubble_sort_alter_partial_solve_wit_3_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  “ ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j a_2 0))
  **  (IntArray.missing_i arr_pre j 0 n_pre a_2 )
.

Definition bubble_sort_alter_partial_solve_wit_4_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  “ ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth (j + 1 ) a_2 0))
  **  (IntArray.missing_i arr_pre (j + 1 ) 0 n_pre a_2 )
.

Definition bubble_sort_alter_partial_solve_wit_5_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  “ ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre j 0 n_pre a_2 )
.

Definition bubble_sort_alter_partial_solve_wit_6_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)) )
|--
  “ ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre (j + 1 ) 0 n_pre (replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)) )
.

(*----- Function bubble_sort_alter1 -----*)

Definition bubble_sort_alter1_safety_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((False \/ (True /\ (n_pre = 0))) \/ (True /\ (n_pre > 0))) ”
.

Definition bubble_sort_alter1_safety_wit_2_zero := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre = 0)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bubble_sort_alter1_safety_wit_3_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bubble_sort_alter1_safety_wit_4_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n_pre - 1 ))) (PreH5 : (Permutation l a )) (PreH6 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH7 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH8 : (n_pre >= 0)) (PreH9 : (n_pre <= 100000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition bubble_sort_alter1_safety_wit_5_zero := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (n_pre = 0)) (PreH2 : (i = 0)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (n_pre = 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition bubble_sort_alter1_safety_wit_6_zero := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (n_pre = 0)) (PreH2 : (i = 0)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (n_pre = 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter1_safety_wit_7_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n_pre - 1 ))) (PreH5 : (Permutation l a )) (PreH6 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH7 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH8 : (n_pre >= 0)) (PreH9 : (n_pre <= 100000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter1_safety_wit_8_zero := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ False ”
.

Definition bubble_sort_alter1_safety_wit_9_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bubble_sort_alter1_safety_wit_10_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i_2: Z) (a: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < (n_pre - 1 ))) (PreH4 : (0 <= j)) (PreH5 : (j <= ((n_pre - 1 ) - i ))) (PreH6 : (Permutation l a_2 )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH8 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH9 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH10 : (i_2 < (n_pre - 1 ))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : (0 <= i_2)) (PreH14 : (i_2 <= (n_pre - 1 ))) (PreH15 : (Permutation l a )) (PreH16 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a)) )) (PreH17 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH18 : (n_pre >= 0)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_2 )
|--
  “ (((n_pre - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre - 1 ) - i )) ”
.

Definition bubble_sort_alter1_safety_wit_11_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 < (n_pre - 1 ))) (PreH4 : (0 <= j)) (PreH5 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH6 : (Permutation l a_2 )) (PreH7 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH8 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH9 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH10 : (i < (n_pre - 1 ))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (Permutation l a )) (PreH16 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH17 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH18 : (n_pre >= 0)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_2 )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition bubble_sort_alter1_safety_wit_12_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 < (n_pre - 1 ))) (PreH4 : (0 <= j)) (PreH5 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH6 : (Permutation l a_2 )) (PreH7 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH8 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH9 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH10 : (i < (n_pre - 1 ))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (Permutation l a )) (PreH16 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH17 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH18 : (n_pre >= 0)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter1_safety_wit_13_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i_2 ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH11 : (i < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (Permutation l a )) (PreH17 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_alter1_safety_wit_14_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i_2 ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH11 : (i < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (Permutation l a )) (PreH17 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter1_safety_wit_15_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a_2 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_alter1_safety_wit_16_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a_2 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter1_safety_wit_17_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a_2 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_alter1_safety_wit_18_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j a_2 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bubble_sort_alter1_safety_wit_19_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre (replace_Znth ((j + 1 )) ((Znth j a_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_alter1_safety_wit_20_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) <= (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition bubble_sort_alter1_safety_wit_21_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i_2: Z) (a: (@list Z)) (j: Z) (i: Z) (a_2: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH11 : (i_2 < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= (n_pre - 1 ))) (PreH16 : (Permutation l a )) (PreH17 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition bubble_sort_alter1_entail_wit_1_zero := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre = 0)) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (n_pre = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre = 0) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition bubble_sort_alter1_entail_wit_2_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - 0 )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - 0 ))) /\ ((n_pre - 0 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (IntArray.full arr_pre n_pre a )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  TT && emp 
|--
  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - 0 ))) /\ ((n_pre - 0 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (l) (0)) <= (Znth (q) (l) (0)))) ” 
  &&  “ (increasing (sublist ((n_pre - 0 )) (n_pre) (l)) ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition bubble_sort_alter1_entail_wit_2_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - 0 ))) /\ ((n_pre - 0 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (l) (0)) <= (Znth (q) (l) (0))))
.

Definition bubble_sort_alter1_entail_wit_2_normal_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  (increasing (sublist ((n_pre - 0 )) (n_pre) (l)) )
.

Definition bubble_sort_alter1_entail_wit_2_normal_split_goal_3 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > 0)) ,
  (Permutation l l )
.

Definition bubble_sort_alter1_entail_wit_3_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a )
|--
  EX (a_2: (@list Z)) ,
  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - 1 ) - i )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < 0)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (0) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (IntArray.full arr_pre n_pre a_2 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  TT && emp 
|--
  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a) (0)) <= (Znth (q_2) (a) (0)))) ”
  &&  emp
).

Definition bubble_sort_alter1_entail_wit_3_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a) (0)) <= (Znth (q_2) (a) (0))))
.

Definition bubble_sort_alter1_entail_wit_4_1_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre (replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))) )
|--
  EX (a_2: (@list Z)) ,
  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < (j + 1 ))) -> ((Znth (p_3) (a_2) (0)) <= (Znth ((j + 1 )) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (IntArray.full arr_pre n_pre a_2 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  TT && emp 
|--
  “ (((Znth (0) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0))) /\ ((Znth (((j + 1 ) - 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0)))) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))))) ) ” 
  &&  “ (Permutation l (replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))) ) ” 
  &&  “ ((Zlength ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))))) = n_pre) ”
  &&  emp
).

Definition bubble_sort_alter1_entail_wit_4_1_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (((Znth (0) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0))) /\ ((Znth (((j + 1 ) - 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0)) <= (Znth ((j + 1 )) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3))))) (0))))
.

Definition bubble_sort_alter1_entail_wit_4_1_normal_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (increasing (sublist ((n_pre - i_2 )) (n_pre) ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))))) )
.

Definition bubble_sort_alter1_entail_wit_4_1_normal_split_goal_3 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (Permutation l (replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))) )
.

Definition bubble_sort_alter1_entail_wit_4_1_normal_split_goal_4 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) > (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  ((Zlength ((replace_Znth ((j + 1 )) ((Znth j a_3 0)) ((replace_Znth (j) ((Znth (j + 1 ) a_3 0)) (a_3)))))) = n_pre)
.

Definition bubble_sort_alter1_entail_wit_4_2_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) <= (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_3 )
|--
  EX (a_2: (@list Z)) ,
  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < (j + 1 ))) -> ((Znth (p_3) (a_2) (0)) <= (Znth ((j + 1 )) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (IntArray.full arr_pre n_pre a_2 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) <= (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  TT && emp 
|--
  “ (((Znth (0) (a_3) (0)) <= (Znth ((j + 1 )) (a_3) (0))) /\ ((Znth (((j + 1 ) - 1 )) (a_3) (0)) <= (Znth ((j + 1 )) (a_3) (0)))) ”
  &&  emp
).

Definition bubble_sort_alter1_entail_wit_4_2_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_3: (@list Z)) (PreH1 : ((Znth j a_3 0) <= (Znth (j + 1 ) a_3 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_3 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_3)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (((Znth (0) (a_3) (0)) <= (Znth ((j + 1 )) (a_3) (0))) /\ ((Znth (((j + 1 ) - 1 )) (a_3) (0)) <= (Znth ((j + 1 )) (a_3) (0))))
.

Definition bubble_sort_alter1_entail_wit_5_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i_2: Z) (a_2: (@list Z)) (j: Z) (i: Z) (a_3: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_3 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_3)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH11 : (i_2 < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= (n_pre - 1 ))) (PreH16 : (Permutation l a_2 )) (PreH17 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre a_3 )
|--
  EX (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - (i + 1 ) )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - (i + 1 ) ))) /\ ((n_pre - (i + 1 ) ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (IntArray.full arr_pre n_pre a )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i_2: Z) (a_2: (@list Z)) (j: Z) (i: Z) (a_3: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_3 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_3)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH11 : (i_2 < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= (n_pre - 1 ))) (PreH16 : (Permutation l a_2 )) (PreH17 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  TT && emp 
|--
  “ (increasing (sublist ((n_pre - (i + 1 ) )) (n_pre) (a_3)) ) ”
  &&  emp
).

Definition bubble_sort_alter1_entail_wit_5_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i_2: Z) (a_2: (@list Z)) (j: Z) (i: Z) (a_3: (@list Z)) (PreH1 : (j >= ((n_pre - 1 ) - i ))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i ))) (PreH7 : (Permutation l a_3 )) (PreH8 : (increasing (sublist ((n_pre - i )) (n_pre) (a_3)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i ))) /\ ((n_pre - i ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) (0)) <= (Znth (q_2) (a_3) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_3) (0)) <= (Znth (j) (a_3) (0))))) (PreH11 : (i_2 < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= (n_pre - 1 ))) (PreH16 : (Permutation l a_2 )) (PreH17 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a_2) (0)) <= (Znth (q) (a_2) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  (increasing (sublist ((n_pre - (i + 1 ) )) (n_pre) (a_3)) )
.

Definition bubble_sort_alter1_return_wit_1_zero := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = 0)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = 0)) ,
  TT && emp 
|--
  “ (increasing l ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition bubble_sort_alter1_return_wit_1_zero_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = 0)) ,
  (increasing l )
.

Definition bubble_sort_alter1_return_wit_1_zero_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (n_pre = 0)) (PreH3 : (i = 0)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = 0)) ,
  (Permutation l l )
.

Definition bubble_sort_alter1_return_wit_2_normal := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  TT && emp 
|--
  “ (increasing a ) ”
  &&  emp
).

Definition bubble_sort_alter1_return_wit_2_normal_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH9 : (n_pre >= 0)) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > 0)) ,
  (increasing a )
.

Definition bubble_sort_alter1_partial_solve_wit_1_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i_2 ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH11 : (i < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (Permutation l a )) (PreH17 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j a_2 0))
  **  (IntArray.missing_i arr_pre j 0 n_pre a_2 )
.

Definition bubble_sort_alter1_partial_solve_wit_2_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : (j < ((n_pre - 1 ) - i_2 ))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < (n_pre - 1 ))) (PreH5 : (0 <= j)) (PreH6 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH10 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH11 : (i < (n_pre - 1 ))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= (n_pre - 1 ))) (PreH16 : (Permutation l a )) (PreH17 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH19 : (n_pre >= 0)) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth (j + 1 ) a_2 0))
  **  (IntArray.missing_i arr_pre (j + 1 ) 0 n_pre a_2 )
.

Definition bubble_sort_alter1_partial_solve_wit_3_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  “ ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j a_2 0))
  **  (IntArray.missing_i arr_pre j 0 n_pre a_2 )
.

Definition bubble_sort_alter1_partial_solve_wit_4_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  “ ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth (j + 1 ) a_2 0))
  **  (IntArray.missing_i arr_pre (j + 1 ) 0 n_pre a_2 )
.

Definition bubble_sort_alter1_partial_solve_wit_5_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre a_2 )
|--
  “ ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre j 0 n_pre a_2 )
.

Definition bubble_sort_alter1_partial_solve_wit_6_normal := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (a: (@list Z)) (j: Z) (i_2: Z) (a_2: (@list Z)) (PreH1 : ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0))) (PreH2 : (j < ((n_pre - 1 ) - i_2 ))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < (n_pre - 1 ))) (PreH6 : (0 <= j)) (PreH7 : (j <= ((n_pre - 1 ) - i_2 ))) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0))))) (PreH11 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0))))) (PreH12 : (i < (n_pre - 1 ))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= (n_pre - 1 ))) (PreH17 : (Permutation l a )) (PreH18 : (increasing (sublist ((n_pre - i )) (n_pre) (a)) )) (PreH19 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0))))) (PreH20 : (n_pre >= 0)) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > 0)) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)) )
|--
  “ ((Znth j a_2 0) > (Znth (j + 1 ) a_2 0)) ” 
  &&  “ (j < ((n_pre - 1 ) - i_2 )) ” 
  &&  “ ((Zlength (a_2)) = n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - i_2 )) ” 
  &&  “ (Permutation l a_2 ) ” 
  &&  “ (increasing (sublist ((n_pre - i_2 )) (n_pre) (a_2)) ) ” 
  &&  “ forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < (n_pre - i_2 ))) /\ ((n_pre - i_2 ) <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) (0)) <= (Znth (q_2) (a_2) (0)))) ” 
  &&  “ forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < j)) -> ((Znth (p_3) (a_2) (0)) <= (Znth (j) (a_2) (0)))) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (a)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist ((n_pre - i )) (n_pre) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (n_pre - i ))) /\ ((n_pre - i ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (a) (0)) <= (Znth (q) (a) (0)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (n_pre > 0) ”
  &&  (((arr_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre (j + 1 ) 0 n_pre (replace_Znth (j) ((Znth (j + 1 ) a_2 0)) (a_2)) )
.

Module Type VC_Correct.


Axiom proof_of_bubble_sort_safety_wit_1 : bubble_sort_safety_wit_1.
Axiom proof_of_bubble_sort_safety_wit_2 : bubble_sort_safety_wit_2.
Axiom proof_of_bubble_sort_safety_wit_3 : bubble_sort_safety_wit_3.
Axiom proof_of_bubble_sort_safety_wit_4 : bubble_sort_safety_wit_4.
Axiom proof_of_bubble_sort_safety_wit_5 : bubble_sort_safety_wit_5.
Axiom proof_of_bubble_sort_safety_wit_6 : bubble_sort_safety_wit_6.
Axiom proof_of_bubble_sort_safety_wit_7 : bubble_sort_safety_wit_7.
Axiom proof_of_bubble_sort_safety_wit_8 : bubble_sort_safety_wit_8.
Axiom proof_of_bubble_sort_safety_wit_9 : bubble_sort_safety_wit_9.
Axiom proof_of_bubble_sort_safety_wit_10 : bubble_sort_safety_wit_10.
Axiom proof_of_bubble_sort_safety_wit_11 : bubble_sort_safety_wit_11.
Axiom proof_of_bubble_sort_safety_wit_12 : bubble_sort_safety_wit_12.
Axiom proof_of_bubble_sort_safety_wit_13 : bubble_sort_safety_wit_13.
Axiom proof_of_bubble_sort_safety_wit_14 : bubble_sort_safety_wit_14.
Axiom proof_of_bubble_sort_safety_wit_15 : bubble_sort_safety_wit_15.
Axiom proof_of_bubble_sort_safety_wit_16 : bubble_sort_safety_wit_16.
Axiom proof_of_bubble_sort_safety_wit_17 : bubble_sort_safety_wit_17.
Axiom proof_of_bubble_sort_safety_wit_18 : bubble_sort_safety_wit_18.
Axiom proof_of_bubble_sort_safety_wit_19 : bubble_sort_safety_wit_19.
Axiom proof_of_bubble_sort_entail_wit_1 : bubble_sort_entail_wit_1.
Axiom proof_of_bubble_sort_entail_wit_2 : bubble_sort_entail_wit_2.
Axiom proof_of_bubble_sort_entail_wit_3_1 : bubble_sort_entail_wit_3_1.
Axiom proof_of_bubble_sort_entail_wit_3_2 : bubble_sort_entail_wit_3_2.
Axiom proof_of_bubble_sort_entail_wit_4 : bubble_sort_entail_wit_4.
Axiom proof_of_bubble_sort_return_wit_1 : bubble_sort_return_wit_1.
Axiom proof_of_bubble_sort_return_wit_2 : bubble_sort_return_wit_2.
Axiom proof_of_bubble_sort_partial_solve_wit_1 : bubble_sort_partial_solve_wit_1.
Axiom proof_of_bubble_sort_partial_solve_wit_2 : bubble_sort_partial_solve_wit_2.
Axiom proof_of_bubble_sort_partial_solve_wit_3 : bubble_sort_partial_solve_wit_3.
Axiom proof_of_bubble_sort_partial_solve_wit_4 : bubble_sort_partial_solve_wit_4.
Axiom proof_of_bubble_sort_partial_solve_wit_5 : bubble_sort_partial_solve_wit_5.
Axiom proof_of_bubble_sort_partial_solve_wit_6 : bubble_sort_partial_solve_wit_6.
Axiom proof_of_bubble_sort_alter_safety_wit_1 : bubble_sort_alter_safety_wit_1.
Axiom proof_of_bubble_sort_alter_safety_wit_2_zero : bubble_sort_alter_safety_wit_2_zero.
Axiom proof_of_bubble_sort_alter_safety_wit_3_normal : bubble_sort_alter_safety_wit_3_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_4_normal : bubble_sort_alter_safety_wit_4_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_5_zero : bubble_sort_alter_safety_wit_5_zero.
Axiom proof_of_bubble_sort_alter_safety_wit_6_zero : bubble_sort_alter_safety_wit_6_zero.
Axiom proof_of_bubble_sort_alter_safety_wit_7_normal : bubble_sort_alter_safety_wit_7_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_8_zero : bubble_sort_alter_safety_wit_8_zero.
Axiom proof_of_bubble_sort_alter_safety_wit_9_normal : bubble_sort_alter_safety_wit_9_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_10_normal : bubble_sort_alter_safety_wit_10_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_11_normal : bubble_sort_alter_safety_wit_11_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_12_normal : bubble_sort_alter_safety_wit_12_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_13_normal : bubble_sort_alter_safety_wit_13_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_14_normal : bubble_sort_alter_safety_wit_14_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_15_normal : bubble_sort_alter_safety_wit_15_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_16_normal : bubble_sort_alter_safety_wit_16_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_17_normal : bubble_sort_alter_safety_wit_17_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_18_normal : bubble_sort_alter_safety_wit_18_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_19_normal : bubble_sort_alter_safety_wit_19_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_20_normal : bubble_sort_alter_safety_wit_20_normal.
Axiom proof_of_bubble_sort_alter_safety_wit_21_normal : bubble_sort_alter_safety_wit_21_normal.
Axiom proof_of_bubble_sort_alter_entail_wit_1_zero : bubble_sort_alter_entail_wit_1_zero.
Axiom proof_of_bubble_sort_alter_entail_wit_2_normal : bubble_sort_alter_entail_wit_2_normal.
Axiom proof_of_bubble_sort_alter_entail_wit_3_normal : bubble_sort_alter_entail_wit_3_normal.
Axiom proof_of_bubble_sort_alter_entail_wit_4_1_normal : bubble_sort_alter_entail_wit_4_1_normal.
Axiom proof_of_bubble_sort_alter_entail_wit_4_2_normal : bubble_sort_alter_entail_wit_4_2_normal.
Axiom proof_of_bubble_sort_alter_entail_wit_5_normal : bubble_sort_alter_entail_wit_5_normal.
Axiom proof_of_bubble_sort_alter_return_wit_1_zero : bubble_sort_alter_return_wit_1_zero.
Axiom proof_of_bubble_sort_alter_return_wit_2_normal : bubble_sort_alter_return_wit_2_normal.
Axiom proof_of_bubble_sort_alter_partial_solve_wit_1_normal : bubble_sort_alter_partial_solve_wit_1_normal.
Axiom proof_of_bubble_sort_alter_partial_solve_wit_2_normal : bubble_sort_alter_partial_solve_wit_2_normal.
Axiom proof_of_bubble_sort_alter_partial_solve_wit_3_normal : bubble_sort_alter_partial_solve_wit_3_normal.
Axiom proof_of_bubble_sort_alter_partial_solve_wit_4_normal : bubble_sort_alter_partial_solve_wit_4_normal.
Axiom proof_of_bubble_sort_alter_partial_solve_wit_5_normal : bubble_sort_alter_partial_solve_wit_5_normal.
Axiom proof_of_bubble_sort_alter_partial_solve_wit_6_normal : bubble_sort_alter_partial_solve_wit_6_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_1 : bubble_sort_alter1_safety_wit_1.
Axiom proof_of_bubble_sort_alter1_safety_wit_2_zero : bubble_sort_alter1_safety_wit_2_zero.
Axiom proof_of_bubble_sort_alter1_safety_wit_3_normal : bubble_sort_alter1_safety_wit_3_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_4_normal : bubble_sort_alter1_safety_wit_4_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_5_zero : bubble_sort_alter1_safety_wit_5_zero.
Axiom proof_of_bubble_sort_alter1_safety_wit_6_zero : bubble_sort_alter1_safety_wit_6_zero.
Axiom proof_of_bubble_sort_alter1_safety_wit_7_normal : bubble_sort_alter1_safety_wit_7_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_8_zero : bubble_sort_alter1_safety_wit_8_zero.
Axiom proof_of_bubble_sort_alter1_safety_wit_9_normal : bubble_sort_alter1_safety_wit_9_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_10_normal : bubble_sort_alter1_safety_wit_10_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_11_normal : bubble_sort_alter1_safety_wit_11_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_12_normal : bubble_sort_alter1_safety_wit_12_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_13_normal : bubble_sort_alter1_safety_wit_13_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_14_normal : bubble_sort_alter1_safety_wit_14_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_15_normal : bubble_sort_alter1_safety_wit_15_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_16_normal : bubble_sort_alter1_safety_wit_16_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_17_normal : bubble_sort_alter1_safety_wit_17_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_18_normal : bubble_sort_alter1_safety_wit_18_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_19_normal : bubble_sort_alter1_safety_wit_19_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_20_normal : bubble_sort_alter1_safety_wit_20_normal.
Axiom proof_of_bubble_sort_alter1_safety_wit_21_normal : bubble_sort_alter1_safety_wit_21_normal.
Axiom proof_of_bubble_sort_alter1_entail_wit_1_zero : bubble_sort_alter1_entail_wit_1_zero.
Axiom proof_of_bubble_sort_alter1_entail_wit_2_normal : bubble_sort_alter1_entail_wit_2_normal.
Axiom proof_of_bubble_sort_alter1_entail_wit_3_normal : bubble_sort_alter1_entail_wit_3_normal.
Axiom proof_of_bubble_sort_alter1_entail_wit_4_1_normal : bubble_sort_alter1_entail_wit_4_1_normal.
Axiom proof_of_bubble_sort_alter1_entail_wit_4_2_normal : bubble_sort_alter1_entail_wit_4_2_normal.
Axiom proof_of_bubble_sort_alter1_entail_wit_5_normal : bubble_sort_alter1_entail_wit_5_normal.
Axiom proof_of_bubble_sort_alter1_return_wit_1_zero : bubble_sort_alter1_return_wit_1_zero.
Axiom proof_of_bubble_sort_alter1_return_wit_2_normal : bubble_sort_alter1_return_wit_2_normal.
Axiom proof_of_bubble_sort_alter1_partial_solve_wit_1_normal : bubble_sort_alter1_partial_solve_wit_1_normal.
Axiom proof_of_bubble_sort_alter1_partial_solve_wit_2_normal : bubble_sort_alter1_partial_solve_wit_2_normal.
Axiom proof_of_bubble_sort_alter1_partial_solve_wit_3_normal : bubble_sort_alter1_partial_solve_wit_3_normal.
Axiom proof_of_bubble_sort_alter1_partial_solve_wit_4_normal : bubble_sort_alter1_partial_solve_wit_4_normal.
Axiom proof_of_bubble_sort_alter1_partial_solve_wit_5_normal : bubble_sort_alter1_partial_solve_wit_5_normal.
Axiom proof_of_bubble_sort_alter1_partial_solve_wit_6_normal : bubble_sort_alter1_partial_solve_wit_6_normal.

End VC_Correct.
