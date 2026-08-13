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

(*----- Function sortArray -----*)

Definition sortArray_safety_wit_1 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sortArray_safety_wit_2 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist (0) (i) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre a )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sortArray_safety_wit_3 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist (0) (i) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre a )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_4 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j a 0) < (Znth i a 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a )) (PreH10 : (increasing (sublist (0) (i) (a)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) (PreH12 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0)))) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth i a 0)) ((replace_Znth (i) ((Znth j a 0)) (a)))) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sortArray_safety_wit_5 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j a 0) >= (Znth i a 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a )) (PreH10 : (increasing (sublist (0) (i) (a)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) (PreH12 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0)))) ,
  (IntArray.full nums_pre numsSize_pre a )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sortArray_safety_wit_6 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : ((i + 1 ) <= j)) (PreH7 : (j <= numsSize_pre)) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist (0) (i) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) (PreH11 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre a )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sortArray_entail_wit_1 := 
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) ,
  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (a: (@list Z))  (i: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre a )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  TT && emp 
|--
  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < 0)) /\ (0 <= q)) /\ (q < numsSize_pre)) -> ((Znth p l 0) <= (Znth q l 0))) ” 
  &&  “ (increasing (sublist (0) (0) (l)) ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition sortArray_entail_wit_1_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < 0)) /\ (0 <= q)) /\ (q < numsSize_pre)) -> ((Znth p l 0) <= (Znth q l 0)))
.

Definition sortArray_entail_wit_1_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  (increasing (sublist (0) (0) (l)) )
.

Definition sortArray_entail_wit_1_split_goal_3 := 
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  (Permutation l l )
.

Definition sortArray_entail_wit_2 := 
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= numsSize_pre)) (PreH6 : (Permutation l a_2 )) (PreH7 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH8 : forall (p_2: Z) , forall (q_3: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_3)) /\ (q_3 < numsSize_pre)) -> ((Znth p_2 a_2 0) <= (Znth q_3 a_2 0)))) ,
  ((( &( "j" ) )) # Int  |-> (i_2 + 1 ))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  (IntArray.full nums_pre numsSize_pre a_2 )
|--
  EX (a: (@list Z))  (j: Z)  (i: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0))) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full nums_pre numsSize_pre a )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (i_2: Z) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (i_2 < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= numsSize_pre)) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_3: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_3)) /\ (q_3 < numsSize_pre)) -> ((Znth p_2 a_2 0) <= (Znth q_3 a_2 0)))) ,
  TT && emp 
|--
  “ forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < (i_2 + 1 ))) -> ((Znth i_2 a_2 0) <= (Znth q_2 a_2 0))) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < numsSize_pre)) -> ((Znth p a_2 0) <= (Znth q a_2 0))) ”
  &&  emp
).

Definition sortArray_entail_wit_2_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (i_2: Z) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (i_2 < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= numsSize_pre)) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_3: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_3)) /\ (q_3 < numsSize_pre)) -> ((Znth p_2 a_2 0) <= (Znth q_3 a_2 0)))) ,
  forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < (i_2 + 1 ))) -> ((Znth i_2 a_2 0) <= (Znth q_2 a_2 0)))
.

Definition sortArray_entail_wit_2_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (i_2: Z) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (i_2 < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= numsSize_pre)) (PreH7 : (Permutation l a_2 )) (PreH8 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH9 : forall (p_2: Z) , forall (q_3: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_3)) /\ (q_3 < numsSize_pre)) -> ((Znth p_2 a_2 0) <= (Znth q_3 a_2 0)))) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < numsSize_pre)) -> ((Znth p a_2 0) <= (Znth q a_2 0)))
.

Definition sortArray_entail_wit_3_1 := 
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (j_2: Z) (i_2: Z) (PreH1 : ((Znth j_2 a_2 0) < (Znth i_2 a_2 0))) (PreH2 : (j_2 < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 < numsSize_pre)) (PreH7 : ((i_2 + 1 ) <= j_2)) (PreH8 : (j_2 <= numsSize_pre)) (PreH9 : (Permutation l a_2 )) (PreH10 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < numsSize_pre)) -> ((Znth p a_2 0) <= (Znth q a_2 0)))) (PreH12 : forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < j_2)) -> ((Znth i_2 a_2 0) <= (Znth q_2 a_2 0)))) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth (j_2) ((Znth i_2 a_2 0)) ((replace_Znth (i_2) ((Znth j_2 a_2 0)) (a_2)))) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
|--
  EX (a: (@list Z))  (j: Z)  (i: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0))) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full nums_pre numsSize_pre a )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (j_2: Z) (i_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 a_2 0)) ((replace_Znth (i_2) ((Znth j_2 a_2 0)) (a_2)))))) = numsSize_pre)) (PreH2 : ((Znth j_2 a_2 0) < (Znth i_2 a_2 0))) (PreH3 : (j_2 < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 < numsSize_pre)) (PreH8 : ((i_2 + 1 ) <= j_2)) (PreH9 : (j_2 <= numsSize_pre)) (PreH10 : (Permutation l a_2 )) (PreH11 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH12 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < numsSize_pre)) -> ((Znth p a_2 0) <= (Znth q a_2 0)))) (PreH13 : forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < j_2)) -> ((Znth i_2 a_2 0) <= (Znth q_2 a_2 0)))) ,
  TT && emp 
|--
  “ (increasing (sublist (0) (i_2) ((replace_Znth (j_2) ((Znth i_2 a_2 0)) ((replace_Znth (i_2) ((Znth j_2 a_2 0)) (a_2)))))) ) ” 
  &&  “ (Permutation l (replace_Znth (j_2) ((Znth i_2 a_2 0)) ((replace_Znth (i_2) ((Znth j_2 a_2 0)) (a_2)))) ) ”
  &&  emp
).

Definition sortArray_entail_wit_3_1_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (j_2: Z) (i_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 a_2 0)) ((replace_Znth (i_2) ((Znth j_2 a_2 0)) (a_2)))))) = numsSize_pre)) (PreH2 : ((Znth j_2 a_2 0) < (Znth i_2 a_2 0))) (PreH3 : (j_2 < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 < numsSize_pre)) (PreH8 : ((i_2 + 1 ) <= j_2)) (PreH9 : (j_2 <= numsSize_pre)) (PreH10 : (Permutation l a_2 )) (PreH11 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH12 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < numsSize_pre)) -> ((Znth p a_2 0) <= (Znth q a_2 0)))) (PreH13 : forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < j_2)) -> ((Znth i_2 a_2 0) <= (Znth q_2 a_2 0)))) ,
  (increasing (sublist (0) (i_2) ((replace_Znth (j_2) ((Znth i_2 a_2 0)) ((replace_Znth (i_2) ((Znth j_2 a_2 0)) (a_2)))))) )
.

Definition sortArray_entail_wit_3_1_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (j_2: Z) (i_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 a_2 0)) ((replace_Znth (i_2) ((Znth j_2 a_2 0)) (a_2)))))) = numsSize_pre)) (PreH2 : ((Znth j_2 a_2 0) < (Znth i_2 a_2 0))) (PreH3 : (j_2 < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 < numsSize_pre)) (PreH8 : ((i_2 + 1 ) <= j_2)) (PreH9 : (j_2 <= numsSize_pre)) (PreH10 : (Permutation l a_2 )) (PreH11 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH12 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < numsSize_pre)) -> ((Znth p a_2 0) <= (Znth q a_2 0)))) (PreH13 : forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < j_2)) -> ((Znth i_2 a_2 0) <= (Znth q_2 a_2 0)))) ,
  (Permutation l (replace_Znth (j_2) ((Znth i_2 a_2 0)) ((replace_Znth (i_2) ((Znth j_2 a_2 0)) (a_2)))) )
.

Definition sortArray_entail_wit_3_2 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (j_2: Z) (i_2: Z) (PreH1 : ((Znth j_2 a_2 0) >= (Znth i_2 a_2 0))) (PreH2 : (j_2 < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 < numsSize_pre)) (PreH7 : ((i_2 + 1 ) <= j_2)) (PreH8 : (j_2 <= numsSize_pre)) (PreH9 : (Permutation l a_2 )) (PreH10 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < numsSize_pre)) -> ((Znth p a_2 0) <= (Znth q a_2 0)))) (PreH12 : forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < j_2)) -> ((Znth i_2 a_2 0) <= (Znth q_2 a_2 0)))) ,
  (IntArray.full nums_pre numsSize_pre a_2 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
|--
  EX (a: (@list Z))  (j: Z)  (i: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0))) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full nums_pre numsSize_pre a )
.

Definition sortArray_entail_wit_4 := 
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (j: Z) (i_2: Z) (PreH1 : (j >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < numsSize_pre)) (PreH6 : ((i_2 + 1 ) <= j)) (PreH7 : (j <= numsSize_pre)) (PreH8 : (Permutation l a_2 )) (PreH9 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH10 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 0) <= (Znth q_2 a_2 0)))) (PreH11 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth i_2 a_2 0) <= (Znth q_3 a_2 0)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
  **  (IntArray.full nums_pre numsSize_pre a_2 )
|--
  EX (a: (@list Z))  (i: Z) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ”
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre a )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (j: Z) (i_2: Z) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (j >= numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 < numsSize_pre)) (PreH7 : ((i_2 + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a_2 )) (PreH10 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH11 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 0) <= (Znth q_2 a_2 0)))) (PreH12 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth i_2 a_2 0) <= (Znth q_3 a_2 0)))) ,
  TT && emp 
|--
  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (i_2 + 1 ))) /\ ((i_2 + 1 ) <= q)) /\ (q < numsSize_pre)) -> ((Znth p a_2 0) <= (Znth q a_2 0))) ” 
  &&  “ (increasing (sublist (0) ((i_2 + 1 )) (a_2)) ) ”
  &&  emp
).

Definition sortArray_entail_wit_4_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (j: Z) (i_2: Z) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (j >= numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 < numsSize_pre)) (PreH7 : ((i_2 + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a_2 )) (PreH10 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH11 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 0) <= (Znth q_2 a_2 0)))) (PreH12 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth i_2 a_2 0) <= (Znth q_3 a_2 0)))) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (i_2 + 1 ))) /\ ((i_2 + 1 ) <= q)) /\ (q < numsSize_pre)) -> ((Znth p a_2 0) <= (Znth q a_2 0)))
.

Definition sortArray_entail_wit_4_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (a_2: (@list Z)) (j: Z) (i_2: Z) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (j >= numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 < numsSize_pre)) (PreH7 : ((i_2 + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a_2 )) (PreH10 : (increasing (sublist (0) (i_2) (a_2)) )) (PreH11 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 0) <= (Znth q_2 a_2 0)))) (PreH12 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth i_2 a_2 0) <= (Znth q_3 a_2 0)))) ,
  (increasing (sublist (0) ((i_2 + 1 )) (a_2)) )
.

Definition sortArray_return_wit_1 := 
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (Permutation l a )) (PreH7 : (increasing (sublist (0) (i) (a)) )) (PreH8 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) ,
  (IntArray.full nums_pre numsSize_pre a )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l1 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : ((Zlength (a)) = numsSize_pre)) (PreH2 : (i >= numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (Permutation l a )) (PreH8 : (increasing (sublist (0) (i) (a)) )) (PreH9 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) ,
  TT && emp 
|--
  “ (increasing a ) ”
  &&  emp
).

Definition sortArray_return_wit_1_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : ((Zlength (a)) = numsSize_pre)) (PreH2 : (i >= numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (Permutation l a )) (PreH8 : (increasing (sublist (0) (i) (a)) )) (PreH9 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) ,
  (increasing a )
.

Definition sortArray_partial_solve_wit_1 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : ((i + 1 ) <= j)) (PreH7 : (j <= numsSize_pre)) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist (0) (i) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) (PreH11 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0)))) ,
  (IntArray.full nums_pre numsSize_pre a )
|--
  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0))) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j a 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre a )
.

Definition sortArray_partial_solve_wit_2 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : ((i + 1 ) <= j)) (PreH7 : (j <= numsSize_pre)) (PreH8 : (Permutation l a )) (PreH9 : (increasing (sublist (0) (i) (a)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) (PreH11 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0)))) ,
  (IntArray.full nums_pre numsSize_pre a )
|--
  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i a 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre a )
.

Definition sortArray_partial_solve_wit_3 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j a 0) < (Znth i a 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a )) (PreH10 : (increasing (sublist (0) (i) (a)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) (PreH12 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0)))) ,
  (IntArray.full nums_pre numsSize_pre a )
|--
  “ ((Znth j a 0) < (Znth i a 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i a 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre a )
.

Definition sortArray_partial_solve_wit_4 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j a 0) < (Znth i a 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a )) (PreH10 : (increasing (sublist (0) (i) (a)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) (PreH12 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0)))) ,
  (IntArray.full nums_pre numsSize_pre a )
|--
  “ ((Znth j a 0) < (Znth i a 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0))) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j a 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre a )
.

Definition sortArray_partial_solve_wit_5 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j a 0) < (Znth i a 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a )) (PreH10 : (increasing (sublist (0) (i) (a)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) (PreH12 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0)))) ,
  (IntArray.full nums_pre numsSize_pre a )
|--
  “ ((Znth j a 0) < (Znth i a 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre a )
.

Definition sortArray_partial_solve_wit_6 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (a: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j a 0) < (Znth i a 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a )) (PreH10 : (increasing (sublist (0) (i) (a)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0)))) (PreH12 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0)))) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth (i) ((Znth j a 0)) (a)) )
|--
  “ ((Znth j a 0) < (Znth i a 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l a ) ” 
  &&  “ (increasing (sublist (0) (i) (a)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < numsSize_pre)) -> ((Znth p a 0) <= (Znth q a 0))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth i a 0) <= (Znth q_2 a 0))) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre (replace_Znth (i) ((Znth j a 0)) (a)) )
.

Module Type VC_Correct.


Axiom proof_of_sortArray_safety_wit_1 : sortArray_safety_wit_1.
Axiom proof_of_sortArray_safety_wit_2 : sortArray_safety_wit_2.
Axiom proof_of_sortArray_safety_wit_3 : sortArray_safety_wit_3.
Axiom proof_of_sortArray_safety_wit_4 : sortArray_safety_wit_4.
Axiom proof_of_sortArray_safety_wit_5 : sortArray_safety_wit_5.
Axiom proof_of_sortArray_safety_wit_6 : sortArray_safety_wit_6.
Axiom proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Axiom proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Axiom proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1.
Axiom proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2.
Axiom proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Axiom proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Axiom proof_of_sortArray_partial_solve_wit_1 : sortArray_partial_solve_wit_1.
Axiom proof_of_sortArray_partial_solve_wit_2 : sortArray_partial_solve_wit_2.
Axiom proof_of_sortArray_partial_solve_wit_3 : sortArray_partial_solve_wit_3.
Axiom proof_of_sortArray_partial_solve_wit_4 : sortArray_partial_solve_wit_4.
Axiom proof_of_sortArray_partial_solve_wit_5 : sortArray_partial_solve_wit_5.
Axiom proof_of_sortArray_partial_solve_wit_6 : sortArray_partial_solve_wit_6.

End VC_Correct.
