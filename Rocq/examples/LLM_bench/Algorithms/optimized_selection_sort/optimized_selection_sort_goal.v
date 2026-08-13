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
Require Import SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_lib.
Local Open Scope sac.

(*----- Function optimized_selection_sort -----*)

Definition optimized_selection_sort_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition optimized_selection_sort_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (cur: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (cur)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (i < INT_MAX)) (PreH8 : (Permutation input cur )) (PreH9 : (increasing (sublist (0) (i) (cur)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition optimized_selection_sort_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (cur: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (cur)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (i < INT_MAX)) (PreH8 : (Permutation input cur )) (PreH9 : (increasing (sublist (0) (i) (cur)) )) (PreH10 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition optimized_selection_sort_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (cur: (@list Z)) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur )) (PreH10 : (increasing (sublist (0) (i) (cur)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "min_index" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition optimized_selection_sort_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (cur: (@list Z)) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur )) (PreH10 : (increasing (sublist (0) (i) (cur)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "min_index" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition optimized_selection_sort_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i: Z) (cur: (@list Z)) (PreH1 : ((Znth j cur 0) < (Znth min_index cur 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur )) (PreH14 : (increasing (sublist (0) (i) (cur)) )) (PreH15 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) (PreH16 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0))))) ,
  (IntArray.full a_pre n_pre cur )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min_index" ) )) # Int  |-> j)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition optimized_selection_sort_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i: Z) (cur: (@list Z)) (PreH1 : ((Znth j cur 0) >= (Znth min_index cur 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur )) (PreH14 : (increasing (sublist (0) (i) (cur)) )) (PreH15 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) (PreH16 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0))))) ,
  (IntArray.full a_pre n_pre cur )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min_index" ) )) # Int  |-> min_index)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition optimized_selection_sort_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i: Z) (cur: (@list Z)) (PreH1 : (min_index <> i)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur )) (PreH14 : (increasing (sublist (0) (i) (cur)) )) (PreH15 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) (PreH16 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0))))) ,
  (IntArray.full a_pre n_pre (replace_Znth (min_index) ((Znth i cur 0)) ((replace_Znth (i) ((Znth min_index cur 0)) (cur)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition optimized_selection_sort_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i: Z) (cur: (@list Z)) (PreH1 : (min_index = i)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur )) (PreH14 : (increasing (sublist (0) (i) (cur)) )) (PreH15 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) (PreH16 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0))))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition optimized_selection_sort_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
|--
  EX (i: Z)  (cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i < INT_MAX) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre cur )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  TT && emp 
|--
  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < 0)) /\ (0 <= q)) /\ (q < n_pre)) -> ((Znth (p) (input) (0)) <= (Znth (q) (input) (0)))) ” 
  &&  “ (increasing (sublist (0) (0) (input)) ) ” 
  &&  “ (Permutation input input ) ”
  &&  emp
).

Definition optimized_selection_sort_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < 0)) /\ (0 <= q)) /\ (q < n_pre)) -> ((Znth (p) (input) (0)) <= (Znth (q) (input) (0))))
.

Definition optimized_selection_sort_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (increasing (sublist (0) (0) (input)) )
.

Definition optimized_selection_sort_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (Permutation input input )
.

Definition optimized_selection_sort_entail_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i_2: Z) (cur_2: (@list Z)) (PreH1 : ((i_2 + 1 ) < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur_2)) = n_pre)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 <= n_pre)) (PreH8 : (i_2 < INT_MAX)) (PreH9 : (Permutation input cur_2 )) (PreH10 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH11 : forall (p_2: Z) , forall (q_3: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  ((( &( "j" ) )) # Int  |-> (i_2 + 1 ))
  **  ((( &( "min_index" ) )) # Int  |-> i_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  (IntArray.full a_pre n_pre cur_2 )
|--
  EX (j: Z)  (min_index: Z)  (i: Z)  (cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (i <= min_index) ” 
  &&  “ (min_index < j) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0)))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min_index" ) )) # Int  |-> min_index)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre cur )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i_2: Z) (cur_2: (@list Z)) (PreH1 : ((i_2 + 1 ) < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur_2)) = n_pre)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 <= n_pre)) (PreH8 : (i_2 < INT_MAX)) (PreH9 : (Permutation input cur_2 )) (PreH10 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH11 : forall (p_2: Z) , forall (q_3: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  TT && emp 
|--
  “ forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < (i_2 + 1 ))) -> ((Znth (i_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0)))) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur_2) (0)) <= (Znth (q) (cur_2) (0)))) ”
  &&  emp
).

Definition optimized_selection_sort_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i_2: Z) (cur_2: (@list Z)) (PreH1 : ((i_2 + 1 ) < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur_2)) = n_pre)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 <= n_pre)) (PreH8 : (i_2 < INT_MAX)) (PreH9 : (Permutation input cur_2 )) (PreH10 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH11 : forall (p_2: Z) , forall (q_3: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < (i_2 + 1 ))) -> ((Znth (i_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))
.

Definition optimized_selection_sort_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i_2: Z) (cur_2: (@list Z)) (PreH1 : ((i_2 + 1 ) < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur_2)) = n_pre)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 <= n_pre)) (PreH8 : (i_2 < INT_MAX)) (PreH9 : (Permutation input cur_2 )) (PreH10 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH11 : forall (p_2: Z) , forall (q_3: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_3)) /\ (q_3 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur_2) (0)) <= (Znth (q) (cur_2) (0))))
.

Definition optimized_selection_sort_entail_wit_3_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j_2: Z) (min_index_2: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : ((Znth j_2 cur_2 0) < (Znth min_index_2 cur_2 0))) (PreH2 : (j_2 < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : (i_2 <= min_index_2)) (PreH10 : (min_index_2 < j_2)) (PreH11 : ((i_2 + 1 ) <= j_2)) (PreH12 : (j_2 <= n_pre)) (PreH13 : (Permutation input cur_2 )) (PreH14 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH15 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur_2) (0)) <= (Znth (q) (cur_2) (0))))) (PreH16 : forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < j_2)) -> ((Znth (min_index_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) ,
  (IntArray.full a_pre n_pre cur_2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "min_index" ) )) # Int  |-> j_2)
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
|--
  EX (j: Z)  (min_index: Z)  (i: Z)  (cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (i <= min_index) ” 
  &&  “ (min_index < j) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0)))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min_index" ) )) # Int  |-> min_index)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre cur )
.

Definition optimized_selection_sort_entail_wit_3_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j_2: Z) (min_index_2: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : ((Znth j_2 cur_2 0) >= (Znth min_index_2 cur_2 0))) (PreH2 : (j_2 < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : (i_2 <= min_index_2)) (PreH10 : (min_index_2 < j_2)) (PreH11 : ((i_2 + 1 ) <= j_2)) (PreH12 : (j_2 <= n_pre)) (PreH13 : (Permutation input cur_2 )) (PreH14 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH15 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (i_2 <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur_2) (0)) <= (Znth (q) (cur_2) (0))))) (PreH16 : forall (q_2: Z) , (((i_2 <= q_2) /\ (q_2 < j_2)) -> ((Znth (min_index_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) ,
  (IntArray.full a_pre n_pre cur_2 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "min_index" ) )) # Int  |-> min_index_2)
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
|--
  EX (j: Z)  (min_index: Z)  (i: Z)  (cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (i <= min_index) ” 
  &&  “ (min_index < j) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0)))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "min_index" ) )) # Int  |-> min_index)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre cur )
.

Definition optimized_selection_sort_entail_wit_4_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : (min_index <> i_2)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : (i_2 <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i_2 + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur_2 )) (PreH14 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH15 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) (PreH16 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth (min_index) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  (IntArray.full a_pre n_pre (replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
|--
  EX (i: Z)  (cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i < INT_MAX) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre cur )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : ((Zlength ((replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2)))))) = n_pre)) (PreH2 : (min_index <> i_2)) (PreH3 : (j >= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : ((Zlength (cur_2)) = n_pre)) (PreH8 : (0 <= i_2)) (PreH9 : ((i_2 + 1 ) < n_pre)) (PreH10 : (i_2 <= min_index)) (PreH11 : (min_index < j)) (PreH12 : ((i_2 + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (Permutation input cur_2 )) (PreH15 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH16 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) (PreH17 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth (min_index) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  TT && emp 
|--
  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (i_2 + 1 ))) /\ ((i_2 + 1 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) ((replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2))))) (0)) <= (Znth (q) ((replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2))))) (0)))) ” 
  &&  “ (increasing (sublist (0) ((i_2 + 1 )) ((replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2)))))) ) ” 
  &&  “ (Permutation input (replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2)))) ) ”
  &&  emp
).

Definition optimized_selection_sort_entail_wit_4_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : ((Zlength ((replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2)))))) = n_pre)) (PreH2 : (min_index <> i_2)) (PreH3 : (j >= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : ((Zlength (cur_2)) = n_pre)) (PreH8 : (0 <= i_2)) (PreH9 : ((i_2 + 1 ) < n_pre)) (PreH10 : (i_2 <= min_index)) (PreH11 : (min_index < j)) (PreH12 : ((i_2 + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (Permutation input cur_2 )) (PreH15 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH16 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) (PreH17 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth (min_index) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (i_2 + 1 ))) /\ ((i_2 + 1 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) ((replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2))))) (0)) <= (Znth (q) ((replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2))))) (0))))
.

Definition optimized_selection_sort_entail_wit_4_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : ((Zlength ((replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2)))))) = n_pre)) (PreH2 : (min_index <> i_2)) (PreH3 : (j >= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : ((Zlength (cur_2)) = n_pre)) (PreH8 : (0 <= i_2)) (PreH9 : ((i_2 + 1 ) < n_pre)) (PreH10 : (i_2 <= min_index)) (PreH11 : (min_index < j)) (PreH12 : ((i_2 + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (Permutation input cur_2 )) (PreH15 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH16 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) (PreH17 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth (min_index) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  (increasing (sublist (0) ((i_2 + 1 )) ((replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2)))))) )
.

Definition optimized_selection_sort_entail_wit_4_1_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : ((Zlength ((replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2)))))) = n_pre)) (PreH2 : (min_index <> i_2)) (PreH3 : (j >= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : ((Zlength (cur_2)) = n_pre)) (PreH8 : (0 <= i_2)) (PreH9 : ((i_2 + 1 ) < n_pre)) (PreH10 : (i_2 <= min_index)) (PreH11 : (min_index < j)) (PreH12 : ((i_2 + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (Permutation input cur_2 )) (PreH15 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH16 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) (PreH17 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth (min_index) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  (Permutation input (replace_Znth (min_index) ((Znth i_2 cur_2 0)) ((replace_Znth (i_2) ((Znth min_index cur_2 0)) (cur_2)))) )
.

Definition optimized_selection_sort_entail_wit_4_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : (min_index = i_2)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : (i_2 <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i_2 + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur_2 )) (PreH14 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH15 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) (PreH16 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth (min_index) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
  **  (IntArray.full a_pre n_pre cur_2 )
|--
  EX (i: Z)  (cur: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (i < INT_MAX) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre cur )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : (min_index = i_2)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : (i_2 <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i_2 + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur_2 )) (PreH14 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH15 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) (PreH16 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth (min_index) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  TT && emp 
|--
  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (i_2 + 1 ))) /\ ((i_2 + 1 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur_2) (0)) <= (Znth (q) (cur_2) (0)))) ” 
  &&  “ (increasing (sublist (0) ((min_index + 1 )) (cur_2)) ) ”
  &&  emp
).

Definition optimized_selection_sort_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : (min_index = i_2)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : (i_2 <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i_2 + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur_2 )) (PreH14 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH15 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) (PreH16 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth (min_index) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (i_2 + 1 ))) /\ ((i_2 + 1 ) <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur_2) (0)) <= (Znth (q) (cur_2) (0))))
.

Definition optimized_selection_sort_entail_wit_4_2_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i_2: Z) (cur_2: (@list Z)) (PreH1 : (min_index = i_2)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : (i_2 <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i_2 + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur_2 )) (PreH14 : (increasing (sublist (0) (i_2) (cur_2)) )) (PreH15 : forall (p_2: Z) , forall (q_2: Z) , (((((0 <= p_2) /\ (p_2 < i_2)) /\ (i_2 <= q_2)) /\ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) (0)) <= (Znth (q_2) (cur_2) (0))))) (PreH16 : forall (q_3: Z) , (((i_2 <= q_3) /\ (q_3 < j)) -> ((Znth (min_index) (cur_2) (0)) <= (Znth (q_3) (cur_2) (0))))) ,
  (increasing (sublist (0) ((min_index + 1 )) (cur_2)) )
.

Definition optimized_selection_sort_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (cur: (@list Z)) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur )) (PreH10 : (increasing (sublist (0) (i) (cur)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) ,
  (IntArray.full a_pre n_pre cur )
|--
  EX (output: (@list Z)) ,
  “ (optimized_selection_sort_result input output ) ” 
  &&  “ (Permutation input output ) ” 
  &&  “ (increasing output ) ” 
  &&  “ ((Zlength (output)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (cur: (@list Z)) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur )) (PreH10 : (increasing (sublist (0) (i) (cur)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) ,
  TT && emp 
|--
  “ (increasing cur ) ” 
  &&  “ (optimized_selection_sort_result input cur ) ”
  &&  emp
).

Definition optimized_selection_sort_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (cur: (@list Z)) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur )) (PreH10 : (increasing (sublist (0) (i) (cur)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) ,
  (increasing cur )
.

Definition optimized_selection_sort_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (cur: (@list Z)) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur )) (PreH10 : (increasing (sublist (0) (i) (cur)) )) (PreH11 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) ,
  (optimized_selection_sort_result input cur )
.

Definition optimized_selection_sort_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i: Z) (cur: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : ((i + 1 ) < n_pre)) (PreH8 : (i <= min_index)) (PreH9 : (min_index < j)) (PreH10 : ((i + 1 ) <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (Permutation input cur )) (PreH13 : (increasing (sublist (0) (i) (cur)) )) (PreH14 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) (PreH15 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0))))) ,
  (IntArray.full a_pre n_pre cur )
|--
  “ (j < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (i <= min_index) ” 
  &&  “ (min_index < j) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0)))) ”
  &&  (((a_pre + (j * sizeof(INT)))) # Int  |-> (Znth j cur 0))
  **  (IntArray.missing_i a_pre j 0 n_pre cur )
.

Definition optimized_selection_sort_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i: Z) (cur: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : ((i + 1 ) < n_pre)) (PreH8 : (i <= min_index)) (PreH9 : (min_index < j)) (PreH10 : ((i + 1 ) <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (Permutation input cur )) (PreH13 : (increasing (sublist (0) (i) (cur)) )) (PreH14 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) (PreH15 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0))))) ,
  (IntArray.full a_pre n_pre cur )
|--
  “ (j < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (i <= min_index) ” 
  &&  “ (min_index < j) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0)))) ”
  &&  (((a_pre + (min_index * sizeof(INT)))) # Int  |-> (Znth min_index cur 0))
  **  (IntArray.missing_i a_pre min_index 0 n_pre cur )
.

Definition optimized_selection_sort_partial_solve_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i: Z) (cur: (@list Z)) (PreH1 : (min_index <> i)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur )) (PreH14 : (increasing (sublist (0) (i) (cur)) )) (PreH15 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) (PreH16 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0))))) ,
  (IntArray.full a_pre n_pre cur )
|--
  “ (min_index <> i) ” 
  &&  “ (j >= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (i <= min_index) ” 
  &&  “ (min_index < j) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0)))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i cur 0))
  **  (IntArray.missing_i a_pre i 0 n_pre cur )
.

Definition optimized_selection_sort_partial_solve_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i: Z) (cur: (@list Z)) (PreH1 : (min_index <> i)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur )) (PreH14 : (increasing (sublist (0) (i) (cur)) )) (PreH15 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) (PreH16 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0))))) ,
  (IntArray.full a_pre n_pre cur )
|--
  “ (min_index <> i) ” 
  &&  “ (j >= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (i <= min_index) ” 
  &&  “ (min_index < j) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0)))) ”
  &&  (((a_pre + (min_index * sizeof(INT)))) # Int  |-> (Znth min_index cur 0))
  **  (IntArray.missing_i a_pre min_index 0 n_pre cur )
.

Definition optimized_selection_sort_partial_solve_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i: Z) (cur: (@list Z)) (PreH1 : (min_index <> i)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur )) (PreH14 : (increasing (sublist (0) (i) (cur)) )) (PreH15 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) (PreH16 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0))))) ,
  (IntArray.full a_pre n_pre cur )
|--
  “ (min_index <> i) ” 
  &&  “ (j >= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (i <= min_index) ” 
  &&  “ (min_index < j) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0)))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre i 0 n_pre cur )
.

Definition optimized_selection_sort_partial_solve_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (j: Z) (min_index: Z) (i: Z) (cur: (@list Z)) (PreH1 : (min_index <> i)) (PreH2 : (j >= n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur )) (PreH14 : (increasing (sublist (0) (i) (cur)) )) (PreH15 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0))))) (PreH16 : forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0))))) ,
  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth min_index cur 0)) (cur)) )
|--
  “ (min_index <> i) ” 
  &&  “ (j >= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (i <= min_index) ” 
  &&  “ (min_index < j) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (Permutation input cur ) ” 
  &&  “ (increasing (sublist (0) (i) (cur)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (i <= q)) /\ (q < n_pre)) -> ((Znth (p) (cur) (0)) <= (Znth (q) (cur) (0)))) ” 
  &&  “ forall (q_2: Z) , (((i <= q_2) /\ (q_2 < j)) -> ((Znth (min_index) (cur) (0)) <= (Znth (q_2) (cur) (0)))) ”
  &&  (((a_pre + (min_index * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre min_index 0 n_pre (replace_Znth (i) ((Znth min_index cur 0)) (cur)) )
.

Module Type VC_Correct.


Axiom proof_of_optimized_selection_sort_safety_wit_1 : optimized_selection_sort_safety_wit_1.
Axiom proof_of_optimized_selection_sort_safety_wit_2 : optimized_selection_sort_safety_wit_2.
Axiom proof_of_optimized_selection_sort_safety_wit_3 : optimized_selection_sort_safety_wit_3.
Axiom proof_of_optimized_selection_sort_safety_wit_4 : optimized_selection_sort_safety_wit_4.
Axiom proof_of_optimized_selection_sort_safety_wit_5 : optimized_selection_sort_safety_wit_5.
Axiom proof_of_optimized_selection_sort_safety_wit_6 : optimized_selection_sort_safety_wit_6.
Axiom proof_of_optimized_selection_sort_safety_wit_7 : optimized_selection_sort_safety_wit_7.
Axiom proof_of_optimized_selection_sort_safety_wit_8 : optimized_selection_sort_safety_wit_8.
Axiom proof_of_optimized_selection_sort_safety_wit_9 : optimized_selection_sort_safety_wit_9.
Axiom proof_of_optimized_selection_sort_entail_wit_1 : optimized_selection_sort_entail_wit_1.
Axiom proof_of_optimized_selection_sort_entail_wit_2 : optimized_selection_sort_entail_wit_2.
Axiom proof_of_optimized_selection_sort_entail_wit_3_1 : optimized_selection_sort_entail_wit_3_1.
Axiom proof_of_optimized_selection_sort_entail_wit_3_2 : optimized_selection_sort_entail_wit_3_2.
Axiom proof_of_optimized_selection_sort_entail_wit_4_1 : optimized_selection_sort_entail_wit_4_1.
Axiom proof_of_optimized_selection_sort_entail_wit_4_2 : optimized_selection_sort_entail_wit_4_2.
Axiom proof_of_optimized_selection_sort_return_wit_1 : optimized_selection_sort_return_wit_1.
Axiom proof_of_optimized_selection_sort_partial_solve_wit_1 : optimized_selection_sort_partial_solve_wit_1.
Axiom proof_of_optimized_selection_sort_partial_solve_wit_2 : optimized_selection_sort_partial_solve_wit_2.
Axiom proof_of_optimized_selection_sort_partial_solve_wit_3 : optimized_selection_sort_partial_solve_wit_3.
Axiom proof_of_optimized_selection_sort_partial_solve_wit_4 : optimized_selection_sort_partial_solve_wit_4.
Axiom proof_of_optimized_selection_sort_partial_solve_wit_5 : optimized_selection_sort_partial_solve_wit_5.
Axiom proof_of_optimized_selection_sort_partial_solve_wit_6 : optimized_selection_sort_partial_solve_wit_6.

End VC_Correct.
