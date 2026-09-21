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
Require Import SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib.
Local Open Scope sac.

(*----- Function max -----*)

Definition max_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
).

Definition max_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) ,
  (a_pre = (max_Z (a_pre) (b_pre)))
.

Definition max_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (b_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (b_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
).

Definition max_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) ,
  (b_pre = (max_Z (a_pre) (b_pre)))
.

(*----- Function max_sub_array -----*)

Definition max_sub_array_safety_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le ((-10000))) l )) (PreH5 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_sub_array_safety_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ False ”
.

Definition max_sub_array_safety_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_sub_array_safety_wit_4 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "res" ) )) # Int  |->_)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_sub_array_safety_wit_5 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "res" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "cur" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition max_sub_array_safety_wit_6 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur )) (PreH12 : (MaxSubarraySumPrefix l i res )) (PreH13 : (Forall (Z.le ((-10000))) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i l 0) )) ”
) \/
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur )) (PreH12 : (MaxSubarraySumPrefix l i res )) (PreH13 : (Forall (Z.le ((-10000))) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((cur + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i l 0) )) ”
).

Definition max_sub_array_safety_wit_6_split_goal_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur )) (PreH12 : (MaxSubarraySumPrefix l i res )) (PreH13 : (Forall (Z.le ((-10000))) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((cur + (Znth i l 0) ) <= INT_MAX) ”
.

Definition max_sub_array_safety_wit_6_split_goal_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur )) (PreH12 : (MaxSubarraySumPrefix l i res )) (PreH13 : (Forall (Z.le ((-10000))) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  “ ((INT_MIN) <= (cur + (Znth i l 0) )) ”
.

Definition max_sub_array_safety_wit_7 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) ))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur )) (PreH14 : (MaxSubarraySumPrefix l i res )) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> retval)
  **  ((( &( "res" ) )) # Int  |-> retval_2)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition max_sub_array_entail_wit_1 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((-10000) <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) <= 1000000000) ” 
  &&  “ ((-10000) <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l 1 (Znth 0 l 0) ) ” 
  &&  “ (MaxSubarraySumPrefix l 1 (Znth 0 l 0) ) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (MaxSubarraySumPrefix l 1 (Znth 0 l 0) ) ” 
  &&  “ (MaxSuffixSumPrefix l 1 (Znth 0 l 0) ) ” 
  &&  “ ((Znth 0 l 0) <= 1000000000) ” 
  &&  “ ((-10000) <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) <= 1000000000) ” 
  &&  “ ((-10000) <= (Znth 0 l 0)) ”
  &&  emp
).

Definition max_sub_array_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  (MaxSubarraySumPrefix l 1 (Znth 0 l 0) )
.

Definition max_sub_array_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  (MaxSuffixSumPrefix l 1 (Znth 0 l 0) )
.

Definition max_sub_array_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  ((Znth 0 l 0) <= 1000000000)
.

Definition max_sub_array_entail_wit_1_split_goal_4 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  ((-10000) <= (Znth 0 l 0))
.

Definition max_sub_array_entail_wit_1_split_goal_5 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  ((Znth 0 l 0) <= 1000000000)
.

Definition max_sub_array_entail_wit_1_split_goal_6 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  ((-10000) <= (Znth 0 l 0))
.

Definition max_sub_array_entail_wit_2 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) ))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur )) (PreH14 : (MaxSubarraySumPrefix l i res )) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((-10000) <= retval) ” 
  &&  “ (retval <= 1000000000) ” 
  &&  “ ((-10000) <= retval_2) ” 
  &&  “ (retval_2 <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l (i + 1 ) retval ) ” 
  &&  “ (MaxSubarraySumPrefix l (i + 1 ) retval_2 ) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) ))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur )) (PreH14 : (MaxSubarraySumPrefix l i res )) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (MaxSubarraySumPrefix l (i + 1 ) retval_2 ) ” 
  &&  “ (MaxSuffixSumPrefix l (i + 1 ) retval ) ” 
  &&  “ (retval_2 <= 1000000000) ” 
  &&  “ ((-10000) <= retval_2) ” 
  &&  “ (retval <= 1000000000) ” 
  &&  “ ((-10000) <= retval) ”
  &&  emp
).

Definition max_sub_array_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) ))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur )) (PreH14 : (MaxSubarraySumPrefix l i res )) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) ,
  (MaxSubarraySumPrefix l (i + 1 ) retval_2 )
.

Definition max_sub_array_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) ))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur )) (PreH14 : (MaxSubarraySumPrefix l i res )) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) ,
  (MaxSuffixSumPrefix l (i + 1 ) retval )
.

Definition max_sub_array_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) ))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur )) (PreH14 : (MaxSubarraySumPrefix l i res )) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) ,
  (retval_2 <= 1000000000)
.

Definition max_sub_array_entail_wit_2_split_goal_4 := 
forall (n_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) ))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur )) (PreH14 : (MaxSubarraySumPrefix l i res )) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) ,
  ((-10000) <= retval_2)
.

Definition max_sub_array_entail_wit_2_split_goal_5 := 
forall (n_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) ))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur )) (PreH14 : (MaxSubarraySumPrefix l i res )) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) ,
  (retval <= 1000000000)
.

Definition max_sub_array_entail_wit_2_split_goal_6 := 
forall (n_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) ))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur )) (PreH14 : (MaxSubarraySumPrefix l i res )) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) ,
  ((-10000) <= retval)
.

Definition max_sub_array_return_wit_1 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur )) (PreH12 : (MaxSubarraySumPrefix l i res )) (PreH13 : (Forall (Z.le ((-10000))) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (MaxSubarraySumPrefix l n_pre res ) ”
  &&  (IntArray.full arr_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur )) (PreH12 : (MaxSubarraySumPrefix l i res )) (PreH13 : (Forall (Z.le ((-10000))) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (MaxSubarraySumPrefix l n_pre res ) ”
  &&  emp
).

Definition max_sub_array_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur )) (PreH12 : (MaxSubarraySumPrefix l i res )) (PreH13 : (Forall (Z.le ((-10000))) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (MaxSubarraySumPrefix l n_pre res )
.

Definition max_sub_array_partial_solve_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (n_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (((arr_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i arr_pre 0 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (n_pre <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (((arr_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i arr_pre 0 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur )) (PreH12 : (MaxSubarraySumPrefix l i res )) (PreH13 : (Forall (Z.le ((-10000))) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_4 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur )) (PreH12 : (MaxSubarraySumPrefix l i res )) (PreH13 : (Forall (Z.le ((-10000))) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_5 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur )) (PreH12 : (MaxSubarraySumPrefix l i res )) (PreH13 : (Forall (Z.le ((-10000))) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_partial_solve_wit_6 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) (retval: Z) (PreH1 : (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) ))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((-10000) <= cur)) (PreH9 : (cur <= 1000000000)) (PreH10 : ((-10000) <= res)) (PreH11 : (res <= 1000000000)) (PreH12 : (MaxSuffixSumPrefix l i cur )) (PreH13 : (MaxSubarraySumPrefix l i res )) (PreH14 : (Forall (Z.le ((-10000))) l )) (PreH15 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) )))) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((-10000) <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ ((-10000) <= res) ” 
  &&  “ (res <= 1000000000) ” 
  &&  “ (MaxSuffixSumPrefix l i cur ) ” 
  &&  “ (MaxSubarraySumPrefix l i res ) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Module Type VC_Correct.


Axiom proof_of_max_return_wit_1 : max_return_wit_1.
Axiom proof_of_max_return_wit_2 : max_return_wit_2.
Axiom proof_of_max_sub_array_safety_wit_1 : max_sub_array_safety_wit_1.
Axiom proof_of_max_sub_array_safety_wit_2 : max_sub_array_safety_wit_2.
Axiom proof_of_max_sub_array_safety_wit_3 : max_sub_array_safety_wit_3.
Axiom proof_of_max_sub_array_safety_wit_4 : max_sub_array_safety_wit_4.
Axiom proof_of_max_sub_array_safety_wit_5 : max_sub_array_safety_wit_5.
Axiom proof_of_max_sub_array_safety_wit_6 : max_sub_array_safety_wit_6.
Axiom proof_of_max_sub_array_safety_wit_7 : max_sub_array_safety_wit_7.
Axiom proof_of_max_sub_array_entail_wit_1 : max_sub_array_entail_wit_1.
Axiom proof_of_max_sub_array_entail_wit_2 : max_sub_array_entail_wit_2.
Axiom proof_of_max_sub_array_return_wit_1 : max_sub_array_return_wit_1.
Axiom proof_of_max_sub_array_partial_solve_wit_1 : max_sub_array_partial_solve_wit_1.
Axiom proof_of_max_sub_array_partial_solve_wit_2 : max_sub_array_partial_solve_wit_2.
Axiom proof_of_max_sub_array_partial_solve_wit_3 : max_sub_array_partial_solve_wit_3.
Axiom proof_of_max_sub_array_partial_solve_wit_4 : max_sub_array_partial_solve_wit_4.
Axiom proof_of_max_sub_array_partial_solve_wit_5 : max_sub_array_partial_solve_wit_5.
Axiom proof_of_max_sub_array_partial_solve_wit_6 : max_sub_array_partial_solve_wit_6.

End VC_Correct.
