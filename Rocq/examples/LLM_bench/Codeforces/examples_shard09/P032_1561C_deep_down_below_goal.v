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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P032_1561C_deep_down_below_lib.
Local Open Scope sac.

(*----- Function sift_caves -----*)

Definition sift_caves_safety_wit_1 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root)) (PreH7 : (root <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= ((2 * root ) + 1 ))) (PreH10 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH11 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH12 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH13 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH14 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * root ) + 1 )) ”
.

Definition sift_caves_safety_wit_2 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root_pre)) (PreH7 : (root_pre <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= ((2 * root_pre ) + 1 ))) (PreH10 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH11 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH12 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH13 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (((2 * root_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * root_pre ) + 1 )) ”
.

Definition sift_caves_safety_wit_3 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root)) (PreH7 : (root <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= ((2 * root ) + 1 ))) (PreH10 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH11 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH12 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH13 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH14 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((2 * root ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * root )) ”
.

Definition sift_caves_safety_wit_4 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root_pre)) (PreH7 : (root_pre <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= ((2 * root_pre ) + 1 ))) (PreH10 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH11 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH12 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH13 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((2 * root_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * root_pre )) ”
.

Definition sift_caves_safety_wit_5 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root_pre)) (PreH7 : (root_pre <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= ((2 * root_pre ) + 1 ))) (PreH10 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH11 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH12 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH13 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sift_caves_safety_wit_6 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root)) (PreH7 : (root <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= ((2 * root ) + 1 ))) (PreH10 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH11 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH12 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH13 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH14 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sift_caves_safety_wit_7 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root_pre)) (PreH7 : (root_pre <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= ((2 * root_pre ) + 1 ))) (PreH10 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH11 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH12 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH13 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_caves_safety_wit_8 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root)) (PreH7 : (root <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= ((2 * root ) + 1 ))) (PreH10 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH11 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH12 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH13 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH14 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_caves_safety_wit_9 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root_pre ) + 1 ))) (PreH11 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (((2 * root_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * root_pre ) + 1 )) ”
.

Definition sift_caves_safety_wit_10 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root_pre ) + 1 ))) (PreH11 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((2 * root_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * root_pre )) ”
.

Definition sift_caves_safety_wit_11 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root_pre ) + 1 ))) (PreH11 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sift_caves_safety_wit_12 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root_pre ) + 1 ))) (PreH11 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_caves_safety_wit_13 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH14 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * root ) + 1 )) ”
.

Definition sift_caves_safety_wit_14 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH14 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((2 * root ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * root )) ”
.

Definition sift_caves_safety_wit_15 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH14 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sift_caves_safety_wit_16 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH14 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_caves_safety_wit_17 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH14 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root ) + 1 ) + 1 )) ”
.

Definition sift_caves_safety_wit_18 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root_pre ) + 1 ))) (PreH11 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |-> ((2 * root_pre ) + 1 ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((((2 * root_pre ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root_pre ) + 1 ) + 1 )) ”
.

Definition sift_caves_safety_wit_19 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root_pre ) + 1 ))) (PreH11 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |-> ((2 * root_pre ) + 1 ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_caves_safety_wit_20 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH14 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_caves_safety_wit_21 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre)) (PreH2 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH3 : (1 <= n)) (PreH4 : (n <= 100000)) (PreH5 : ((Zlength (requirements_now)) = n)) (PreH6 : ((Zlength (gains_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root_pre)) (PreH9 : (root_pre <= hi_pre)) (PreH10 : (hi_pre < n)) (PreH11 : (0 <= ((2 * root_pre ) + 1 ))) (PreH12 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root_pre ) + 1 ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((((2 * root_pre ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root_pre ) + 1 ) + 1 )) ”
.

Definition sift_caves_safety_wit_22 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= hi_pre)) (PreH2 : (((2 * root ) + 1 ) <= hi_pre)) (PreH3 : (1 <= n)) (PreH4 : (n <= 100000)) (PreH5 : ((Zlength (requirements_now)) = n)) (PreH6 : ((Zlength (gains_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= hi_pre)) (PreH10 : (hi_pre < n)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH15 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH18 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root ) + 1 ) + 1 )) ”
.

Definition sift_caves_safety_wit_23 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= hi_pre)) (PreH2 : (((2 * root ) + 1 ) <= hi_pre)) (PreH3 : (1 <= n)) (PreH4 : (n <= 100000)) (PreH5 : ((Zlength (requirements_now)) = n)) (PreH6 : ((Zlength (gains_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= hi_pre)) (PreH10 : (hi_pre < n)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH15 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH18 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_caves_safety_wit_24 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre)) (PreH2 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH3 : (1 <= n)) (PreH4 : (n <= 100000)) (PreH5 : ((Zlength (requirements_now)) = n)) (PreH6 : ((Zlength (gains_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root_pre)) (PreH9 : (root_pre <= hi_pre)) (PreH10 : (hi_pre < n)) (PreH11 : (0 <= ((2 * root_pre ) + 1 ))) (PreH12 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root_pre ) + 1 ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_caves_safety_wit_25 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : ((Znth ((2 * root_pre ) + 1 ) requirements_now 0) < (Znth (((2 * root_pre ) + 1 ) + 1 ) requirements_now 0))) (PreH2 : ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre)) (PreH3 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : ((Zlength (requirements_now)) = n)) (PreH7 : ((Zlength (gains_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root_pre)) (PreH10 : (root_pre <= hi_pre)) (PreH11 : (hi_pre < n)) (PreH12 : (0 <= ((2 * root_pre ) + 1 ))) (PreH13 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root_pre ) + 1 ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((((2 * root_pre ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root_pre ) + 1 ) + 1 )) ”
.

Definition sift_caves_safety_wit_26 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : ((Znth ((2 * root ) + 1 ) requirements_now 0) < (Znth (((2 * root ) + 1 ) + 1 ) requirements_now 0))) (PreH2 : ((((2 * root ) + 1 ) + 1 ) <= hi_pre)) (PreH3 : (((2 * root ) + 1 ) <= hi_pre)) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : ((Zlength (requirements_now)) = n)) (PreH7 : ((Zlength (gains_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= hi_pre)) (PreH11 : (hi_pre < n)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH17 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH18 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH19 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root ) + 1 ) + 1 )) ”
.

Definition sift_caves_entail_wit_1 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements)) = n)) (PreH4 : ((Zlength (gains)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= hi_pre)) (PreH7 : (hi_pre < n)) (PreH8 : (HeapOrderedExceptAtFrom requirements root_pre hi_pre root_pre )) ,
  (Int64Array.full req_pre n requirements )
  **  (Int64Array.full gain_pre n gains )
|--
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
  ||
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((((2 * root_pre ) + 1 ) <= hi_pre) -> ((Znth ((2 * root_pre ) + 1 ) requirements_now 0) <= (Znth ((root_pre - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((((2 * root_pre ) + 2 ) <= hi_pre) -> ((Znth ((2 * root_pre ) + 2 ) requirements_now 0) <= (Znth ((root_pre - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
.

Definition sift_caves_entail_wit_2_1 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : ((Znth ((2 * root_pre ) + 1 ) requirements_now_2 0) < (Znth (((2 * root_pre ) + 1 ) + 1 ) requirements_now_2 0))) (PreH2 : ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre)) (PreH3 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : ((Zlength (requirements_now_2)) = n)) (PreH7 : ((Zlength (gains_now_2)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root_pre)) (PreH10 : (root_pre <= hi_pre)) (PreH11 : (hi_pre < n)) (PreH12 : (0 <= ((2 * root_pre ) + 1 ))) (PreH13 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now_2 )
  **  (Int64Array.full gain_pre n gains_now_2 )
|--
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= (((2 * root_pre ) + 1 ) + 1 )) ” 
  &&  “ ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre (((2 * root_pre ) + 1 ) + 1 ) ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
  ||
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= (((2 * root_pre ) + 1 ) + 1 )) ” 
  &&  “ ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre (((2 * root_pre ) + 1 ) + 1 ) ) ” 
  &&  “ ((Znth (((2 * root_pre ) + 1 ) + 1 ) requirements_now 0) <= (Znth ((root_pre - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
.

Definition sift_caves_entail_wit_2_2 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : ((Znth ((2 * root ) + 1 ) requirements_now_2 0) < (Znth (((2 * root ) + 1 ) + 1 ) requirements_now_2 0))) (PreH2 : ((((2 * root ) + 1 ) + 1 ) <= hi_pre)) (PreH3 : (((2 * root ) + 1 ) <= hi_pre)) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : ((Zlength (requirements_now_2)) = n)) (PreH7 : ((Zlength (gains_now_2)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= hi_pre)) (PreH11 : (hi_pre < n)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0)))) (PreH17 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0)))) (PreH18 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH19 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now_2 )
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full gain_pre n gains_now_2 )
|--
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= (((2 * root ) + 1 ) + 1 )) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre (((2 * root ) + 1 ) + 1 ) ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
  ||
  (EX (root_2: Z)  (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_2) ” 
  &&  “ (root_2 <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= (((2 * root ) + 1 ) + 1 )) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_2 hi_pre (((2 * root ) + 1 ) + 1 ) ) ” 
  &&  “ ((Znth (((2 * root ) + 1 ) + 1 ) requirements_now 0) <= (Znth ((root_2 - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_2 ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  ((( &( "root" ) )) # Int  |-> root_2)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
.

Definition sift_caves_entail_wit_2_3 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) > hi_pre)) (PreH2 : (((2 * root ) + 1 ) <= hi_pre)) (PreH3 : (1 <= n)) (PreH4 : (n <= 100000)) (PreH5 : ((Zlength (requirements_now_2)) = n)) (PreH6 : ((Zlength (gains_now_2)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= hi_pre)) (PreH10 : (hi_pre < n)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH15 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0)))) (PreH16 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH18 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now_2 )
  **  (Int64Array.full gain_pre n gains_now_2 )
|--
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre ((2 * root ) + 1 ) ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
  ||
  (EX (root_2: Z)  (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_2) ” 
  &&  “ (root_2 <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_2 hi_pre ((2 * root ) + 1 ) ) ” 
  &&  “ ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root_2 - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_2 ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  ((( &( "root" ) )) # Int  |-> root_2)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
.

Definition sift_caves_entail_wit_2_4 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : ((((2 * root_pre ) + 1 ) + 1 ) > hi_pre)) (PreH2 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH3 : (1 <= n)) (PreH4 : (n <= 100000)) (PreH5 : ((Zlength (requirements_now_2)) = n)) (PreH6 : ((Zlength (gains_now_2)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root_pre)) (PreH9 : (root_pre <= hi_pre)) (PreH10 : (hi_pre < n)) (PreH11 : (0 <= ((2 * root_pre ) + 1 ))) (PreH12 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now_2 )
  **  (Int64Array.full gain_pre n gains_now_2 )
|--
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre ((2 * root_pre ) + 1 ) ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
  ||
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre ((2 * root_pre ) + 1 ) ) ” 
  &&  “ ((Znth ((2 * root_pre ) + 1 ) requirements_now 0) <= (Znth ((root_pre - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
.

Definition sift_caves_entail_wit_2_5 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : ((Znth ((2 * root_pre ) + 1 ) requirements_now_2 0) >= (Znth (((2 * root_pre ) + 1 ) + 1 ) requirements_now_2 0))) (PreH2 : ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre)) (PreH3 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : ((Zlength (requirements_now_2)) = n)) (PreH7 : ((Zlength (gains_now_2)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root_pre)) (PreH10 : (root_pre <= hi_pre)) (PreH11 : (hi_pre < n)) (PreH12 : (0 <= ((2 * root_pre ) + 1 ))) (PreH13 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now_2 )
  **  (Int64Array.full gain_pre n gains_now_2 )
|--
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre ((2 * root_pre ) + 1 ) ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
  ||
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre ((2 * root_pre ) + 1 ) ) ” 
  &&  “ ((Znth ((2 * root_pre ) + 1 ) requirements_now 0) <= (Znth ((root_pre - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
.

Definition sift_caves_entail_wit_2_6 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : ((Znth ((2 * root ) + 1 ) requirements_now_2 0) >= (Znth (((2 * root ) + 1 ) + 1 ) requirements_now_2 0))) (PreH2 : ((((2 * root ) + 1 ) + 1 ) <= hi_pre)) (PreH3 : (((2 * root ) + 1 ) <= hi_pre)) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : ((Zlength (requirements_now_2)) = n)) (PreH7 : ((Zlength (gains_now_2)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= hi_pre)) (PreH11 : (hi_pre < n)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0)))) (PreH17 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0)))) (PreH18 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH19 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now_2 )
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full gain_pre n gains_now_2 )
|--
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre ((2 * root ) + 1 ) ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
  ||
  (EX (root_2: Z)  (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_2) ” 
  &&  “ (root_2 <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_2 hi_pre ((2 * root ) + 1 ) ) ” 
  &&  “ ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root_2 - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_2 ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  ((( &( "root" ) )) # Int  |-> root_2)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
.

Definition sift_caves_entail_wit_3_1 := 
(
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full gain_pre n (replace_Znth (child_2) ((Znth root_pre gains_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 gains_now_2 0)) (gains_now_2)))) )
  **  (Int64Array.full req_pre n (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) )
  **  ((( &( "t" ) )) # Int64  |-> (Znth root_pre gains_now_2 0))
  **  ((( &( "child" ) )) # Int  |-> child_2)
|--
  EX (child: Z)  (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre < child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre child ) ” 
  &&  “ ((((2 * child ) + 1 ) <= hi_pre) -> ((Znth ((2 * child ) + 1 ) requirements_now 0) <= (Znth ((child - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((((2 * child ) + 2 ) <= hi_pre) -> ((Znth ((2 * child ) + 2 ) requirements_now 0) <= (Znth ((child - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  ((( &( "child" ) )) # Int  |-> child)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
  **  ((( &( "t" ) )) # Int64  |->_)
) \/
(
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  TT && emp 
|--
  “ ((sublist ((hi_pre + 1 )) (n) ((replace_Znth (child_2) ((Znth root_pre gains_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 gains_now_2 0)) (gains_now_2)))))) = (sublist ((hi_pre + 1 )) (n) (gains))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) ((replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))))) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((((2 * child_2 ) + 2 ) <= hi_pre) -> ((Znth ((2 * child_2 ) + 2 ) (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0) <= (Znth ((child_2 - 1 ) ÷ 2 ) (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0))) ” 
  &&  “ ((((2 * child_2 ) + 1 ) <= hi_pre) -> ((Znth ((2 * child_2 ) + 1 ) (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0) <= (Znth ((child_2 - 1 ) ÷ 2 ) (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0))) ” 
  &&  “ (HeapOrderedExceptAtFrom (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) root_pre hi_pre child_2 ) ” 
  &&  “ (ParallelPermutation requirements gains (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) (replace_Znth (child_2) ((Znth root_pre gains_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 gains_now_2 0)) (gains_now_2)))) ) ” 
  &&  “ (root_pre < child_2) ” 
  &&  “ ((Zlength ((replace_Znth (child_2) ((Znth root_pre gains_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 gains_now_2 0)) (gains_now_2)))))) = n) ” 
  &&  “ ((Zlength ((replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))))) = n) ”
  &&  emp
).

Definition sift_caves_entail_wit_3_1_split_goal_1 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((sublist ((hi_pre + 1 )) (n) ((replace_Znth (child_2) ((Znth root_pre gains_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 gains_now_2 0)) (gains_now_2)))))) = (sublist ((hi_pre + 1 )) (n) (gains)))
.

Definition sift_caves_entail_wit_3_1_split_goal_2 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((sublist ((hi_pre + 1 )) (n) ((replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))))) = (sublist ((hi_pre + 1 )) (n) (requirements)))
.

Definition sift_caves_entail_wit_3_1_split_goal_3 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((((2 * child_2 ) + 2 ) <= hi_pre) -> ((Znth ((2 * child_2 ) + 2 ) (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0) <= (Znth ((child_2 - 1 ) ÷ 2 ) (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0)))
.

Definition sift_caves_entail_wit_3_1_split_goal_4 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((((2 * child_2 ) + 1 ) <= hi_pre) -> ((Znth ((2 * child_2 ) + 1 ) (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0) <= (Znth ((child_2 - 1 ) ÷ 2 ) (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0)))
.

Definition sift_caves_entail_wit_3_1_split_goal_5 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (HeapOrderedExceptAtFrom (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) root_pre hi_pre child_2 )
.

Definition sift_caves_entail_wit_3_1_split_goal_6 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (ParallelPermutation requirements gains (replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) (replace_Znth (child_2) ((Znth root_pre gains_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 gains_now_2 0)) (gains_now_2)))) )
.

Definition sift_caves_entail_wit_3_1_split_goal_7 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (root_pre < child_2)
.

Definition sift_caves_entail_wit_3_1_split_goal_8 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((Zlength ((replace_Znth (child_2) ((Znth root_pre gains_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 gains_now_2 0)) (gains_now_2)))))) = n)
.

Definition sift_caves_entail_wit_3_1_split_goal_9 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (child_2: Z) (PreH1 : ((Znth root_pre requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root_pre hi_pre child_2 )) (PreH13 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((Zlength ((replace_Znth (child_2) ((Znth root_pre requirements_now_2 0)) ((replace_Znth (root_pre) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))))) = n)
.

Definition sift_caves_entail_wit_3_2 := 
(
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full gain_pre n (replace_Znth (child_2) ((Znth root gains_now_2 0)) ((replace_Znth (root) ((Znth child_2 gains_now_2 0)) (gains_now_2)))) )
  **  (Int64Array.full req_pre n (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) )
  **  ((( &( "t" ) )) # Int64  |-> (Znth root gains_now_2 0))
  **  ((( &( "child" ) )) # Int  |-> child_2)
|--
  EX (child: Z)  (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root < child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre child ) ” 
  &&  “ ((((2 * child ) + 1 ) <= hi_pre) -> ((Znth ((2 * child ) + 1 ) requirements_now 0) <= (Znth ((child - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((((2 * child ) + 2 ) <= hi_pre) -> ((Znth ((2 * child ) + 2 ) requirements_now 0) <= (Znth ((child - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  ((( &( "child" ) )) # Int  |-> child)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
  **  ((( &( "t" ) )) # Int64  |->_)
) \/
(
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  TT && emp 
|--
  “ ((sublist ((hi_pre + 1 )) (n) ((replace_Znth (child_2) ((Znth root gains_now_2 0)) ((replace_Znth (root) ((Znth child_2 gains_now_2 0)) (gains_now_2)))))) = (sublist ((hi_pre + 1 )) (n) (gains))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) ((replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))))) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((((2 * child_2 ) + 2 ) <= hi_pre) -> ((Znth ((2 * child_2 ) + 2 ) (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0) <= (Znth ((child_2 - 1 ) ÷ 2 ) (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0))) ” 
  &&  “ ((((2 * child_2 ) + 1 ) <= hi_pre) -> ((Znth ((2 * child_2 ) + 1 ) (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0) <= (Znth ((child_2 - 1 ) ÷ 2 ) (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0))) ” 
  &&  “ (HeapOrderedExceptAtFrom (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) root_pre hi_pre child_2 ) ” 
  &&  “ (ParallelPermutation requirements gains (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) (replace_Znth (child_2) ((Znth root gains_now_2 0)) ((replace_Znth (root) ((Znth child_2 gains_now_2 0)) (gains_now_2)))) ) ” 
  &&  “ (root < child_2) ” 
  &&  “ ((Zlength ((replace_Znth (child_2) ((Znth root gains_now_2 0)) ((replace_Znth (root) ((Znth child_2 gains_now_2 0)) (gains_now_2)))))) = n) ” 
  &&  “ ((Zlength ((replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))))) = n) ”
  &&  emp
).

Definition sift_caves_entail_wit_3_2_split_goal_1 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((sublist ((hi_pre + 1 )) (n) ((replace_Znth (child_2) ((Znth root gains_now_2 0)) ((replace_Znth (root) ((Znth child_2 gains_now_2 0)) (gains_now_2)))))) = (sublist ((hi_pre + 1 )) (n) (gains)))
.

Definition sift_caves_entail_wit_3_2_split_goal_2 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((sublist ((hi_pre + 1 )) (n) ((replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))))) = (sublist ((hi_pre + 1 )) (n) (requirements)))
.

Definition sift_caves_entail_wit_3_2_split_goal_3 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((((2 * child_2 ) + 2 ) <= hi_pre) -> ((Znth ((2 * child_2 ) + 2 ) (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0) <= (Znth ((child_2 - 1 ) ÷ 2 ) (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0)))
.

Definition sift_caves_entail_wit_3_2_split_goal_4 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((((2 * child_2 ) + 1 ) <= hi_pre) -> ((Znth ((2 * child_2 ) + 1 ) (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0) <= (Znth ((child_2 - 1 ) ÷ 2 ) (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) 0)))
.

Definition sift_caves_entail_wit_3_2_split_goal_5 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (HeapOrderedExceptAtFrom (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) root_pre hi_pre child_2 )
.

Definition sift_caves_entail_wit_3_2_split_goal_6 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (ParallelPermutation requirements gains (replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))) (replace_Znth (child_2) ((Znth root gains_now_2 0)) ((replace_Znth (root) ((Znth child_2 gains_now_2 0)) (gains_now_2)))) )
.

Definition sift_caves_entail_wit_3_2_split_goal_7 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (root < child_2)
.

Definition sift_caves_entail_wit_3_2_split_goal_8 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((Zlength ((replace_Znth (child_2) ((Znth root gains_now_2 0)) ((replace_Znth (root) ((Znth child_2 gains_now_2 0)) (gains_now_2)))))) = n)
.

Definition sift_caves_entail_wit_3_2_split_goal_9 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (child_2: Z) (PreH1 : ((Znth root requirements_now_2 0) < (Znth child_2 requirements_now_2 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now_2)) = n)) (PreH5 : ((Zlength (gains_now_2)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child_2)) (PreH11 : (child_2 <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now_2 root hi_pre child_2 )) (PreH13 : ((Znth child_2 requirements_now_2 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now_2 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((Zlength ((replace_Znth (child_2) ((Znth root requirements_now_2 0)) ((replace_Znth (root) ((Znth child_2 requirements_now_2 0)) (requirements_now_2)))))) = n)
.

Definition sift_caves_entail_wit_4_1 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now_2)) = n)) (PreH4 : ((Zlength (gains_now_2)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root)) (PreH7 : (root < root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH11 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre root_pre )) (PreH12 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH13 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now_2 )
  **  (Int64Array.full gain_pre n gains_now_2 )
|--
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
  ||
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((((2 * root_pre ) + 1 ) <= hi_pre) -> ((Znth ((2 * root_pre ) + 1 ) requirements_now 0) <= (Znth ((root_pre - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((((2 * root_pre ) + 2 ) <= hi_pre) -> ((Znth ((2 * root_pre ) + 2 ) requirements_now 0) <= (Znth ((root_pre - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
.

Definition sift_caves_entail_wit_4_2 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root_2: Z) (child: Z) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now_2)) = n)) (PreH4 : ((Zlength (gains_now_2)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root_2)) (PreH7 : (root_2 < child)) (PreH8 : (child <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH11 : (HeapOrderedExceptAtFrom requirements_now_2 root_pre hi_pre child )) (PreH12 : ((((2 * child ) + 1 ) <= hi_pre) -> ((Znth ((2 * child ) + 1 ) requirements_now_2 0) <= (Znth ((child - 1 ) ÷ 2 ) requirements_now_2 0)))) (PreH13 : ((((2 * child ) + 2 ) <= hi_pre) -> ((Znth ((2 * child ) + 2 ) requirements_now_2 0) <= (Znth ((child - 1 ) ÷ 2 ) requirements_now_2 0)))) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now_2)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now_2)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  ((( &( "root" ) )) # Int  |-> child)
  **  (Int64Array.full req_pre n requirements_now_2 )
  **  (Int64Array.full gain_pre n gains_now_2 )
|--
  (EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  ((( &( "root" ) )) # Int  |-> root_pre)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
  ||
  (EX (root: Z)  (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now ))
.

Definition sift_caves_return_wit_1 := 
(
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) >= (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  EX (gains_after: (@list Z))  (requirements_after: (@list Z)) ,
  “ ((Zlength (requirements_after)) = n) ” 
  &&  “ ((Zlength (gains_after)) = n) ” 
  &&  “ (ParallelPermutation requirements gains requirements_after gains_after ) ” 
  &&  “ (HeapParentsFrom requirements_after root_pre hi_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_after)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_after)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_after )
  **  (Int64Array.full gain_pre n gains_after )
) \/
(
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) >= (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  TT && emp 
|--
  “ (HeapParentsFrom requirements_now root_pre hi_pre ) ”
  &&  emp
).

Definition sift_caves_return_wit_1_split_goal_1 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) >= (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (HeapParentsFrom requirements_now root_pre hi_pre )
.

Definition sift_caves_return_wit_2 := 
(
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) >= (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  EX (gains_after: (@list Z))  (requirements_after: (@list Z)) ,
  “ ((Zlength (requirements_after)) = n) ” 
  &&  “ ((Zlength (gains_after)) = n) ” 
  &&  “ (ParallelPermutation requirements gains requirements_after gains_after ) ” 
  &&  “ (HeapParentsFrom requirements_after root_pre hi_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_after)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_after)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_after )
  **  (Int64Array.full gain_pre n gains_after )
) \/
(
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) >= (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  TT && emp 
|--
  “ (HeapParentsFrom requirements_now root_pre hi_pre ) ”
  &&  emp
).

Definition sift_caves_return_wit_2_split_goal_1 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) >= (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (HeapParentsFrom requirements_now root_pre hi_pre )
.

Definition sift_caves_return_wit_3 := 
(
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root_pre ) + 1 ) > hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root_pre ) + 1 ))) (PreH11 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  EX (gains_after: (@list Z))  (requirements_after: (@list Z)) ,
  “ ((Zlength (requirements_after)) = n) ” 
  &&  “ ((Zlength (gains_after)) = n) ” 
  &&  “ (ParallelPermutation requirements gains requirements_after gains_after ) ” 
  &&  “ (HeapParentsFrom requirements_after root_pre hi_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_after)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_after)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_after )
  **  (Int64Array.full gain_pre n gains_after )
) \/
(
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root_pre ) + 1 ) > hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root_pre ) + 1 ))) (PreH11 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  TT && emp 
|--
  “ (HeapParentsFrom requirements_now root_pre hi_pre ) ”
  &&  emp
).

Definition sift_caves_return_wit_3_split_goal_1 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root_pre ) + 1 ) > hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root_pre ) + 1 ))) (PreH11 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (HeapParentsFrom requirements_now root_pre hi_pre )
.

Definition sift_caves_return_wit_4 := 
(
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) > hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH14 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  EX (gains_after: (@list Z))  (requirements_after: (@list Z)) ,
  “ ((Zlength (requirements_after)) = n) ” 
  &&  “ ((Zlength (gains_after)) = n) ” 
  &&  “ (ParallelPermutation requirements gains requirements_after gains_after ) ” 
  &&  “ (HeapParentsFrom requirements_after root_pre hi_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_after)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_after)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (Int64Array.full req_pre n requirements_after )
  **  (Int64Array.full gain_pre n gains_after )
) \/
(
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) > hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH14 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  TT && emp 
|--
  “ (HeapParentsFrom requirements_now root_pre hi_pre ) ”
  &&  emp
).

Definition sift_caves_return_wit_4_split_goal_1 := 
forall (hi_pre: Z) (root_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) > hi_pre)) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH14 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH15 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (HeapParentsFrom requirements_now root_pre hi_pre )
.

Definition sift_caves_partial_solve_wit_1 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= hi_pre)) (PreH2 : (((2 * root ) + 1 ) <= hi_pre)) (PreH3 : (1 <= n)) (PreH4 : (n <= 100000)) (PreH5 : ((Zlength (requirements_now)) = n)) (PreH6 : ((Zlength (gains_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= hi_pre)) (PreH10 : (hi_pre < n)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH15 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH18 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= hi_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= hi_pre) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (((2 * root ) + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((2 * root ) + 1 ) requirements_now 0))
  **  (Int64Array.missing_i req_pre ((2 * root ) + 1 ) 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_2 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre)) (PreH2 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH3 : (1 <= n)) (PreH4 : (n <= 100000)) (PreH5 : ((Zlength (requirements_now)) = n)) (PreH6 : ((Zlength (gains_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root_pre)) (PreH9 : (root_pre <= hi_pre)) (PreH10 : (hi_pre < n)) (PreH11 : (0 <= ((2 * root_pre ) + 1 ))) (PreH12 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= hi_pre) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (((2 * root_pre ) + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((2 * root_pre ) + 1 ) requirements_now 0))
  **  (Int64Array.missing_i req_pre ((2 * root_pre ) + 1 ) 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_3 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= hi_pre)) (PreH2 : (((2 * root ) + 1 ) <= hi_pre)) (PreH3 : (1 <= n)) (PreH4 : (n <= 100000)) (PreH5 : ((Zlength (requirements_now)) = n)) (PreH6 : ((Zlength (gains_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= hi_pre)) (PreH10 : (hi_pre < n)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH15 : ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH16 : ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH18 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= hi_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= hi_pre) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((((2 * root ) + 1 ) <= hi_pre) -> ((Znth ((2 * root ) + 1 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((((2 * root ) + 2 ) <= hi_pre) -> ((Znth ((2 * root ) + 2 ) requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + ((((2 * root ) + 1 ) + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (((2 * root ) + 1 ) + 1 ) requirements_now 0))
  **  (Int64Array.missing_i req_pre (((2 * root ) + 1 ) + 1 ) 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_4 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre)) (PreH2 : (((2 * root_pre ) + 1 ) <= hi_pre)) (PreH3 : (1 <= n)) (PreH4 : (n <= 100000)) (PreH5 : ((Zlength (requirements_now)) = n)) (PreH6 : ((Zlength (gains_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root_pre)) (PreH9 : (root_pre <= hi_pre)) (PreH10 : (hi_pre < n)) (PreH11 : (0 <= ((2 * root_pre ) + 1 ))) (PreH12 : (((2 * root_pre ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((((2 * root_pre ) + 1 ) + 1 ) <= hi_pre) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= hi_pre) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + ((((2 * root_pre ) + 1 ) + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (((2 * root_pre ) + 1 ) + 1 ) requirements_now 0))
  **  (Int64Array.missing_i req_pre (((2 * root_pre ) + 1 ) + 1 ) 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_5 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root_pre)) (PreH7 : (root_pre <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= child)) (PreH10 : (child <= hi_pre)) (PreH11 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre child ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (root_pre * sizeof(INT64)))) # Int64  |-> (Znth root_pre requirements_now 0))
  **  (Int64Array.missing_i req_pre root_pre 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_6 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root)) (PreH7 : (root <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= child)) (PreH10 : (child <= hi_pre)) (PreH11 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH12 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root hi_pre child ) ” 
  &&  “ ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (root * sizeof(INT64)))) # Int64  |-> (Znth root requirements_now 0))
  **  (Int64Array.missing_i req_pre root 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_7 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root_pre)) (PreH7 : (root_pre <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= child)) (PreH10 : (child <= hi_pre)) (PreH11 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH12 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH13 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH14 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre child ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (child * sizeof(INT64)))) # Int64  |-> (Znth child requirements_now 0))
  **  (Int64Array.missing_i req_pre child 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_8 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : (1 <= n)) (PreH2 : (n <= 100000)) (PreH3 : ((Zlength (requirements_now)) = n)) (PreH4 : ((Zlength (gains_now)) = n)) (PreH5 : (0 <= root_pre)) (PreH6 : (root_pre <= root)) (PreH7 : (root <= hi_pre)) (PreH8 : (hi_pre < n)) (PreH9 : (0 <= child)) (PreH10 : (child <= hi_pre)) (PreH11 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH12 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root hi_pre child ) ” 
  &&  “ ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (child * sizeof(INT64)))) # Int64  |-> (Znth child requirements_now 0))
  **  (Int64Array.missing_i req_pre child 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_9 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre child ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (root_pre * sizeof(INT64)))) # Int64  |-> (Znth root_pre requirements_now 0))
  **  (Int64Array.missing_i req_pre root_pre 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_10 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((Znth root requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root hi_pre child ) ” 
  &&  “ ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (root * sizeof(INT64)))) # Int64  |-> (Znth root requirements_now 0))
  **  (Int64Array.missing_i req_pre root 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_11 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre child ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (child * sizeof(INT64)))) # Int64  |-> (Znth child requirements_now 0))
  **  (Int64Array.missing_i req_pre child 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_12 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre child ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (root_pre * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i req_pre root_pre 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_13 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((Znth root requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root hi_pre child ) ” 
  &&  “ ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (child * sizeof(INT64)))) # Int64  |-> (Znth child requirements_now 0))
  **  (Int64Array.missing_i req_pre child 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_14 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((Znth root requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root hi_pre child ) ” 
  &&  “ ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (root * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i req_pre root 0 n requirements_now )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_15 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n (replace_Znth (root_pre) ((Znth child requirements_now 0)) (requirements_now)) )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre child ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (child * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i req_pre child 0 n (replace_Znth (root_pre) ((Znth child requirements_now 0)) (requirements_now)) )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_16 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n (replace_Znth (root) ((Znth child requirements_now 0)) (requirements_now)) )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((Znth root requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root hi_pre child ) ” 
  &&  “ ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((req_pre + (child * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i req_pre child 0 n (replace_Znth (root) ((Znth child requirements_now 0)) (requirements_now)) )
  **  (Int64Array.full gain_pre n gains_now )
.

Definition sift_caves_partial_solve_wit_17 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root_pre requirements_now 0)) ((replace_Znth (root_pre) ((Znth child requirements_now 0)) (requirements_now)))) )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre child ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((gain_pre + (root_pre * sizeof(INT64)))) # Int64  |-> (Znth root_pre gains_now 0))
  **  (Int64Array.missing_i gain_pre root_pre 0 n gains_now )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root_pre requirements_now 0)) ((replace_Znth (root_pre) ((Znth child requirements_now 0)) (requirements_now)))) )
.

Definition sift_caves_partial_solve_wit_18 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root requirements_now 0)) ((replace_Znth (root) ((Znth child requirements_now 0)) (requirements_now)))) )
  **  (Int64Array.full gain_pre n gains_now )
|--
  “ ((Znth root requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root hi_pre child ) ” 
  &&  “ ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((gain_pre + (root * sizeof(INT64)))) # Int64  |-> (Znth root gains_now 0))
  **  (Int64Array.missing_i gain_pre root 0 n gains_now )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root requirements_now 0)) ((replace_Znth (root) ((Znth child requirements_now 0)) (requirements_now)))) )
.

Definition sift_caves_partial_solve_wit_19 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full gain_pre n gains_now )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root_pre requirements_now 0)) ((replace_Znth (root_pre) ((Znth child requirements_now 0)) (requirements_now)))) )
|--
  “ ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre child ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((gain_pre + (child * sizeof(INT64)))) # Int64  |-> (Znth child gains_now 0))
  **  (Int64Array.missing_i gain_pre child 0 n gains_now )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root_pre requirements_now 0)) ((replace_Znth (root_pre) ((Znth child requirements_now 0)) (requirements_now)))) )
.

Definition sift_caves_partial_solve_wit_20 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full gain_pre n gains_now )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root_pre requirements_now 0)) ((replace_Znth (root_pre) ((Znth child requirements_now 0)) (requirements_now)))) )
|--
  “ ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre child ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((gain_pre + (root_pre * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i gain_pre root_pre 0 n gains_now )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root_pre requirements_now 0)) ((replace_Znth (root_pre) ((Znth child requirements_now 0)) (requirements_now)))) )
.

Definition sift_caves_partial_solve_wit_21 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full gain_pre n gains_now )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root requirements_now 0)) ((replace_Znth (root) ((Znth child requirements_now 0)) (requirements_now)))) )
|--
  “ ((Znth root requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root hi_pre child ) ” 
  &&  “ ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((gain_pre + (child * sizeof(INT64)))) # Int64  |-> (Znth child gains_now 0))
  **  (Int64Array.missing_i gain_pre child 0 n gains_now )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root requirements_now 0)) ((replace_Znth (root) ((Znth child requirements_now 0)) (requirements_now)))) )
.

Definition sift_caves_partial_solve_wit_22 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full gain_pre n gains_now )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root requirements_now 0)) ((replace_Znth (root) ((Znth child requirements_now 0)) (requirements_now)))) )
|--
  “ ((Znth root requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root hi_pre child ) ” 
  &&  “ ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((gain_pre + (root * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i gain_pre root 0 n gains_now )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root requirements_now 0)) ((replace_Znth (root) ((Znth child requirements_now 0)) (requirements_now)))) )
.

Definition sift_caves_partial_solve_wit_23 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (child: Z) (PreH1 : ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root_pre)) (PreH8 : (root_pre <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root_pre hi_pre child )) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre )) (PreH15 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full gain_pre n (replace_Znth (root_pre) ((Znth child gains_now 0)) (gains_now)) )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root_pre requirements_now 0)) ((replace_Znth (root_pre) ((Znth child requirements_now 0)) (requirements_now)))) )
|--
  “ ((Znth root_pre requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root_pre hi_pre child ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root_pre ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((gain_pre + (child * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i gain_pre child 0 n (replace_Znth (root_pre) ((Znth child gains_now 0)) (gains_now)) )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root_pre requirements_now 0)) ((replace_Znth (root_pre) ((Znth child requirements_now 0)) (requirements_now)))) )
.

Definition sift_caves_partial_solve_wit_24 := 
forall (hi_pre: Z) (root_pre: Z) (gain_pre: Z) (req_pre: Z) (n: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (child: Z) (PreH1 : ((Znth root requirements_now 0) < (Znth child requirements_now 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 100000)) (PreH4 : ((Zlength (requirements_now)) = n)) (PreH5 : ((Zlength (gains_now)) = n)) (PreH6 : (0 <= root_pre)) (PreH7 : (root_pre <= root)) (PreH8 : (root <= hi_pre)) (PreH9 : (hi_pre < n)) (PreH10 : (0 <= child)) (PreH11 : (child <= hi_pre)) (PreH12 : (SelectedLargerChild requirements_now root hi_pre child )) (PreH13 : ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0))) (PreH14 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH15 : (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root )) (PreH16 : ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements)))) (PreH17 : ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains)))) ,
  (Int64Array.full gain_pre n (replace_Znth (root) ((Znth child gains_now 0)) (gains_now)) )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root requirements_now 0)) ((replace_Znth (root) ((Znth child requirements_now 0)) (requirements_now)))) )
|--
  “ ((Znth root requirements_now 0) < (Znth child requirements_now 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n) ” 
  &&  “ ((Zlength (gains_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= hi_pre) ” 
  &&  “ (hi_pre < n) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= hi_pre) ” 
  &&  “ (SelectedLargerChild requirements_now root hi_pre child ) ” 
  &&  “ ((Znth child requirements_now 0) <= (Znth ((root - 1 ) ÷ 2 ) requirements_now 0)) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root_pre hi_pre root ) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (requirements_now)) = (sublist ((hi_pre + 1 )) (n) (requirements))) ” 
  &&  “ ((sublist ((hi_pre + 1 )) (n) (gains_now)) = (sublist ((hi_pre + 1 )) (n) (gains))) ”
  &&  (((gain_pre + (child * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i gain_pre child 0 n (replace_Znth (root) ((Znth child gains_now 0)) (gains_now)) )
  **  (Int64Array.full req_pre n (replace_Znth (child) ((Znth root requirements_now 0)) ((replace_Znth (root) ((Znth child requirements_now 0)) (requirements_now)))) )
.

(*----- Function sort_caves -----*)

Definition sort_caves_safety_wit_1 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
|--
  “ (((n_pre ÷ 2 ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre ÷ 2 ) - 1 )) ”
) \/
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
|--
  “ (((n_pre ÷ 2 ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre ÷ 2 ) - 1 )) ”
).

Definition sort_caves_safety_wit_1_split_goal_1 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
|--
  “ (((n_pre ÷ 2 ) - 1 ) <= INT_MAX) ”
.

Definition sort_caves_safety_wit_1_split_goal_2 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
|--
  “ ((INT_MIN) <= ((n_pre ÷ 2 ) - 1 )) ”
.

Definition sort_caves_safety_wit_2 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
|--
  “ ((n_pre <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition sort_caves_safety_wit_3 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sort_caves_safety_wit_4 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_caves_safety_wit_5 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : ((-1) <= root)) (PreH8 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH9 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH10 : (HeapParentsFrom requirements_now (root + 1 ) (n_pre - 1 ) )) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_caves_safety_wit_6 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : (0 <= root)) (PreH8 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH9 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH10 : (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root )) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition sort_caves_safety_wit_7 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : (0 <= root)) (PreH8 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH9 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH10 : (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root )) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_caves_safety_wit_8 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (gains_after: (@list Z)) (requirements_after: (@list Z)) (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements_now gains_now requirements_after gains_after )) (PreH4 : (HeapParentsFrom requirements_after root (n_pre - 1 ) )) (PreH5 : ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (requirements_after)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (requirements_now)))) (PreH6 : ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (gains_after)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (gains_now)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : ((Zlength (requirements)) = n_pre)) (PreH10 : ((Zlength (gains)) = n_pre)) (PreH11 : ((Zlength (requirements_now)) = n_pre)) (PreH12 : ((Zlength (gains_now)) = n_pre)) (PreH13 : (0 <= root)) (PreH14 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH15 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH16 : (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root )) ,
  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ ((root - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (root - 1 )) ”
.

Definition sort_caves_safety_wit_9 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (root < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : ((-1) <= root)) (PreH9 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH10 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH11 : (HeapParentsFrom requirements_now (root + 1 ) (n_pre - 1 ) )) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition sort_caves_safety_wit_10 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (root < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : ((-1) <= root)) (PreH9 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH10 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH11 : (HeapParentsFrom requirements_now (root + 1 ) (n_pre - 1 ) )) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_caves_safety_wit_11 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : (0 <= hi)) (PreH8 : (hi <= (n_pre - 1 ))) (PreH9 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_caves_safety_wit_12 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  ((( &( "t" ) )) # Int64  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_caves_safety_wit_13 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full req_pre n_pre requirements_now )
  **  ((( &( "t" ) )) # Int64  |-> (Znth 0 requirements_now 0))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_caves_safety_wit_14 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now 0)) ((replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)))) )
  **  ((( &( "t" ) )) # Int64  |-> (Znth 0 requirements_now 0))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_caves_safety_wit_15 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full gain_pre n_pre gains_now )
  **  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now 0)) ((replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)))) )
  **  ((( &( "t" ) )) # Int64  |-> (Znth 0 gains_now 0))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_caves_safety_wit_16 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (hi: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : (1 <= hi)) (PreH8 : (hi <= (n_pre - 1 ))) (PreH9 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH10 : (HeapOrderedExceptAtFrom requirements_now 0 (hi - 1 ) 0 )) (PreH11 : (increasing (sublist (hi) (n_pre) (requirements_now)) )) (PreH12 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now 0) <= (Znth q requirements_now 0)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
  **  ((( &( "t" ) )) # Int64  |->_)
|--
  “ ((hi - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hi - 1 )) ”
.

Definition sort_caves_safety_wit_17 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (hi: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : (1 <= hi)) (PreH8 : (hi <= (n_pre - 1 ))) (PreH9 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH10 : (HeapOrderedExceptAtFrom requirements_now 0 (hi - 1 ) 0 )) (PreH11 : (increasing (sublist (hi) (n_pre) (requirements_now)) )) (PreH12 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now 0) <= (Znth q requirements_now 0)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
  **  ((( &( "t" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_caves_safety_wit_18 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (hi: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : (1 <= hi)) (PreH8 : (hi <= (n_pre - 1 ))) (PreH9 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH10 : (HeapOrderedExceptAtFrom requirements_now 0 (hi - 1 ) 0 )) (PreH11 : (increasing (sublist (hi) (n_pre) (requirements_now)) )) (PreH12 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now 0) <= (Znth q requirements_now 0)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
  **  ((( &( "t" ) )) # Int64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_caves_safety_wit_19 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (hi: Z) (gains_after: (@list Z)) (requirements_after: (@list Z)) (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements_now gains_now requirements_after gains_after )) (PreH4 : (HeapParentsFrom requirements_after 0 (hi - 1 ) )) (PreH5 : ((sublist (((hi - 1 ) + 1 )) (n_pre) (requirements_after)) = (sublist (((hi - 1 ) + 1 )) (n_pre) (requirements_now)))) (PreH6 : ((sublist (((hi - 1 ) + 1 )) (n_pre) (gains_after)) = (sublist (((hi - 1 ) + 1 )) (n_pre) (gains_now)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : ((Zlength (requirements)) = n_pre)) (PreH10 : ((Zlength (gains)) = n_pre)) (PreH11 : ((Zlength (requirements_now)) = n_pre)) (PreH12 : ((Zlength (gains_now)) = n_pre)) (PreH13 : (1 <= hi)) (PreH14 : (hi <= (n_pre - 1 ))) (PreH15 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH16 : (HeapOrderedExceptAtFrom requirements_now 0 (hi - 1 ) 0 )) (PreH17 : (increasing (sublist (hi) (n_pre) (requirements_now)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now 0) <= (Znth q requirements_now 0)))) ,
  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ ((hi - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hi - 1 )) ”
.

Definition sort_caves_entail_wit_1 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
|--
  EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ ((-1) <= ((n_pre ÷ 2 ) - 1 )) ” 
  &&  “ (((n_pre ÷ 2 ) - 1 ) <= ((n_pre ÷ 2 ) - 1 )) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapParentsFrom requirements_now (((n_pre ÷ 2 ) - 1 ) + 1 ) (n_pre - 1 ) ) ”
  &&  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  TT && emp 
|--
  “ (HeapParentsFrom requirements (((n_pre ÷ 2 ) - 1 ) + 1 ) (n_pre - 1 ) ) ” 
  &&  “ (ParallelPermutation requirements gains requirements gains ) ” 
  &&  “ ((-1) <= ((n_pre ÷ 2 ) - 1 )) ”
  &&  emp
).

Definition sort_caves_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  (HeapParentsFrom requirements (((n_pre ÷ 2 ) - 1 ) + 1 ) (n_pre - 1 ) )
.

Definition sort_caves_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  (ParallelPermutation requirements gains requirements gains )
.

Definition sort_caves_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) ,
  ((-1) <= ((n_pre ÷ 2 ) - 1 ))
.

Definition sort_caves_entail_wit_2 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (root >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : ((-1) <= root)) (PreH9 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH10 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH11 : (HeapParentsFrom requirements_now_2 (root + 1 ) (n_pre - 1 ) )) ,
  (Int64Array.full req_pre n_pre requirements_now_2 )
  **  (Int64Array.full gain_pre n_pre gains_now_2 )
|--
  EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (root <= ((n_pre ÷ 2 ) - 1 )) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root ) ”
  &&  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (root >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : ((-1) <= root)) (PreH9 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH10 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH11 : (HeapParentsFrom requirements_now_2 (root + 1 ) (n_pre - 1 ) )) ,
  TT && emp 
|--
  “ (HeapOrderedExceptAtFrom requirements_now_2 root (n_pre - 1 ) root ) ”
  &&  emp
).

Definition sort_caves_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (root >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : ((-1) <= root)) (PreH9 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH10 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH11 : (HeapParentsFrom requirements_now_2 (root + 1 ) (n_pre - 1 ) )) ,
  (HeapOrderedExceptAtFrom requirements_now_2 root (n_pre - 1 ) root )
.

Definition sort_caves_entail_wit_3 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (gains_after: (@list Z)) (requirements_after: (@list Z)) (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements_now_2 gains_now_2 requirements_after gains_after )) (PreH4 : (HeapParentsFrom requirements_after root (n_pre - 1 ) )) (PreH5 : ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (requirements_after)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (requirements_now_2)))) (PreH6 : ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (gains_after)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (gains_now_2)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : ((Zlength (requirements)) = n_pre)) (PreH10 : ((Zlength (gains)) = n_pre)) (PreH11 : ((Zlength (requirements_now_2)) = n_pre)) (PreH12 : ((Zlength (gains_now_2)) = n_pre)) (PreH13 : (0 <= root)) (PreH14 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH15 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH16 : (HeapOrderedExceptAtFrom requirements_now_2 root (n_pre - 1 ) root )) ,
  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
|--
  EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ ((-1) <= (root - 1 )) ” 
  &&  “ ((root - 1 ) <= ((n_pre ÷ 2 ) - 1 )) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapParentsFrom requirements_now ((root - 1 ) + 1 ) (n_pre - 1 ) ) ”
  &&  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (gains_after: (@list Z)) (requirements_after: (@list Z)) (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements_now_2 gains_now_2 requirements_after gains_after )) (PreH4 : (HeapParentsFrom requirements_after root (n_pre - 1 ) )) (PreH5 : ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (requirements_after)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (requirements_now_2)))) (PreH6 : ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (gains_after)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (gains_now_2)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : ((Zlength (requirements)) = n_pre)) (PreH10 : ((Zlength (gains)) = n_pre)) (PreH11 : ((Zlength (requirements_now_2)) = n_pre)) (PreH12 : ((Zlength (gains_now_2)) = n_pre)) (PreH13 : (0 <= root)) (PreH14 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH15 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH16 : (HeapOrderedExceptAtFrom requirements_now_2 root (n_pre - 1 ) root )) ,
  TT && emp 
|--
  “ (HeapParentsFrom requirements_after ((root - 1 ) + 1 ) (n_pre - 1 ) ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_after gains_after ) ”
  &&  emp
).

Definition sort_caves_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (gains_after: (@list Z)) (requirements_after: (@list Z)) (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements_now_2 gains_now_2 requirements_after gains_after )) (PreH4 : (HeapParentsFrom requirements_after root (n_pre - 1 ) )) (PreH5 : ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (requirements_after)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (requirements_now_2)))) (PreH6 : ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (gains_after)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (gains_now_2)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : ((Zlength (requirements)) = n_pre)) (PreH10 : ((Zlength (gains)) = n_pre)) (PreH11 : ((Zlength (requirements_now_2)) = n_pre)) (PreH12 : ((Zlength (gains_now_2)) = n_pre)) (PreH13 : (0 <= root)) (PreH14 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH15 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH16 : (HeapOrderedExceptAtFrom requirements_now_2 root (n_pre - 1 ) root )) ,
  (HeapParentsFrom requirements_after ((root - 1 ) + 1 ) (n_pre - 1 ) )
.

Definition sort_caves_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (root: Z) (gains_after: (@list Z)) (requirements_after: (@list Z)) (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements_now_2 gains_now_2 requirements_after gains_after )) (PreH4 : (HeapParentsFrom requirements_after root (n_pre - 1 ) )) (PreH5 : ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (requirements_after)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (requirements_now_2)))) (PreH6 : ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (gains_after)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (gains_now_2)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : ((Zlength (requirements)) = n_pre)) (PreH10 : ((Zlength (gains)) = n_pre)) (PreH11 : ((Zlength (requirements_now_2)) = n_pre)) (PreH12 : ((Zlength (gains_now_2)) = n_pre)) (PreH13 : (0 <= root)) (PreH14 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH15 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH16 : (HeapOrderedExceptAtFrom requirements_now_2 root (n_pre - 1 ) root )) ,
  (ParallelPermutation requirements gains requirements_after gains_after )
.

Definition sort_caves_entail_wit_4 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (root < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : ((-1) <= root)) (PreH9 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH10 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH11 : (HeapParentsFrom requirements_now_2 (root + 1 ) (n_pre - 1 ) )) ,
  (Int64Array.full req_pre n_pre requirements_now_2 )
  **  (Int64Array.full gain_pre n_pre gains_now_2 )
|--
  EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) <= (n_pre - 1 )) ” 
  &&  “ (HeapSortState requirements gains requirements_now gains_now (n_pre - 1 ) ) ”
  &&  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (root < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : ((-1) <= root)) (PreH9 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH10 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH11 : (HeapParentsFrom requirements_now_2 (root + 1 ) (n_pre - 1 ) )) ,
  TT && emp 
|--
  “ (HeapSortState requirements gains requirements_now_2 gains_now_2 (n_pre - 1 ) ) ”
  &&  emp
).

Definition sort_caves_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (root: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (root < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : ((-1) <= root)) (PreH9 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH10 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH11 : (HeapParentsFrom requirements_now_2 (root + 1 ) (n_pre - 1 ) )) ,
  (HeapSortState requirements gains requirements_now_2 gains_now_2 (n_pre - 1 ) )
.

Definition sort_caves_entail_wit_5 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now_2 gains_now_2 hi )) ,
  (Int64Array.full gain_pre n_pre (replace_Znth (hi) ((Znth 0 gains_now_2 0)) ((replace_Znth (0) ((Znth hi gains_now_2 0)) (gains_now_2)))) )
  **  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))) )
  **  ((( &( "t" ) )) # Int64  |-> (Znth 0 gains_now_2 0))
|--
  EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (1 <= hi) ” 
  &&  “ (hi <= (n_pre - 1 )) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now 0 (hi - 1 ) 0 ) ” 
  &&  “ (increasing (sublist (hi) (n_pre) (requirements_now)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now 0) <= (Znth q requirements_now 0))) ”
  &&  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
  **  ((( &( "t" ) )) # Int64  |->_)
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now_2 gains_now_2 hi )) ,
  TT && emp 
|--
  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p (replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))) 0) <= (Znth q (replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))) 0))) ” 
  &&  “ (increasing (sublist (hi) (n_pre) ((replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))))) ) ” 
  &&  “ (HeapOrderedExceptAtFrom (replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))) 0 (hi - 1 ) 0 ) ” 
  &&  “ (ParallelPermutation requirements gains (replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))) (replace_Znth (hi) ((Znth 0 gains_now_2 0)) ((replace_Znth (0) ((Znth hi gains_now_2 0)) (gains_now_2)))) ) ” 
  &&  “ ((Zlength ((replace_Znth (hi) ((Znth 0 gains_now_2 0)) ((replace_Znth (0) ((Znth hi gains_now_2 0)) (gains_now_2)))))) = n_pre) ” 
  &&  “ ((Zlength ((replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))))) = n_pre) ”
  &&  emp
).

Definition sort_caves_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now_2 gains_now_2 hi )) ,
  forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p (replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))) 0) <= (Znth q (replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))) 0)))
.

Definition sort_caves_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now_2 gains_now_2 hi )) ,
  (increasing (sublist (hi) (n_pre) ((replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))))) )
.

Definition sort_caves_entail_wit_5_split_goal_3 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now_2 gains_now_2 hi )) ,
  (HeapOrderedExceptAtFrom (replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))) 0 (hi - 1 ) 0 )
.

Definition sort_caves_entail_wit_5_split_goal_4 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now_2 gains_now_2 hi )) ,
  (ParallelPermutation requirements gains (replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))) (replace_Znth (hi) ((Znth 0 gains_now_2 0)) ((replace_Znth (0) ((Znth hi gains_now_2 0)) (gains_now_2)))) )
.

Definition sort_caves_entail_wit_5_split_goal_5 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now_2 gains_now_2 hi )) ,
  ((Zlength ((replace_Znth (hi) ((Znth 0 gains_now_2 0)) ((replace_Znth (0) ((Znth hi gains_now_2 0)) (gains_now_2)))))) = n_pre)
.

Definition sort_caves_entail_wit_5_split_goal_6 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now_2: (@list Z)) (requirements_now_2: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now_2)) = n_pre)) (PreH7 : ((Zlength (gains_now_2)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now_2 gains_now_2 hi )) ,
  ((Zlength ((replace_Znth (hi) ((Znth 0 requirements_now_2 0)) ((replace_Znth (0) ((Znth hi requirements_now_2 0)) (requirements_now_2)))))) = n_pre)
.

Definition sort_caves_entail_wit_6 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (hi: Z) (gains_after: (@list Z)) (requirements_after: (@list Z)) (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements_now_2 gains_now_2 requirements_after gains_after )) (PreH4 : (HeapParentsFrom requirements_after 0 (hi - 1 ) )) (PreH5 : ((sublist (((hi - 1 ) + 1 )) (n_pre) (requirements_after)) = (sublist (((hi - 1 ) + 1 )) (n_pre) (requirements_now_2)))) (PreH6 : ((sublist (((hi - 1 ) + 1 )) (n_pre) (gains_after)) = (sublist (((hi - 1 ) + 1 )) (n_pre) (gains_now_2)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : ((Zlength (requirements)) = n_pre)) (PreH10 : ((Zlength (gains)) = n_pre)) (PreH11 : ((Zlength (requirements_now_2)) = n_pre)) (PreH12 : ((Zlength (gains_now_2)) = n_pre)) (PreH13 : (1 <= hi)) (PreH14 : (hi <= (n_pre - 1 ))) (PreH15 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH16 : (HeapOrderedExceptAtFrom requirements_now_2 0 (hi - 1 ) 0 )) (PreH17 : (increasing (sublist (hi) (n_pre) (requirements_now_2)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now_2 0) <= (Znth q requirements_now_2 0)))) ,
  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
|--
  EX (gains_now: (@list Z))  (requirements_now: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= (hi - 1 )) ” 
  &&  “ ((hi - 1 ) <= (n_pre - 1 )) ” 
  &&  “ (HeapSortState requirements gains requirements_now gains_now (hi - 1 ) ) ”
  &&  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (hi: Z) (gains_after: (@list Z)) (requirements_after: (@list Z)) (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements_now_2 gains_now_2 requirements_after gains_after )) (PreH4 : (HeapParentsFrom requirements_after 0 (hi - 1 ) )) (PreH5 : ((sublist (((hi - 1 ) + 1 )) (n_pre) (requirements_after)) = (sublist (((hi - 1 ) + 1 )) (n_pre) (requirements_now_2)))) (PreH6 : ((sublist (((hi - 1 ) + 1 )) (n_pre) (gains_after)) = (sublist (((hi - 1 ) + 1 )) (n_pre) (gains_now_2)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : ((Zlength (requirements)) = n_pre)) (PreH10 : ((Zlength (gains)) = n_pre)) (PreH11 : ((Zlength (requirements_now_2)) = n_pre)) (PreH12 : ((Zlength (gains_now_2)) = n_pre)) (PreH13 : (1 <= hi)) (PreH14 : (hi <= (n_pre - 1 ))) (PreH15 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH16 : (HeapOrderedExceptAtFrom requirements_now_2 0 (hi - 1 ) 0 )) (PreH17 : (increasing (sublist (hi) (n_pre) (requirements_now_2)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now_2 0) <= (Znth q requirements_now_2 0)))) ,
  TT && emp 
|--
  “ (HeapSortState requirements gains requirements_after gains_after (hi - 1 ) ) ”
  &&  emp
).

Definition sort_caves_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now_2: (@list Z)) (gains_now_2: (@list Z)) (hi: Z) (gains_after: (@list Z)) (requirements_after: (@list Z)) (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements_now_2 gains_now_2 requirements_after gains_after )) (PreH4 : (HeapParentsFrom requirements_after 0 (hi - 1 ) )) (PreH5 : ((sublist (((hi - 1 ) + 1 )) (n_pre) (requirements_after)) = (sublist (((hi - 1 ) + 1 )) (n_pre) (requirements_now_2)))) (PreH6 : ((sublist (((hi - 1 ) + 1 )) (n_pre) (gains_after)) = (sublist (((hi - 1 ) + 1 )) (n_pre) (gains_now_2)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : ((Zlength (requirements)) = n_pre)) (PreH10 : ((Zlength (gains)) = n_pre)) (PreH11 : ((Zlength (requirements_now_2)) = n_pre)) (PreH12 : ((Zlength (gains_now_2)) = n_pre)) (PreH13 : (1 <= hi)) (PreH14 : (hi <= (n_pre - 1 ))) (PreH15 : (ParallelPermutation requirements gains requirements_now_2 gains_now_2 )) (PreH16 : (HeapOrderedExceptAtFrom requirements_now_2 0 (hi - 1 ) 0 )) (PreH17 : (increasing (sublist (hi) (n_pre) (requirements_now_2)) )) (PreH18 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now_2 0) <= (Znth q requirements_now_2 0)))) ,
  (HeapSortState requirements gains requirements_after gains_after (hi - 1 ) )
.

Definition sort_caves_return_wit_1 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  EX (gains_after: (@list Z))  (requirements_after: (@list Z)) ,
  “ ((Zlength (requirements_after)) = n_pre) ” 
  &&  “ ((Zlength (gains_after)) = n_pre) ” 
  &&  “ (ParallelPermutation requirements gains requirements_after gains_after ) ” 
  &&  “ (increasing requirements_after ) ”
  &&  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  TT && emp 
|--
  “ (increasing requirements_now ) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ”
  &&  emp
).

Definition sort_caves_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (increasing requirements_now )
.

Definition sort_caves_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (ParallelPermutation requirements gains requirements_now gains_now )
.

Definition sort_caves_partial_solve_wit_1_pure := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : (0 <= root)) (PreH8 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH9 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH10 : (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root )) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root ) ” 
  &&  “ (root <= (n_pre - 1 )) ”
) \/
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (PreH1 : (root <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (root >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (requirements)) = n_pre)) (PreH8 : ((Zlength (gains)) = n_pre)) (PreH9 : ((Zlength (requirements_now)) = n_pre)) (PreH10 : ((Zlength (gains_now)) = n_pre)) (PreH11 : (0 <= root)) (PreH12 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root )) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (root <= (n_pre - 1 )) ”
).

Definition sort_caves_partial_solve_wit_1_pure_split_goal_1 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (PreH1 : (root <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (root >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (requirements)) = n_pre)) (PreH8 : ((Zlength (gains)) = n_pre)) (PreH9 : ((Zlength (requirements_now)) = n_pre)) (PreH10 : ((Zlength (gains_now)) = n_pre)) (PreH11 : (0 <= root)) (PreH12 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH13 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH14 : (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root )) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (root <= (n_pre - 1 )) ”
.

Definition sort_caves_partial_solve_wit_1_aux := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (root: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : (0 <= root)) (PreH8 : (root <= ((n_pre ÷ 2 ) - 1 ))) (PreH9 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH10 : (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root )) ,
  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root ) ” 
  &&  “ (root <= (n_pre - 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (root <= ((n_pre ÷ 2 ) - 1 )) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now root (n_pre - 1 ) root ) ”
  &&  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
.

Definition sort_caves_partial_solve_wit_1 := sort_caves_partial_solve_wit_1_pure -> sort_caves_partial_solve_wit_1_aux.

Definition sort_caves_partial_solve_wit_2 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (hi > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi <= (n_pre - 1 )) ” 
  &&  “ (HeapSortState requirements gains requirements_now gains_now hi ) ”
  &&  (((req_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 requirements_now 0))
  **  (Int64Array.missing_i req_pre 0 0 n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
.

Definition sort_caves_partial_solve_wit_3 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (hi > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi <= (n_pre - 1 )) ” 
  &&  “ (HeapSortState requirements gains requirements_now gains_now hi ) ”
  &&  (((req_pre + (hi * sizeof(INT64)))) # Int64  |-> (Znth hi requirements_now 0))
  **  (Int64Array.missing_i req_pre hi 0 n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
.

Definition sort_caves_partial_solve_wit_4 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (hi > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi <= (n_pre - 1 )) ” 
  &&  “ (HeapSortState requirements gains requirements_now gains_now hi ) ”
  &&  (((req_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i req_pre 0 0 n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
.

Definition sort_caves_partial_solve_wit_5 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full req_pre n_pre (replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)) )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (hi > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi <= (n_pre - 1 )) ” 
  &&  “ (HeapSortState requirements gains requirements_now gains_now hi ) ”
  &&  (((req_pre + (hi * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i req_pre hi 0 n_pre (replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)) )
  **  (Int64Array.full gain_pre n_pre gains_now )
.

Definition sort_caves_partial_solve_wit_6 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now 0)) ((replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)))) )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (hi > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi <= (n_pre - 1 )) ” 
  &&  “ (HeapSortState requirements gains requirements_now gains_now hi ) ”
  &&  (((gain_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 gains_now 0))
  **  (Int64Array.missing_i gain_pre 0 0 n_pre gains_now )
  **  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now 0)) ((replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)))) )
.

Definition sort_caves_partial_solve_wit_7 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full gain_pre n_pre gains_now )
  **  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now 0)) ((replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)))) )
|--
  “ (hi > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi <= (n_pre - 1 )) ” 
  &&  “ (HeapSortState requirements gains requirements_now gains_now hi ) ”
  &&  (((gain_pre + (hi * sizeof(INT64)))) # Int64  |-> (Znth hi gains_now 0))
  **  (Int64Array.missing_i gain_pre hi 0 n_pre gains_now )
  **  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now 0)) ((replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)))) )
.

Definition sort_caves_partial_solve_wit_8 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full gain_pre n_pre gains_now )
  **  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now 0)) ((replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)))) )
|--
  “ (hi > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi <= (n_pre - 1 )) ” 
  &&  “ (HeapSortState requirements gains requirements_now gains_now hi ) ”
  &&  (((gain_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i gain_pre 0 0 n_pre gains_now )
  **  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now 0)) ((replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)))) )
.

Definition sort_caves_partial_solve_wit_9 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (hi: Z) (gains_now: (@list Z)) (requirements_now: (@list Z)) (PreH1 : (hi > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (requirements)) = n_pre)) (PreH5 : ((Zlength (gains)) = n_pre)) (PreH6 : ((Zlength (requirements_now)) = n_pre)) (PreH7 : ((Zlength (gains_now)) = n_pre)) (PreH8 : (0 <= hi)) (PreH9 : (hi <= (n_pre - 1 ))) (PreH10 : (HeapSortState requirements gains requirements_now gains_now hi )) ,
  (Int64Array.full gain_pre n_pre (replace_Znth (0) ((Znth hi gains_now 0)) (gains_now)) )
  **  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now 0)) ((replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)))) )
|--
  “ (hi > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi <= (n_pre - 1 )) ” 
  &&  “ (HeapSortState requirements gains requirements_now gains_now hi ) ”
  &&  (((gain_pre + (hi * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i gain_pre hi 0 n_pre (replace_Znth (0) ((Znth hi gains_now 0)) (gains_now)) )
  **  (Int64Array.full req_pre n_pre (replace_Znth (hi) ((Znth 0 requirements_now 0)) ((replace_Znth (0) ((Znth hi requirements_now 0)) (requirements_now)))) )
.

Definition sort_caves_partial_solve_wit_10_pure := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (hi: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : (1 <= hi)) (PreH8 : (hi <= (n_pre - 1 ))) (PreH9 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH10 : (HeapOrderedExceptAtFrom requirements_now 0 (hi - 1 ) 0 )) (PreH11 : (increasing (sublist (hi) (n_pre) (requirements_now)) )) (PreH12 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now 0) <= (Znth q requirements_now 0)))) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
  **  ((( &( "t" ) )) # Int64  |->_)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (hi - 1 )) ” 
  &&  “ ((hi - 1 ) < n_pre) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now 0 (hi - 1 ) 0 ) ”
.

Definition sort_caves_partial_solve_wit_10_aux := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (requirements_now: (@list Z)) (gains_now: (@list Z)) (hi: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (requirements)) = n_pre)) (PreH4 : ((Zlength (gains)) = n_pre)) (PreH5 : ((Zlength (requirements_now)) = n_pre)) (PreH6 : ((Zlength (gains_now)) = n_pre)) (PreH7 : (1 <= hi)) (PreH8 : (hi <= (n_pre - 1 ))) (PreH9 : (ParallelPermutation requirements gains requirements_now gains_now )) (PreH10 : (HeapOrderedExceptAtFrom requirements_now 0 (hi - 1 ) 0 )) (PreH11 : (increasing (sublist (hi) (n_pre) (requirements_now)) )) (PreH12 : forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now 0) <= (Znth q requirements_now 0)))) ,
  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (hi - 1 )) ” 
  &&  “ ((hi - 1 ) < n_pre) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now 0 (hi - 1 ) 0 ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ ((Zlength (requirements_now)) = n_pre) ” 
  &&  “ ((Zlength (gains_now)) = n_pre) ” 
  &&  “ (1 <= hi) ” 
  &&  “ (hi <= (n_pre - 1 )) ” 
  &&  “ (ParallelPermutation requirements gains requirements_now gains_now ) ” 
  &&  “ (HeapOrderedExceptAtFrom requirements_now 0 (hi - 1 ) 0 ) ” 
  &&  “ (increasing (sublist (hi) (n_pre) (requirements_now)) ) ” 
  &&  “ forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < hi)) /\ (hi <= q)) /\ (q < n_pre)) -> ((Znth p requirements_now 0) <= (Znth q requirements_now 0))) ”
  &&  (Int64Array.full req_pre n_pre requirements_now )
  **  (Int64Array.full gain_pre n_pre gains_now )
.

Definition sort_caves_partial_solve_wit_10 := sort_caves_partial_solve_wit_10_pure -> sort_caves_partial_solve_wit_10_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (gains_after: (@list Z)) (requirements_after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements gains requirements_after gains_after )) (PreH4 : (increasing requirements_after )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH8 : ((Zlength ((concat (caves)))) <= 100000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH10 : (n_pre = (Zlength (caves)))) (PreH11 : ((Zlength (requirements)) = n_pre)) (PreH12 : ((Zlength (gains)) = n_pre)) (PreH13 : (CaveSummaryBridge caves requirements gains )) ,
  ((( &( "gained" ) )) # Int64  |->_)
  **  ((( &( "need" ) )) # Int64  |-> 0)
  **  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (gains_after: (@list Z)) (requirements_after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements gains requirements_after gains_after )) (PreH4 : (increasing requirements_after )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH8 : ((Zlength ((concat (caves)))) <= 100000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH10 : (n_pre = (Zlength (caves)))) (PreH11 : ((Zlength (requirements)) = n_pre)) (PreH12 : ((Zlength (gains)) = n_pre)) (PreH13 : (CaveSummaryBridge caves requirements gains )) ,
  ((( &( "need" ) )) # Int64  |->_)
  **  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (gains_after: (@list Z)) (requirements_after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements gains requirements_after gains_after )) (PreH4 : (increasing requirements_after )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH8 : ((Zlength ((concat (caves)))) <= 100000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH10 : (n_pre = (Zlength (caves)))) (PreH11 : ((Zlength (requirements)) = n_pre)) (PreH12 : ((Zlength (gains)) = n_pre)) (PreH13 : (CaveSummaryBridge caves requirements gains )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "gained" ) )) # Int64  |-> 0)
  **  ((( &( "need" ) )) # Int64  |-> 0)
  **  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (caves)))) (PreH5 : ((Zlength (requirements_sorted)) = n_pre)) (PreH6 : ((Zlength (gains_sorted)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= gained)) (PreH10 : (gained <= 100000)) (PreH11 : (0 <= need)) (PreH12 : (need <= 1000000001)) (PreH13 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH14 : (CaveInputBounds caves )) (PreH15 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH16 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH17 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  (Int64Array.full gain_pre n_pre gains_sorted )
|--
  “ (((Znth i requirements_sorted 0) - gained ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i requirements_sorted 0) - gained )) ”
) \/
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (caves)))) (PreH5 : ((Zlength (requirements_sorted)) = n_pre)) (PreH6 : ((Zlength (gains_sorted)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= gained)) (PreH10 : (gained <= 100000)) (PreH11 : (0 <= need)) (PreH12 : (need <= 1000000001)) (PreH13 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH14 : (CaveInputBounds caves )) (PreH15 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH16 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH17 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  (Int64Array.full gain_pre n_pre gains_sorted )
|--
  “ (((Znth i requirements_sorted 0) - gained ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i requirements_sorted 0) - gained )) ”
).

Definition solver_safety_wit_4_split_goal_1 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (caves)))) (PreH5 : ((Zlength (requirements_sorted)) = n_pre)) (PreH6 : ((Zlength (gains_sorted)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= gained)) (PreH10 : (gained <= 100000)) (PreH11 : (0 <= need)) (PreH12 : (need <= 1000000001)) (PreH13 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH14 : (CaveInputBounds caves )) (PreH15 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH16 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH17 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  (Int64Array.full gain_pre n_pre gains_sorted )
|--
  “ (((Znth i requirements_sorted 0) - gained ) <= INT64_MAX) ”
.

Definition solver_safety_wit_4_split_goal_2 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (caves)))) (PreH5 : ((Zlength (requirements_sorted)) = n_pre)) (PreH6 : ((Zlength (gains_sorted)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= gained)) (PreH10 : (gained <= 100000)) (PreH11 : (0 <= need)) (PreH12 : (need <= 1000000001)) (PreH13 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH14 : (CaveInputBounds caves )) (PreH15 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH16 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH17 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |->_)
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  (Int64Array.full gain_pre n_pre gains_sorted )
|--
  “ ((INT64_MIN) <= ((Znth i requirements_sorted 0) - gained )) ”
.

Definition solver_safety_wit_5 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
|--
  “ ((gained + (Znth i gains_sorted 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (gained + (Znth i gains_sorted 0) )) ”
) \/
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
|--
  “ ((gained + (Znth i gains_sorted 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (gained + (Znth i gains_sorted 0) )) ”
).

Definition solver_safety_wit_5_split_goal_1 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
|--
  “ ((gained + (Znth i gains_sorted 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_5_split_goal_2 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
|--
  “ ((INT64_MIN) <= (gained + (Znth i gains_sorted 0) )) ”
.

Definition solver_safety_wit_6 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> need)
|--
  “ ((gained + (Znth i gains_sorted 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (gained + (Znth i gains_sorted 0) )) ”
) \/
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> need)
|--
  “ ((gained + (Znth i gains_sorted 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (gained + (Znth i gains_sorted 0) )) ”
).

Definition solver_safety_wit_6_split_goal_1 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> need)
|--
  “ ((gained + (Znth i gains_sorted 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_6_split_goal_2 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "start" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> gained)
  **  ((( &( "need" ) )) # Int64  |-> need)
|--
  “ ((INT64_MIN) <= (gained + (Znth i gains_sorted 0) )) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> (gained + (Znth i gains_sorted 0) ))
  **  ((( &( "need" ) )) # Int64  |-> ((Znth i requirements_sorted 0) - gained ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "gained" ) )) # Int64  |-> (gained + (Znth i gains_sorted 0) ))
  **  ((( &( "need" ) )) # Int64  |-> need)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (gains_after: (@list Z)) (requirements_after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements gains requirements_after gains_after )) (PreH4 : (increasing requirements_after )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH8 : ((Zlength ((concat (caves)))) <= 100000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH10 : (n_pre = (Zlength (caves)))) (PreH11 : ((Zlength (requirements)) = n_pre)) (PreH12 : ((Zlength (gains)) = n_pre)) (PreH13 : (CaveSummaryBridge caves requirements gains )) ,
  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
|--
  EX (gains_sorted: (@list Z))  (requirements_sorted: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (caves))) ” 
  &&  “ ((Zlength (requirements_sorted)) = n_pre) ” 
  &&  “ ((Zlength (gains_sorted)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 100000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000001) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (gains_sorted))))) ” 
  &&  “ (CaveInputBounds caves ) ” 
  &&  “ (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted ) ” 
  &&  “ (CaveSummaryBounds requirements_sorted gains_sorted ) ” 
  &&  “ (GreedyNeed requirements_sorted gains_sorted 0 0 ) ”
  &&  (Int64Array.full req_pre n_pre requirements_sorted )
  **  (Int64Array.full gain_pre n_pre gains_sorted )
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (gains_after: (@list Z)) (requirements_after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements gains requirements_after gains_after )) (PreH4 : (increasing requirements_after )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH8 : ((Zlength ((concat (caves)))) <= 100000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH10 : (n_pre = (Zlength (caves)))) (PreH11 : ((Zlength (requirements)) = n_pre)) (PreH12 : ((Zlength (gains)) = n_pre)) (PreH13 : (CaveSummaryBridge caves requirements gains )) ,
  TT && emp 
|--
  “ (GreedyNeed requirements_after gains_after 0 0 ) ” 
  &&  “ (CaveSummaryBounds requirements_after gains_after ) ” 
  &&  “ (SortedCaveSummaries caves requirements gains requirements_after gains_after ) ” 
  &&  “ (CaveInputBounds caves ) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (gains_after))))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (gains_after: (@list Z)) (requirements_after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements gains requirements_after gains_after )) (PreH4 : (increasing requirements_after )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH8 : ((Zlength ((concat (caves)))) <= 100000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH10 : (n_pre = (Zlength (caves)))) (PreH11 : ((Zlength (requirements)) = n_pre)) (PreH12 : ((Zlength (gains)) = n_pre)) (PreH13 : (CaveSummaryBridge caves requirements gains )) ,
  (GreedyNeed requirements_after gains_after 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (gains_after: (@list Z)) (requirements_after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements gains requirements_after gains_after )) (PreH4 : (increasing requirements_after )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH8 : ((Zlength ((concat (caves)))) <= 100000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH10 : (n_pre = (Zlength (caves)))) (PreH11 : ((Zlength (requirements)) = n_pre)) (PreH12 : ((Zlength (gains)) = n_pre)) (PreH13 : (CaveSummaryBridge caves requirements gains )) ,
  (CaveSummaryBounds requirements_after gains_after )
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (gains_after: (@list Z)) (requirements_after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements gains requirements_after gains_after )) (PreH4 : (increasing requirements_after )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH8 : ((Zlength ((concat (caves)))) <= 100000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH10 : (n_pre = (Zlength (caves)))) (PreH11 : ((Zlength (requirements)) = n_pre)) (PreH12 : ((Zlength (gains)) = n_pre)) (PreH13 : (CaveSummaryBridge caves requirements gains )) ,
  (SortedCaveSummaries caves requirements gains requirements_after gains_after )
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (gains_after: (@list Z)) (requirements_after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements gains requirements_after gains_after )) (PreH4 : (increasing requirements_after )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH8 : ((Zlength ((concat (caves)))) <= 100000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH10 : (n_pre = (Zlength (caves)))) (PreH11 : ((Zlength (requirements)) = n_pre)) (PreH12 : ((Zlength (gains)) = n_pre)) (PreH13 : (CaveSummaryBridge caves requirements gains )) ,
  (CaveInputBounds caves )
.

Definition solver_entail_wit_1_split_goal_5 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (gains_after: (@list Z)) (requirements_after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (requirements_after)) = n_pre)) (PreH2 : ((Zlength (gains_after)) = n_pre)) (PreH3 : (ParallelPermutation requirements gains requirements_after gains_after )) (PreH4 : (increasing requirements_after )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH8 : ((Zlength ((concat (caves)))) <= 100000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH10 : (n_pre = (Zlength (caves)))) (PreH11 : ((Zlength (requirements)) = n_pre)) (PreH12 : ((Zlength (gains)) = n_pre)) (PreH13 : (CaveSummaryBridge caves requirements gains )) ,
  (0 = (sum ((sublist (0) (0) (gains_after)))))
.

Definition solver_entail_wit_2_1 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted_2 )
  **  (Int64Array.full req_pre n_pre requirements_sorted_2 )
|--
  EX (gains_sorted: (@list Z))  (requirements_sorted: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (caves))) ” 
  &&  “ ((Zlength (requirements_sorted)) = n_pre) ” 
  &&  “ ((Zlength (gains_sorted)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (gained + (Znth i gains_sorted_2 0) )) ” 
  &&  “ ((gained + (Znth i gains_sorted_2 0) ) <= 100000) ” 
  &&  “ (0 <= ((Znth i requirements_sorted_2 0) - gained )) ” 
  &&  “ (((Znth i requirements_sorted_2 0) - gained ) <= 1000000001) ” 
  &&  “ ((gained + (Znth i gains_sorted_2 0) ) = (sum ((sublist (0) ((i + 1 )) (gains_sorted))))) ” 
  &&  “ (CaveInputBounds caves ) ” 
  &&  “ (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted ) ” 
  &&  “ (CaveSummaryBounds requirements_sorted gains_sorted ) ” 
  &&  “ (GreedyNeed requirements_sorted gains_sorted (i + 1 ) ((Znth i requirements_sorted_2 0) - gained ) ) ”
  &&  (Int64Array.full req_pre n_pre requirements_sorted )
  **  (Int64Array.full gain_pre n_pre gains_sorted )
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  TT && emp 
|--
  “ (GreedyNeed requirements_sorted_2 gains_sorted_2 (i + 1 ) ((Znth i requirements_sorted_2 0) - gained ) ) ” 
  &&  “ ((gained + (Znth i gains_sorted_2 0) ) = (sum ((sublist (0) ((i + 1 )) (gains_sorted_2))))) ” 
  &&  “ (((Znth i requirements_sorted_2 0) - gained ) <= 1000000001) ” 
  &&  “ ((gained + (Znth i gains_sorted_2 0) ) <= 100000) ” 
  &&  “ (0 <= (gained + (Znth i gains_sorted_2 0) )) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  (GreedyNeed requirements_sorted_2 gains_sorted_2 (i + 1 ) ((Znth i requirements_sorted_2 0) - gained ) )
.

Definition solver_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  ((gained + (Znth i gains_sorted_2 0) ) = (sum ((sublist (0) ((i + 1 )) (gains_sorted_2)))))
.

Definition solver_entail_wit_2_1_split_goal_3 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  (((Znth i requirements_sorted_2 0) - gained ) <= 1000000001)
.

Definition solver_entail_wit_2_1_split_goal_4 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  ((gained + (Znth i gains_sorted_2 0) ) <= 100000)
.

Definition solver_entail_wit_2_1_split_goal_5 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  (0 <= (gained + (Znth i gains_sorted_2 0) ))
.

Definition solver_entail_wit_2_2 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  (Int64Array.full gain_pre n_pre gains_sorted_2 )
  **  (Int64Array.full req_pre n_pre requirements_sorted_2 )
|--
  EX (gains_sorted: (@list Z))  (requirements_sorted: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (caves))) ” 
  &&  “ ((Zlength (requirements_sorted)) = n_pre) ” 
  &&  “ ((Zlength (gains_sorted)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (gained + (Znth i gains_sorted_2 0) )) ” 
  &&  “ ((gained + (Znth i gains_sorted_2 0) ) <= 100000) ” 
  &&  “ (0 <= need) ” 
  &&  “ (need <= 1000000001) ” 
  &&  “ ((gained + (Znth i gains_sorted_2 0) ) = (sum ((sublist (0) ((i + 1 )) (gains_sorted))))) ” 
  &&  “ (CaveInputBounds caves ) ” 
  &&  “ (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted ) ” 
  &&  “ (CaveSummaryBounds requirements_sorted gains_sorted ) ” 
  &&  “ (GreedyNeed requirements_sorted gains_sorted (i + 1 ) need ) ”
  &&  (Int64Array.full req_pre n_pre requirements_sorted )
  **  (Int64Array.full gain_pre n_pre gains_sorted )
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  TT && emp 
|--
  “ (GreedyNeed requirements_sorted_2 gains_sorted_2 (i + 1 ) need ) ” 
  &&  “ ((gained + (Znth i gains_sorted_2 0) ) = (sum ((sublist (0) ((i + 1 )) (gains_sorted_2))))) ” 
  &&  “ ((gained + (Znth i gains_sorted_2 0) ) <= 100000) ” 
  &&  “ (0 <= (gained + (Znth i gains_sorted_2 0) )) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  (GreedyNeed requirements_sorted_2 gains_sorted_2 (i + 1 ) need )
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  ((gained + (Znth i gains_sorted_2 0) ) = (sum ((sublist (0) ((i + 1 )) (gains_sorted_2)))))
.

Definition solver_entail_wit_2_2_split_goal_3 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  ((gained + (Znth i gains_sorted_2 0) ) <= 100000)
.

Definition solver_entail_wit_2_2_split_goal_4 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted_2: (@list Z)) (requirements_sorted_2: (@list Z)) (PreH1 : (((Znth i requirements_sorted_2 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted_2)) = n_pre)) (PreH7 : ((Zlength (gains_sorted_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted_2)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted_2 gains_sorted_2 )) (PreH17 : (CaveSummaryBounds requirements_sorted_2 gains_sorted_2 )) (PreH18 : (GreedyNeed requirements_sorted_2 gains_sorted_2 i need )) ,
  (0 <= (gained + (Znth i gains_sorted_2 0) ))
.

Definition solver_entail_wit_3 := 
(
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (caves)))) (PreH5 : ((Zlength (requirements_sorted)) = n_pre)) (PreH6 : ((Zlength (gains_sorted)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= gained)) (PreH10 : (gained <= 100000)) (PreH11 : (0 <= need)) (PreH12 : (need <= 1000000001)) (PreH13 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH14 : (CaveInputBounds caves )) (PreH15 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH16 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH17 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  ((( &( "gained" ) )) # Int64  |-> gained)
  **  (Int64Array.full req_pre n_pre requirements_sorted )
  **  (Int64Array.full gain_pre n_pre gains_sorted )
|--
  EX (gains_after: (@list Z))  (requirements_after: (@list Z)) ,
  “ (Spec caves need ) ” 
  &&  “ ((Zlength (requirements_after)) = n_pre) ” 
  &&  “ ((Zlength (gains_after)) = n_pre) ”
  &&  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
  **  ((( &( "gained" ) )) # Int64  |->_)
) \/
(
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (caves)))) (PreH5 : ((Zlength (requirements_sorted)) = n_pre)) (PreH6 : ((Zlength (gains_sorted)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= gained)) (PreH10 : (gained <= 100000)) (PreH11 : (0 <= need)) (PreH12 : (need <= 1000000001)) (PreH13 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH14 : (CaveInputBounds caves )) (PreH15 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH16 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH17 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  TT && emp 
|--
  “ (Spec caves need ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (caves)))) (PreH5 : ((Zlength (requirements_sorted)) = n_pre)) (PreH6 : ((Zlength (gains_sorted)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= gained)) (PreH10 : (gained <= 100000)) (PreH11 : (0 <= need)) (PreH12 : (need <= 1000000001)) (PreH13 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH14 : (CaveInputBounds caves )) (PreH15 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH16 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH17 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Spec caves need )
.

Definition solver_return_wit_1 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (caves: (@list (@list Z))) (requirements_after: (@list Z)) (gains_after: (@list Z)) (need: Z) (PreH1 : (Spec caves need )) (PreH2 : ((Zlength (requirements_after)) = n_pre)) (PreH3 : ((Zlength (gains_after)) = n_pre)) ,
  (Int64Array.full req_pre n_pre requirements_after )
  **  (Int64Array.full gain_pre n_pre gains_after )
|--
  EX (gain_after: (@list Z))  (req_after: (@list Z)) ,
  “ (Spec caves need ) ” 
  &&  “ ((Zlength (req_after)) = n_pre) ” 
  &&  “ ((Zlength (gain_after)) = n_pre) ”
  &&  (Int64Array.full req_pre n_pre req_after )
  **  (Int64Array.full gain_pre n_pre gain_after )
.

Definition solver_partial_solve_wit_1_pure := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH4 : ((Zlength ((concat (caves)))) <= 100000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (caves)))) (PreH7 : ((Zlength (requirements)) = n_pre)) (PreH8 : ((Zlength (gains)) = n_pre)) (PreH9 : (CaveSummaryBridge caves requirements gains )) ,
  ((( &( "req" ) )) # Ptr  |-> req_pre)
  **  ((( &( "gain" ) )) # Ptr  |-> gain_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000)))) (PreH4 : ((Zlength ((concat (caves)))) <= 100000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (caves)))) (PreH7 : ((Zlength (requirements)) = n_pre)) (PreH8 : ((Zlength (gains)) = n_pre)) (PreH9 : (CaveSummaryBridge caves requirements gains )) ,
  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 < (Zlength ((Znth i caves __default__List_Z)))) /\ ((Zlength ((Znth i caves __default__List_Z))) <= 100000))) ” 
  &&  “ ((Zlength ((concat (caves)))) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength ((concat (caves)))))) -> ((1 <= (Znth k (concat (caves)) 0)) /\ ((Znth k (concat (caves)) 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (caves))) ” 
  &&  “ ((Zlength (requirements)) = n_pre) ” 
  &&  “ ((Zlength (gains)) = n_pre) ” 
  &&  “ (CaveSummaryBridge caves requirements gains ) ”
  &&  (Int64Array.full req_pre n_pre requirements )
  **  (Int64Array.full gain_pre n_pre gains )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (caves)))) (PreH5 : ((Zlength (requirements_sorted)) = n_pre)) (PreH6 : ((Zlength (gains_sorted)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= gained)) (PreH10 : (gained <= 100000)) (PreH11 : (0 <= need)) (PreH12 : (need <= 1000000001)) (PreH13 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH14 : (CaveInputBounds caves )) (PreH15 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH16 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH17 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full req_pre n_pre requirements_sorted )
  **  (Int64Array.full gain_pre n_pre gains_sorted )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (caves))) ” 
  &&  “ ((Zlength (requirements_sorted)) = n_pre) ” 
  &&  “ ((Zlength (gains_sorted)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= gained) ” 
  &&  “ (gained <= 100000) ” 
  &&  “ (0 <= need) ” 
  &&  “ (need <= 1000000001) ” 
  &&  “ (gained = (sum ((sublist (0) (i) (gains_sorted))))) ” 
  &&  “ (CaveInputBounds caves ) ” 
  &&  “ (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted ) ” 
  &&  “ (CaveSummaryBounds requirements_sorted gains_sorted ) ” 
  &&  “ (GreedyNeed requirements_sorted gains_sorted i need ) ”
  &&  (((req_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i requirements_sorted 0))
  **  (Int64Array.missing_i req_pre i 0 n_pre requirements_sorted )
  **  (Int64Array.full gain_pre n_pre gains_sorted )
.

Definition solver_partial_solve_wit_3 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) > need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full req_pre n_pre requirements_sorted )
  **  (Int64Array.full gain_pre n_pre gains_sorted )
|--
  “ (((Znth i requirements_sorted 0) - gained ) > need) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (caves))) ” 
  &&  “ ((Zlength (requirements_sorted)) = n_pre) ” 
  &&  “ ((Zlength (gains_sorted)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= gained) ” 
  &&  “ (gained <= 100000) ” 
  &&  “ (0 <= need) ” 
  &&  “ (need <= 1000000001) ” 
  &&  “ (gained = (sum ((sublist (0) (i) (gains_sorted))))) ” 
  &&  “ (CaveInputBounds caves ) ” 
  &&  “ (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted ) ” 
  &&  “ (CaveSummaryBounds requirements_sorted gains_sorted ) ” 
  &&  “ (GreedyNeed requirements_sorted gains_sorted i need ) ”
  &&  (((gain_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i gains_sorted 0))
  **  (Int64Array.missing_i gain_pre i 0 n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
.

Definition solver_partial_solve_wit_4 := 
forall (n_pre: Z) (gain_pre: Z) (req_pre: Z) (gains: (@list Z)) (requirements: (@list Z)) (caves: (@list (@list Z))) (need: Z) (gained: Z) (i: Z) (gains_sorted: (@list Z)) (requirements_sorted: (@list Z)) (PreH1 : (((Znth i requirements_sorted 0) - gained ) <= need)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (caves)))) (PreH6 : ((Zlength (requirements_sorted)) = n_pre)) (PreH7 : ((Zlength (gains_sorted)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= gained)) (PreH11 : (gained <= 100000)) (PreH12 : (0 <= need)) (PreH13 : (need <= 1000000001)) (PreH14 : (gained = (sum ((sublist (0) (i) (gains_sorted)))))) (PreH15 : (CaveInputBounds caves )) (PreH16 : (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted )) (PreH17 : (CaveSummaryBounds requirements_sorted gains_sorted )) (PreH18 : (GreedyNeed requirements_sorted gains_sorted i need )) ,
  (Int64Array.full req_pre n_pre requirements_sorted )
  **  (Int64Array.full gain_pre n_pre gains_sorted )
|--
  “ (((Znth i requirements_sorted 0) - gained ) <= need) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (caves))) ” 
  &&  “ ((Zlength (requirements_sorted)) = n_pre) ” 
  &&  “ ((Zlength (gains_sorted)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= gained) ” 
  &&  “ (gained <= 100000) ” 
  &&  “ (0 <= need) ” 
  &&  “ (need <= 1000000001) ” 
  &&  “ (gained = (sum ((sublist (0) (i) (gains_sorted))))) ” 
  &&  “ (CaveInputBounds caves ) ” 
  &&  “ (SortedCaveSummaries caves requirements gains requirements_sorted gains_sorted ) ” 
  &&  “ (CaveSummaryBounds requirements_sorted gains_sorted ) ” 
  &&  “ (GreedyNeed requirements_sorted gains_sorted i need ) ”
  &&  (((gain_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i gains_sorted 0))
  **  (Int64Array.missing_i gain_pre i 0 n_pre gains_sorted )
  **  (Int64Array.full req_pre n_pre requirements_sorted )
.

Module Type VC_Correct.


Axiom proof_of_sift_caves_safety_wit_1 : sift_caves_safety_wit_1.
Axiom proof_of_sift_caves_safety_wit_2 : sift_caves_safety_wit_2.
Axiom proof_of_sift_caves_safety_wit_3 : sift_caves_safety_wit_3.
Axiom proof_of_sift_caves_safety_wit_4 : sift_caves_safety_wit_4.
Axiom proof_of_sift_caves_safety_wit_5 : sift_caves_safety_wit_5.
Axiom proof_of_sift_caves_safety_wit_6 : sift_caves_safety_wit_6.
Axiom proof_of_sift_caves_safety_wit_7 : sift_caves_safety_wit_7.
Axiom proof_of_sift_caves_safety_wit_8 : sift_caves_safety_wit_8.
Axiom proof_of_sift_caves_safety_wit_9 : sift_caves_safety_wit_9.
Axiom proof_of_sift_caves_safety_wit_10 : sift_caves_safety_wit_10.
Axiom proof_of_sift_caves_safety_wit_11 : sift_caves_safety_wit_11.
Axiom proof_of_sift_caves_safety_wit_12 : sift_caves_safety_wit_12.
Axiom proof_of_sift_caves_safety_wit_13 : sift_caves_safety_wit_13.
Axiom proof_of_sift_caves_safety_wit_14 : sift_caves_safety_wit_14.
Axiom proof_of_sift_caves_safety_wit_15 : sift_caves_safety_wit_15.
Axiom proof_of_sift_caves_safety_wit_16 : sift_caves_safety_wit_16.
Axiom proof_of_sift_caves_safety_wit_17 : sift_caves_safety_wit_17.
Axiom proof_of_sift_caves_safety_wit_18 : sift_caves_safety_wit_18.
Axiom proof_of_sift_caves_safety_wit_19 : sift_caves_safety_wit_19.
Axiom proof_of_sift_caves_safety_wit_20 : sift_caves_safety_wit_20.
Axiom proof_of_sift_caves_safety_wit_21 : sift_caves_safety_wit_21.
Axiom proof_of_sift_caves_safety_wit_22 : sift_caves_safety_wit_22.
Axiom proof_of_sift_caves_safety_wit_23 : sift_caves_safety_wit_23.
Axiom proof_of_sift_caves_safety_wit_24 : sift_caves_safety_wit_24.
Axiom proof_of_sift_caves_safety_wit_25 : sift_caves_safety_wit_25.
Axiom proof_of_sift_caves_safety_wit_26 : sift_caves_safety_wit_26.
Axiom proof_of_sift_caves_entail_wit_1 : sift_caves_entail_wit_1.
Axiom proof_of_sift_caves_entail_wit_2_1 : sift_caves_entail_wit_2_1.
Axiom proof_of_sift_caves_entail_wit_2_2 : sift_caves_entail_wit_2_2.
Axiom proof_of_sift_caves_entail_wit_2_3 : sift_caves_entail_wit_2_3.
Axiom proof_of_sift_caves_entail_wit_2_4 : sift_caves_entail_wit_2_4.
Axiom proof_of_sift_caves_entail_wit_2_5 : sift_caves_entail_wit_2_5.
Axiom proof_of_sift_caves_entail_wit_2_6 : sift_caves_entail_wit_2_6.
Axiom proof_of_sift_caves_entail_wit_3_1 : sift_caves_entail_wit_3_1.
Axiom proof_of_sift_caves_entail_wit_3_2 : sift_caves_entail_wit_3_2.
Axiom proof_of_sift_caves_entail_wit_4_1 : sift_caves_entail_wit_4_1.
Axiom proof_of_sift_caves_entail_wit_4_2 : sift_caves_entail_wit_4_2.
Axiom proof_of_sift_caves_return_wit_1 : sift_caves_return_wit_1.
Axiom proof_of_sift_caves_return_wit_2 : sift_caves_return_wit_2.
Axiom proof_of_sift_caves_return_wit_3 : sift_caves_return_wit_3.
Axiom proof_of_sift_caves_return_wit_4 : sift_caves_return_wit_4.
Axiom proof_of_sift_caves_partial_solve_wit_1 : sift_caves_partial_solve_wit_1.
Axiom proof_of_sift_caves_partial_solve_wit_2 : sift_caves_partial_solve_wit_2.
Axiom proof_of_sift_caves_partial_solve_wit_3 : sift_caves_partial_solve_wit_3.
Axiom proof_of_sift_caves_partial_solve_wit_4 : sift_caves_partial_solve_wit_4.
Axiom proof_of_sift_caves_partial_solve_wit_5 : sift_caves_partial_solve_wit_5.
Axiom proof_of_sift_caves_partial_solve_wit_6 : sift_caves_partial_solve_wit_6.
Axiom proof_of_sift_caves_partial_solve_wit_7 : sift_caves_partial_solve_wit_7.
Axiom proof_of_sift_caves_partial_solve_wit_8 : sift_caves_partial_solve_wit_8.
Axiom proof_of_sift_caves_partial_solve_wit_9 : sift_caves_partial_solve_wit_9.
Axiom proof_of_sift_caves_partial_solve_wit_10 : sift_caves_partial_solve_wit_10.
Axiom proof_of_sift_caves_partial_solve_wit_11 : sift_caves_partial_solve_wit_11.
Axiom proof_of_sift_caves_partial_solve_wit_12 : sift_caves_partial_solve_wit_12.
Axiom proof_of_sift_caves_partial_solve_wit_13 : sift_caves_partial_solve_wit_13.
Axiom proof_of_sift_caves_partial_solve_wit_14 : sift_caves_partial_solve_wit_14.
Axiom proof_of_sift_caves_partial_solve_wit_15 : sift_caves_partial_solve_wit_15.
Axiom proof_of_sift_caves_partial_solve_wit_16 : sift_caves_partial_solve_wit_16.
Axiom proof_of_sift_caves_partial_solve_wit_17 : sift_caves_partial_solve_wit_17.
Axiom proof_of_sift_caves_partial_solve_wit_18 : sift_caves_partial_solve_wit_18.
Axiom proof_of_sift_caves_partial_solve_wit_19 : sift_caves_partial_solve_wit_19.
Axiom proof_of_sift_caves_partial_solve_wit_20 : sift_caves_partial_solve_wit_20.
Axiom proof_of_sift_caves_partial_solve_wit_21 : sift_caves_partial_solve_wit_21.
Axiom proof_of_sift_caves_partial_solve_wit_22 : sift_caves_partial_solve_wit_22.
Axiom proof_of_sift_caves_partial_solve_wit_23 : sift_caves_partial_solve_wit_23.
Axiom proof_of_sift_caves_partial_solve_wit_24 : sift_caves_partial_solve_wit_24.
Axiom proof_of_sort_caves_safety_wit_1 : sort_caves_safety_wit_1.
Axiom proof_of_sort_caves_safety_wit_2 : sort_caves_safety_wit_2.
Axiom proof_of_sort_caves_safety_wit_3 : sort_caves_safety_wit_3.
Axiom proof_of_sort_caves_safety_wit_4 : sort_caves_safety_wit_4.
Axiom proof_of_sort_caves_safety_wit_5 : sort_caves_safety_wit_5.
Axiom proof_of_sort_caves_safety_wit_6 : sort_caves_safety_wit_6.
Axiom proof_of_sort_caves_safety_wit_7 : sort_caves_safety_wit_7.
Axiom proof_of_sort_caves_safety_wit_8 : sort_caves_safety_wit_8.
Axiom proof_of_sort_caves_safety_wit_9 : sort_caves_safety_wit_9.
Axiom proof_of_sort_caves_safety_wit_10 : sort_caves_safety_wit_10.
Axiom proof_of_sort_caves_safety_wit_11 : sort_caves_safety_wit_11.
Axiom proof_of_sort_caves_safety_wit_12 : sort_caves_safety_wit_12.
Axiom proof_of_sort_caves_safety_wit_13 : sort_caves_safety_wit_13.
Axiom proof_of_sort_caves_safety_wit_14 : sort_caves_safety_wit_14.
Axiom proof_of_sort_caves_safety_wit_15 : sort_caves_safety_wit_15.
Axiom proof_of_sort_caves_safety_wit_16 : sort_caves_safety_wit_16.
Axiom proof_of_sort_caves_safety_wit_17 : sort_caves_safety_wit_17.
Axiom proof_of_sort_caves_safety_wit_18 : sort_caves_safety_wit_18.
Axiom proof_of_sort_caves_safety_wit_19 : sort_caves_safety_wit_19.
Axiom proof_of_sort_caves_entail_wit_1 : sort_caves_entail_wit_1.
Axiom proof_of_sort_caves_entail_wit_2 : sort_caves_entail_wit_2.
Axiom proof_of_sort_caves_entail_wit_3 : sort_caves_entail_wit_3.
Axiom proof_of_sort_caves_entail_wit_4 : sort_caves_entail_wit_4.
Axiom proof_of_sort_caves_entail_wit_5 : sort_caves_entail_wit_5.
Axiom proof_of_sort_caves_entail_wit_6 : sort_caves_entail_wit_6.
Axiom proof_of_sort_caves_return_wit_1 : sort_caves_return_wit_1.
Axiom proof_of_sort_caves_partial_solve_wit_1_pure : sort_caves_partial_solve_wit_1_pure.
Axiom proof_of_sort_caves_partial_solve_wit_1 : sort_caves_partial_solve_wit_1.
Axiom proof_of_sort_caves_partial_solve_wit_2 : sort_caves_partial_solve_wit_2.
Axiom proof_of_sort_caves_partial_solve_wit_3 : sort_caves_partial_solve_wit_3.
Axiom proof_of_sort_caves_partial_solve_wit_4 : sort_caves_partial_solve_wit_4.
Axiom proof_of_sort_caves_partial_solve_wit_5 : sort_caves_partial_solve_wit_5.
Axiom proof_of_sort_caves_partial_solve_wit_6 : sort_caves_partial_solve_wit_6.
Axiom proof_of_sort_caves_partial_solve_wit_7 : sort_caves_partial_solve_wit_7.
Axiom proof_of_sort_caves_partial_solve_wit_8 : sort_caves_partial_solve_wit_8.
Axiom proof_of_sort_caves_partial_solve_wit_9 : sort_caves_partial_solve_wit_9.
Axiom proof_of_sort_caves_partial_solve_wit_10_pure : sort_caves_partial_solve_wit_10_pure.
Axiom proof_of_sort_caves_partial_solve_wit_10 : sort_caves_partial_solve_wit_10.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.

End VC_Correct.
