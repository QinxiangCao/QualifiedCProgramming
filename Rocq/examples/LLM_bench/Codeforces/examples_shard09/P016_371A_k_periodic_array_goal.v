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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P016_371A_k_periodic_array_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (Pre k_pre values )) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i values 0) = 1) \/ ((Znth i values 0) = 2)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  ((( &( "changes" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (Pre k_pre values )) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i values 0) = 1) \/ ((Znth i values 0) = 2)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "changes" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (changes: Z) (r: Z) (PreH1 : (r < k_pre)) (PreH2 : (Pre k_pre values )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH8 : (0 <= r)) (PreH9 : (r <= k_pre)) (PreH10 : (0 <= changes)) (PreH11 : (changes <= n_pre)) (PreH12 : (PrefixCost k_pre r values changes )) ,
  ((( &( "twos" ) )) # Int  |->_)
  **  ((( &( "ones" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> changes)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (changes: Z) (r: Z) (PreH1 : (r < k_pre)) (PreH2 : (Pre k_pre values )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH8 : (0 <= r)) (PreH9 : (r <= k_pre)) (PreH10 : (0 <= changes)) (PreH11 : (changes <= n_pre)) (PreH12 : (PrefixCost k_pre r values changes )) ,
  ((( &( "ones" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> changes)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre k_pre values )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH8 : (0 <= r)) (PreH9 : (r < k_pre)) (PreH10 : (0 <= changes)) (PreH11 : (changes <= n_pre)) (PreH12 : (PrefixCost k_pre r values changes )) (PreH13 : (0 <= q)) (PreH14 : (i = (r + (q * k_pre ) ))) (PreH15 : (r <= i)) (PreH16 : (i <= (n_pre + r ))) (PreH17 : (0 <= ones)) (PreH18 : (0 <= twos)) (PreH19 : ((ones + twos ) <= n_pre)) (PreH20 : (ResidueScan k_pre r i values ones twos )) ,
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> changes)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ones" ) )) # Int  |-> ones)
  **  ((( &( "twos" ) )) # Int  |-> twos)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> changes)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ones" ) )) # Int  |-> ones)
  **  ((( &( "twos" ) )) # Int  |-> twos)
|--
  “ ((ones + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ones + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> changes)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ones" ) )) # Int  |-> ones)
  **  ((( &( "twos" ) )) # Int  |-> twos)
|--
  “ ((twos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (twos + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> changes)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ones" ) )) # Int  |-> (ones + 1 ))
  **  ((( &( "twos" ) )) # Int  |-> twos)
|--
  “ ((i + k_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + k_pre )) ”
.

Definition solver_safety_wit_9 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> changes)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ones" ) )) # Int  |-> ones)
  **  ((( &( "twos" ) )) # Int  |-> (twos + 1 ))
|--
  “ ((i + k_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + k_pre )) ”
.

Definition solver_safety_wit_10 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones >= twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> changes)
  **  ((( &( "ones" ) )) # Int  |-> ones)
  **  ((( &( "twos" ) )) # Int  |-> twos)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((changes + twos ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (changes + twos )) ”
.

Definition solver_safety_wit_11 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones < twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> changes)
  **  ((( &( "ones" ) )) # Int  |-> ones)
  **  ((( &( "twos" ) )) # Int  |-> twos)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((changes + ones ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (changes + ones )) ”
.

Definition solver_safety_wit_12 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones < twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> (changes + ones ))
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones >= twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "changes" ) )) # Int  |-> (changes + twos ))
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (Pre k_pre values )) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i values 0) = 1) \/ ((Znth i values 0) = 2)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  (IntArray.full a_pre n_pre values )
|--
  “ (Pre k_pre values ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (PrefixCost k_pre 0 values 0 ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (PreH1 : (Pre k_pre values )) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i values 0) = 1) \/ ((Znth i values 0) = 2)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  TT && emp 
|--
  “ (PrefixCost k_pre 0 values 0 ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (PreH1 : (Pre k_pre values )) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i values 0) = 1) \/ ((Znth i values 0) = 2)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  (PrefixCost k_pre 0 values 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (PreH1 : (Pre k_pre values )) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i values 0) = 1) \/ ((Znth i values 0) = 2)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))
.

Definition solver_entail_wit_2 := 
(
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (changes: Z) (r: Z) (PreH1 : (r < k_pre)) (PreH2 : (Pre k_pre values )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH8 : (0 <= r)) (PreH9 : (r <= k_pre)) (PreH10 : (0 <= changes)) (PreH11 : (changes <= n_pre)) (PreH12 : (PrefixCost k_pre r values changes )) ,
  (IntArray.full a_pre n_pre values )
|--
  EX (q: Z) ,
  “ (Pre k_pre values ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2))) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < k_pre) ” 
  &&  “ (0 <= changes) ” 
  &&  “ (changes <= n_pre) ” 
  &&  “ (PrefixCost k_pre r values changes ) ” 
  &&  “ (0 <= q) ” 
  &&  “ (r = (r + (q * k_pre ) )) ” 
  &&  “ (r <= r) ” 
  &&  “ (r <= (n_pre + r )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + 0 ) <= n_pre) ” 
  &&  “ (ResidueScan k_pre r r values 0 0 ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (changes: Z) (r: Z) (PreH1 : (r < k_pre)) (PreH2 : (Pre k_pre values )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH8 : (0 <= r)) (PreH9 : (r <= k_pre)) (PreH10 : (0 <= changes)) (PreH11 : (changes <= n_pre)) (PreH12 : (PrefixCost k_pre r values changes )) ,
  TT && emp 
|--
  EX (q: Z) ,
  “ (0 <= q) ” 
  &&  “ (r = (r + (q * k_pre ) )) ” 
  &&  “ (r <= r) ” 
  &&  “ (r <= ((Zlength (values)) + r )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + 0 ) <= (Zlength (values))) ” 
  &&  “ (ResidueScan k_pre r r values 0 0 ) ”
  &&  emp
).

Definition solver_entail_wit_3_1 := 
(
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q_2: Z) (changes: Z) (r: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q_2)) (PreH15 : (i = (r + (q_2 * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  (IntArray.full a_pre n_pre values )
|--
  EX (q: Z) ,
  “ (Pre k_pre values ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2))) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < k_pre) ” 
  &&  “ (0 <= changes) ” 
  &&  “ (changes <= n_pre) ” 
  &&  “ (PrefixCost k_pre r values changes ) ” 
  &&  “ (0 <= q) ” 
  &&  “ ((i + k_pre ) = (r + (q * k_pre ) )) ” 
  &&  “ (r <= (i + k_pre )) ” 
  &&  “ ((i + k_pre ) <= (n_pre + r )) ” 
  &&  “ (0 <= (ones + 1 )) ” 
  &&  “ (0 <= twos) ” 
  &&  “ (((ones + 1 ) + twos ) <= n_pre) ” 
  &&  “ (ResidueScan k_pre r (i + k_pre ) values (ones + 1 ) twos ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q_2: Z) (changes: Z) (r: Z) (PreH1 : ((Znth i values 0) = 1)) (PreH2 : (i < n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q_2)) (PreH15 : (i = (r + (q_2 * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  TT && emp 
|--
  EX (q: Z) ,
  “ (0 <= q) ” 
  &&  “ (((r + (q_2 * k_pre ) ) + k_pre ) = (r + (q * k_pre ) )) ” 
  &&  “ (r <= ((r + (q_2 * k_pre ) ) + k_pre )) ” 
  &&  “ (((r + (q_2 * k_pre ) ) + k_pre ) <= ((Zlength (values)) + r )) ” 
  &&  “ (0 <= (ones + 1 )) ” 
  &&  “ (((ones + 1 ) + twos ) <= (Zlength (values))) ” 
  &&  “ (ResidueScan k_pre r ((r + (q_2 * k_pre ) ) + k_pre ) values (ones + 1 ) twos ) ”
  &&  emp
).

Definition solver_entail_wit_3_2 := 
(
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q_2: Z) (changes: Z) (r: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q_2)) (PreH15 : (i = (r + (q_2 * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  (IntArray.full a_pre n_pre values )
|--
  EX (q: Z) ,
  “ (Pre k_pre values ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2))) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < k_pre) ” 
  &&  “ (0 <= changes) ” 
  &&  “ (changes <= n_pre) ” 
  &&  “ (PrefixCost k_pre r values changes ) ” 
  &&  “ (0 <= q) ” 
  &&  “ ((i + k_pre ) = (r + (q * k_pre ) )) ” 
  &&  “ (r <= (i + k_pre )) ” 
  &&  “ ((i + k_pre ) <= (n_pre + r )) ” 
  &&  “ (0 <= ones) ” 
  &&  “ (0 <= (twos + 1 )) ” 
  &&  “ ((ones + (twos + 1 ) ) <= n_pre) ” 
  &&  “ (ResidueScan k_pre r (i + k_pre ) values ones (twos + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q_2: Z) (changes: Z) (r: Z) (PreH1 : ((Znth i values 0) <> 1)) (PreH2 : (i < n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q_2)) (PreH15 : (i = (r + (q_2 * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  TT && emp 
|--
  EX (q: Z) ,
  “ (0 <= q) ” 
  &&  “ (((r + (q_2 * k_pre ) ) + k_pre ) = (r + (q * k_pre ) )) ” 
  &&  “ (r <= ((r + (q_2 * k_pre ) ) + k_pre )) ” 
  &&  “ (((r + (q_2 * k_pre ) ) + k_pre ) <= ((Zlength (values)) + r )) ” 
  &&  “ (0 <= (twos + 1 )) ” 
  &&  “ ((ones + (twos + 1 ) ) <= (Zlength (values))) ” 
  &&  “ (ResidueScan k_pre r ((r + (q_2 * k_pre ) ) + k_pre ) values ones (twos + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_4_1 := 
(
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones < twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  (IntArray.full a_pre n_pre values )
|--
  “ (Pre k_pre values ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2))) ” 
  &&  “ (0 <= (r + 1 )) ” 
  &&  “ ((r + 1 ) <= k_pre) ” 
  &&  “ (0 <= (changes + ones )) ” 
  &&  “ ((changes + ones ) <= n_pre) ” 
  &&  “ (PrefixCost k_pre (r + 1 ) values (changes + ones ) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones < twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  TT && emp 
|--
  “ (PrefixCost k_pre (r + 1 ) values (changes + ones ) ) ” 
  &&  “ ((changes + ones ) <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2))) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones < twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  (PrefixCost k_pre (r + 1 ) values (changes + ones ) )
.

Definition solver_entail_wit_4_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones < twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  ((changes + ones ) <= n_pre)
.

Definition solver_entail_wit_4_1_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones < twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))
.

Definition solver_entail_wit_4_2 := 
(
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones >= twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  (IntArray.full a_pre n_pre values )
|--
  “ (Pre k_pre values ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2))) ” 
  &&  “ (0 <= (r + 1 )) ” 
  &&  “ ((r + 1 ) <= k_pre) ” 
  &&  “ (0 <= (changes + twos )) ” 
  &&  “ ((changes + twos ) <= n_pre) ” 
  &&  “ (PrefixCost k_pre (r + 1 ) values (changes + twos ) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones >= twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  TT && emp 
|--
  “ (PrefixCost k_pre (r + 1 ) values (changes + twos ) ) ” 
  &&  “ ((changes + twos ) <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2))) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones >= twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  (PrefixCost k_pre (r + 1 ) values (changes + twos ) )
.

Definition solver_entail_wit_4_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones >= twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  ((changes + twos ) <= n_pre)
.

Definition solver_entail_wit_4_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (ones >= twos)) (PreH2 : (i >= n_pre)) (PreH3 : (Pre k_pre values )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 values 0) = 1) \/ ((Znth j_2 values 0) = 2)))) (PreH9 : (0 <= r)) (PreH10 : (r < k_pre)) (PreH11 : (0 <= changes)) (PreH12 : (changes <= n_pre)) (PreH13 : (PrefixCost k_pre r values changes )) (PreH14 : (0 <= q)) (PreH15 : (i = (r + (q * k_pre ) ))) (PreH16 : (r <= i)) (PreH17 : (i <= (n_pre + r ))) (PreH18 : (0 <= ones)) (PreH19 : (0 <= twos)) (PreH20 : ((ones + twos ) <= n_pre)) (PreH21 : (ResidueScan k_pre r i values ones twos )) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))
.

Definition solver_return_wit_1 := 
(
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (changes: Z) (r: Z) (PreH1 : (r >= k_pre)) (PreH2 : (Pre k_pre values )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH8 : (0 <= r)) (PreH9 : (r <= k_pre)) (PreH10 : (0 <= changes)) (PreH11 : (changes <= n_pre)) (PreH12 : (PrefixCost k_pre r values changes )) ,
  (IntArray.full a_pre n_pre values )
|--
  “ (Spec k_pre values changes ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (changes: Z) (r: Z) (PreH1 : (r >= k_pre)) (PreH2 : (Pre k_pre values )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH8 : (0 <= r)) (PreH9 : (r <= k_pre)) (PreH10 : (0 <= changes)) (PreH11 : (changes <= n_pre)) (PreH12 : (PrefixCost k_pre r values changes )) ,
  TT && emp 
|--
  “ (Spec k_pre values changes ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (changes: Z) (r: Z) (PreH1 : (r >= k_pre)) (PreH2 : (Pre k_pre values )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH8 : (0 <= r)) (PreH9 : (r <= k_pre)) (PreH10 : (0 <= changes)) (PreH11 : (changes <= n_pre)) (PreH12 : (PrefixCost k_pre r values changes )) ,
  (Spec k_pre values changes )
.

Definition solver_partial_solve_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (twos: Z) (ones: Z) (i: Z) (q: Z) (changes: Z) (r: Z) (PreH1 : (i < n_pre)) (PreH2 : (Pre k_pre values )) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2)))) (PreH8 : (0 <= r)) (PreH9 : (r < k_pre)) (PreH10 : (0 <= changes)) (PreH11 : (changes <= n_pre)) (PreH12 : (PrefixCost k_pre r values changes )) (PreH13 : (0 <= q)) (PreH14 : (i = (r + (q * k_pre ) ))) (PreH15 : (r <= i)) (PreH16 : (i <= (n_pre + r ))) (PreH17 : (0 <= ones)) (PreH18 : (0 <= twos)) (PreH19 : ((ones + twos ) <= n_pre)) (PreH20 : (ResidueScan k_pre r i values ones twos )) ,
  (IntArray.full a_pre n_pre values )
|--
  “ (i < n_pre) ” 
  &&  “ (Pre k_pre values ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j values 0) = 1) \/ ((Znth j values 0) = 2))) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < k_pre) ” 
  &&  “ (0 <= changes) ” 
  &&  “ (changes <= n_pre) ” 
  &&  “ (PrefixCost k_pre r values changes ) ” 
  &&  “ (0 <= q) ” 
  &&  “ (i = (r + (q * k_pre ) )) ” 
  &&  “ (r <= i) ” 
  &&  “ (i <= (n_pre + r )) ” 
  &&  “ (0 <= ones) ” 
  &&  “ (0 <= twos) ” 
  &&  “ ((ones + twos ) <= n_pre) ” 
  &&  “ (ResidueScan k_pre r i values ones twos ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
