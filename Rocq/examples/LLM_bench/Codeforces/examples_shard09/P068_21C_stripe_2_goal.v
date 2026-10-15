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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P068_21C_stripe_2_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (total = (PrefixSum (values) (i)))) (PreH9 : (((-10000) * i ) <= total)) (PreH10 : (total <= (10000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> (total + (Znth i values 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (total = (PrefixSum (values) (i)))) (PreH9 : (((-10000) * i ) <= total)) (PreH10 : (total <= (10000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + (Znth i values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + (Znth i values 0) )) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (total = (PrefixSum (values) (i)))) (PreH9 : (((-10000) * i ) <= total)) (PreH10 : (total <= (10000 * i ))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((total <> (INT64_MIN)) \/ (3 <> (-1))) ” 
  &&  “ (3 <> 0) ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (total = (PrefixSum (values) (i)))) (PreH9 : (((-10000) * i ) <= total)) (PreH10 : (total <= (10000 * i ))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (total = (PrefixSum (values) (i)))) (PreH9 : (((-10000) * i ) <= total)) (PreH10 : (total <= (10000 * i ))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (values)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH5 : (total = (PrefixSum (values) (n_pre)))) (PreH6 : (Spec values 0 )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  ((( &( "ways" ) )) # Int64  |->_)
  **  ((( &( "first" ) )) # Int64  |-> 0)
  **  ((( &( "run" ) )) # Int64  |-> 0)
  **  ((( &( "third" ) )) # Int64  |-> (total ÷ 3 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  ((( &( "first" ) )) # Int64  |->_)
  **  ((( &( "run" ) )) # Int64  |-> 0)
  **  ((( &( "third" ) )) # Int64  |-> (total ÷ 3 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  ((( &( "run" ) )) # Int64  |->_)
  **  ((( &( "third" ) )) # Int64  |-> (total ÷ 3 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  ((( &( "third" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((total <> (INT64_MIN)) \/ (3 <> (-1))) ” 
  &&  “ (3 <> 0) ”
.

Definition solver_safety_wit_13 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  ((( &( "third" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_14 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ways" ) )) # Int64  |-> 0)
  **  ((( &( "first" ) )) # Int64  |-> 0)
  **  ((( &( "run" ) )) # Int64  |-> 0)
  **  ((( &( "third" ) )) # Int64  |-> (total ÷ 3 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (values)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH5 : (total = (PrefixSum (values) (n_pre)))) (PreH6 : (total = (3 * third ))) (PreH7 : (((-10000) * n_pre ) <= total)) (PreH8 : (total <= (10000 * n_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (run = (PrefixSum (values) (i)))) (PreH12 : (first = (FirstCutCount (values) (third) (i)))) (PreH13 : (ways = (ValidPairCount (values) (third) (i)))) (PreH14 : (((-10000) * i ) <= run)) (PreH15 : (run <= (10000 * i ))) (PreH16 : (0 <= first)) (PreH17 : (first <= i)) (PreH18 : (0 <= ways)) (PreH19 : (ways <= (100000 * i ))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (values)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH5 : (total = (PrefixSum (values) (n_pre)))) (PreH6 : (total = (3 * third ))) (PreH7 : (((-10000) * n_pre ) <= total)) (PreH8 : (total <= (10000 * n_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (run = (PrefixSum (values) (i)))) (PreH12 : (first = (FirstCutCount (values) (third) (i)))) (PreH13 : (ways = (ValidPairCount (values) (third) (i)))) (PreH14 : (((-10000) * i ) <= run)) (PreH15 : (run <= (10000 * i ))) (PreH16 : (0 <= first)) (PreH17 : (first <= i)) (PreH18 : (0 <= ways)) (PreH19 : (ways <= (100000 * i ))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (total = (PrefixSum (values) (n_pre)))) (PreH7 : (total = (3 * third ))) (PreH8 : (((-10000) * n_pre ) <= total)) (PreH9 : (total <= (10000 * n_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (run = (PrefixSum (values) (i)))) (PreH13 : (first = (FirstCutCount (values) (third) (i)))) (PreH14 : (ways = (ValidPairCount (values) (third) (i)))) (PreH15 : (((-10000) * i ) <= run)) (PreH16 : (run <= (10000 * i ))) (PreH17 : (0 <= first)) (PreH18 : (first <= i)) (PreH19 : (0 <= ways)) (PreH20 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ ((run + (Znth i values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (run + (Znth i values 0) )) ”
.

Definition solver_safety_wit_18 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (total = (PrefixSum (values) (n_pre)))) (PreH7 : (total = (3 * third ))) (PreH8 : (((-10000) * n_pre ) <= total)) (PreH9 : (total <= (10000 * n_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (run = (PrefixSum (values) (i)))) (PreH13 : (first = (FirstCutCount (values) (third) (i)))) (PreH14 : (ways = (ValidPairCount (values) (third) (i)))) (PreH15 : (((-10000) * i ) <= run)) (PreH16 : (run <= (10000 * i ))) (PreH17 : (0 <= first)) (PreH18 : (first <= i)) (PreH19 : (0 <= ways)) (PreH20 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : (i >= 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH7 : (total = (PrefixSum (values) (n_pre)))) (PreH8 : (total = (3 * third ))) (PreH9 : (((-10000) * n_pre ) <= total)) (PreH10 : (total <= (10000 * n_pre ))) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (run = (PrefixSum (values) (i)))) (PreH14 : (first = (FirstCutCount (values) (third) (i)))) (PreH15 : (ways = (ValidPairCount (values) (third) (i)))) (PreH16 : (((-10000) * i ) <= run)) (PreH17 : (run <= (10000 * i ))) (PreH18 : (0 <= first)) (PreH19 : (first <= i)) (PreH20 : (0 <= ways)) (PreH21 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ ((2 * third ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * third )) ”
.

Definition solver_safety_wit_20 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : (i >= 1)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH7 : (total = (PrefixSum (values) (n_pre)))) (PreH8 : (total = (3 * third ))) (PreH9 : (((-10000) * n_pre ) <= total)) (PreH10 : (total <= (10000 * n_pre ))) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre - 1 ))) (PreH13 : (run = (PrefixSum (values) (i)))) (PreH14 : (first = (FirstCutCount (values) (third) (i)))) (PreH15 : (ways = (ValidPairCount (values) (third) (i)))) (PreH16 : (((-10000) * i ) <= run)) (PreH17 : (run <= (10000 * i ))) (PreH18 : (0 <= first)) (PreH19 : (first <= i)) (PreH20 : (0 <= ways)) (PreH21 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_21 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH2 : (i >= 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ ((ways + first ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (ways + first )) ”
.

Definition solver_safety_wit_22 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> (ways + first ))
|--
  “ ((first + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (first + 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ ((first + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (first + 1 )) ”
.

Definition solver_safety_wit_24 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ ((first + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (first + 1 )) ”
.

Definition solver_safety_wit_25 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> (first + 1 ))
  **  ((( &( "ways" ) )) # Int64  |-> (ways + first ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_26 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> (first + 1 ))
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_27 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> (first + 1 ))
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_28 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> (ways + first ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "third" ) )) # Int64  |-> third)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "run" ) )) # Int64  |-> (run + (Znth i values 0) ))
  **  ((( &( "first" ) )) # Int64  |-> first)
  **  ((( &( "ways" ) )) # Int64  |-> ways)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (PrefixSum (values) (0))) ” 
  &&  “ (((-10000) * 0 ) <= 0) ” 
  &&  “ (0 <= (10000 * 0 )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  TT && emp 
|--
  “ (0 = (PrefixSum (values) (0))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  (0 = (PrefixSum (values) (0)))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((-10000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 10000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))
.

Definition solver_entail_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (total = (PrefixSum (values) (i)))) (PreH9 : (((-10000) * i ) <= total)) (PreH10 : (total <= (10000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((total + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 )))) ” 
  &&  “ (((-10000) * (i + 1 ) ) <= (total + (Znth i values 0) )) ” 
  &&  “ ((total + (Znth i values 0) ) <= (10000 * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (total = (PrefixSum (values) (i)))) (PreH9 : (((-10000) * i ) <= total)) (PreH10 : (total <= (10000 * i ))) ,
  TT && emp 
|--
  “ (((-10000) * (i + 1 ) ) <= (total + (Znth i values 0) )) ” 
  &&  “ ((total + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (total = (PrefixSum (values) (i)))) (PreH9 : (((-10000) * i ) <= total)) (PreH10 : (total <= (10000 * i ))) ,
  (((-10000) * (i + 1 ) ) <= (total + (Znth i values 0) ))
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (total = (PrefixSum (values) (i)))) (PreH9 : (((-10000) * i ) <= total)) (PreH10 : (total <= (10000 * i ))) ,
  ((total + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 ))))
.

Definition solver_entail_wit_3 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) <> 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ (Spec values 0 ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) <> 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  TT && emp 
|--
  “ (Spec values 0 ) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) <> 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  (Spec values 0 )
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) <> 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  (total = (PrefixSum (values) (n_pre)))
.

Definition solver_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) <> 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))
.

Definition solver_entail_wit_4 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ (total = (3 * (total ÷ 3 ) )) ” 
  &&  “ (((-10000) * n_pre ) <= total) ” 
  &&  “ (total <= (10000 * n_pre )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ (0 = (PrefixSum (values) (0))) ” 
  &&  “ (0 = (FirstCutCount (values) ((total ÷ 3 )) (0))) ” 
  &&  “ (0 = (ValidPairCount (values) ((total ÷ 3 )) (0))) ” 
  &&  “ (((-10000) * 0 ) <= 0) ” 
  &&  “ (0 <= (10000 * 0 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (100000 * 0 )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  TT && emp 
|--
  “ (0 = (ValidPairCount (values) ((total ÷ 3 )) (0))) ” 
  &&  “ (0 = (FirstCutCount (values) ((total ÷ 3 )) (0))) ” 
  &&  “ (0 = (PrefixSum (values) (0))) ” 
  &&  “ (((-10000) * n_pre ) <= total) ” 
  &&  “ (total = (3 * (total ÷ 3 ) )) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  (0 = (ValidPairCount (values) ((total ÷ 3 )) (0)))
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  (0 = (FirstCutCount (values) ((total ÷ 3 )) (0)))
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  (0 = (PrefixSum (values) (0)))
.

Definition solver_entail_wit_4_split_goal_4 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  (((-10000) * n_pre ) <= total)
.

Definition solver_entail_wit_4_split_goal_5 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  (total = (3 * (total ÷ 3 ) ))
.

Definition solver_entail_wit_4_split_goal_6 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  (total = (PrefixSum (values) (n_pre)))
.

Definition solver_entail_wit_4_split_goal_7 := 
forall (n_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : ((total % ( 3 ) ) = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (values)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((-10000) <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (total = (PrefixSum (values) (i)))) (PreH10 : (((-10000) * i ) <= total)) (PreH11 : (total <= (10000 * i ))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))
.

Definition solver_entail_wit_5_1 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ (total = (3 * third )) ” 
  &&  “ (((-10000) * n_pre ) <= total) ” 
  &&  “ (total <= (10000 * n_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((run + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 )))) ” 
  &&  “ ((first + 1 ) = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ ((ways + first ) = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ (((-10000) * (i + 1 ) ) <= (run + (Znth i values 0) )) ” 
  &&  “ ((run + (Znth i values 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= (first + 1 )) ” 
  &&  “ ((first + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= (ways + first )) ” 
  &&  “ ((ways + first ) <= (100000 * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  TT && emp 
|--
  “ ((ways + first ) = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ ((first + 1 ) = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ (third = (PrefixSum (values) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  ((ways + first ) = (ValidPairCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_1_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  ((first + 1 ) = (FirstCutCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_1_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (third = (PrefixSum (values) ((i + 1 ))))
.

Definition solver_entail_wit_5_2 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ (total = (3 * third )) ” 
  &&  “ (((-10000) * n_pre ) <= total) ” 
  &&  “ (total <= (10000 * n_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((run + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 )))) ” 
  &&  “ ((first + 1 ) = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ (ways = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ (((-10000) * (i + 1 ) ) <= (run + (Znth i values 0) )) ” 
  &&  “ ((run + (Znth i values 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= (first + 1 )) ” 
  &&  “ ((first + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= ways) ” 
  &&  “ (ways <= (100000 * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  TT && emp 
|--
  “ (third <= (10000 * (i + 1 ) )) ” 
  &&  “ (((-10000) * (i + 1 ) ) <= third) ” 
  &&  “ (ways = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ ((first + 1 ) = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ (third = (PrefixSum (values) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_5_2_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (third <= (10000 * (i + 1 ) ))
.

Definition solver_entail_wit_5_2_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (((-10000) * (i + 1 ) ) <= third)
.

Definition solver_entail_wit_5_2_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (ways = (ValidPairCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_2_split_goal_4 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  ((first + 1 ) = (FirstCutCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_2_split_goal_5 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (third = (PrefixSum (values) ((i + 1 ))))
.

Definition solver_entail_wit_5_3 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ (total = (3 * third )) ” 
  &&  “ (((-10000) * n_pre ) <= total) ” 
  &&  “ (total <= (10000 * n_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((run + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 )))) ” 
  &&  “ ((first + 1 ) = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ (ways = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ (((-10000) * (i + 1 ) ) <= (run + (Znth i values 0) )) ” 
  &&  “ ((run + (Znth i values 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= (first + 1 )) ” 
  &&  “ ((first + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= ways) ” 
  &&  “ (ways <= (100000 * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  TT && emp 
|--
  “ (third <= (10000 * (i + 1 ) )) ” 
  &&  “ (((-10000) * (i + 1 ) ) <= third) ” 
  &&  “ (ways = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ ((first + 1 ) = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ (third = (PrefixSum (values) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_5_3_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (third <= (10000 * (i + 1 ) ))
.

Definition solver_entail_wit_5_3_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (((-10000) * (i + 1 ) ) <= third)
.

Definition solver_entail_wit_5_3_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (ways = (ValidPairCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_3_split_goal_4 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  ((first + 1 ) = (FirstCutCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_3_split_goal_5 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) = third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (third = (PrefixSum (values) ((i + 1 ))))
.

Definition solver_entail_wit_5_4 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ (total = (3 * third )) ” 
  &&  “ (((-10000) * n_pre ) <= total) ” 
  &&  “ (total <= (10000 * n_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((run + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 )))) ” 
  &&  “ (first = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ ((ways + first ) = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ (((-10000) * (i + 1 ) ) <= (run + (Znth i values 0) )) ” 
  &&  “ ((run + (Znth i values 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first <= (i + 1 )) ” 
  &&  “ (0 <= (ways + first )) ” 
  &&  “ ((ways + first ) <= (100000 * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  TT && emp 
|--
  “ ((2 * third ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (((-10000) * (i + 1 ) ) <= (2 * third )) ” 
  &&  “ ((ways + first ) = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ (first = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ ((2 * third ) = (PrefixSum (values) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_5_4_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  ((2 * third ) <= (10000 * (i + 1 ) ))
.

Definition solver_entail_wit_5_4_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (((-10000) * (i + 1 ) ) <= (2 * third ))
.

Definition solver_entail_wit_5_4_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  ((ways + first ) = (ValidPairCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_4_split_goal_4 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (first = (FirstCutCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_4_split_goal_5 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) = (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  ((2 * third ) = (PrefixSum (values) ((i + 1 ))))
.

Definition solver_entail_wit_5_5 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ (total = (3 * third )) ” 
  &&  “ (((-10000) * n_pre ) <= total) ” 
  &&  “ (total <= (10000 * n_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((run + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 )))) ” 
  &&  “ (first = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ (ways = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ (((-10000) * (i + 1 ) ) <= (run + (Znth i values 0) )) ” 
  &&  “ ((run + (Znth i values 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first <= (i + 1 )) ” 
  &&  “ (0 <= ways) ” 
  &&  “ (ways <= (100000 * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  TT && emp 
|--
  “ (ways = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ (first = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ ((run + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_5_5_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (ways = (ValidPairCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_5_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  (first = (FirstCutCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_5_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : (i < 1)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (values)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH8 : (total = (PrefixSum (values) (n_pre)))) (PreH9 : (total = (3 * third ))) (PreH10 : (((-10000) * n_pre ) <= total)) (PreH11 : (total <= (10000 * n_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre - 1 ))) (PreH14 : (run = (PrefixSum (values) (i)))) (PreH15 : (first = (FirstCutCount (values) (third) (i)))) (PreH16 : (ways = (ValidPairCount (values) (third) (i)))) (PreH17 : (((-10000) * i ) <= run)) (PreH18 : (run <= (10000 * i ))) (PreH19 : (0 <= first)) (PreH20 : (first <= i)) (PreH21 : (0 <= ways)) (PreH22 : (ways <= (100000 * i ))) ,
  ((run + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 ))))
.

Definition solver_entail_wit_5_6 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ (total = (3 * third )) ” 
  &&  “ (((-10000) * n_pre ) <= total) ” 
  &&  “ (total <= (10000 * n_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((run + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 )))) ” 
  &&  “ (first = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ (ways = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ (((-10000) * (i + 1 ) ) <= (run + (Znth i values 0) )) ” 
  &&  “ ((run + (Znth i values 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first <= (i + 1 )) ” 
  &&  “ (0 <= ways) ” 
  &&  “ (ways <= (100000 * (i + 1 ) )) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  TT && emp 
|--
  “ (((-10000) * (i + 1 ) ) <= (run + (Znth i values 0) )) ” 
  &&  “ (ways = (ValidPairCount (values) (third) ((i + 1 )))) ” 
  &&  “ (first = (FirstCutCount (values) (third) ((i + 1 )))) ” 
  &&  “ ((run + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_5_6_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (((-10000) * (i + 1 ) ) <= (run + (Znth i values 0) ))
.

Definition solver_entail_wit_5_6_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (ways = (ValidPairCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_6_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  (first = (FirstCutCount (values) (third) ((i + 1 ))))
.

Definition solver_entail_wit_5_6_split_goal_4 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((run + (Znth i values 0) ) <> third)) (PreH2 : ((run + (Znth i values 0) ) <> (2 * third ))) (PreH3 : (i >= 1)) (PreH4 : ((i + 1 ) < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (values)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH9 : (total = (PrefixSum (values) (n_pre)))) (PreH10 : (total = (3 * third ))) (PreH11 : (((-10000) * n_pre ) <= total)) (PreH12 : (total <= (10000 * n_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre - 1 ))) (PreH15 : (run = (PrefixSum (values) (i)))) (PreH16 : (first = (FirstCutCount (values) (third) (i)))) (PreH17 : (ways = (ValidPairCount (values) (third) (i)))) (PreH18 : (((-10000) * i ) <= run)) (PreH19 : (run <= (10000 * i ))) (PreH20 : (0 <= first)) (PreH21 : (first <= i)) (PreH22 : (0 <= ways)) (PreH23 : (ways <= (100000 * i ))) ,
  ((run + (Znth i values 0) ) = (PrefixSum (values) ((i + 1 ))))
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (total = (PrefixSum (values) (n_pre)))) (PreH7 : (total = (3 * third ))) (PreH8 : (((-10000) * n_pre ) <= total)) (PreH9 : (total <= (10000 * n_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (run = (PrefixSum (values) (i)))) (PreH13 : (first = (FirstCutCount (values) (third) (i)))) (PreH14 : (ways = (ValidPairCount (values) (third) (i)))) (PreH15 : (((-10000) * i ) <= run)) (PreH16 : (run <= (10000 * i ))) (PreH17 : (0 <= first)) (PreH18 : (first <= i)) (PreH19 : (0 <= ways)) (PreH20 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (Spec values ways ) ”
  &&  (Int64Array.full a_pre n_pre values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (total = (PrefixSum (values) (n_pre)))) (PreH7 : (total = (3 * third ))) (PreH8 : (((-10000) * n_pre ) <= total)) (PreH9 : (total <= (10000 * n_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (run = (PrefixSum (values) (i)))) (PreH13 : (first = (FirstCutCount (values) (third) (i)))) (PreH14 : (ways = (ValidPairCount (values) (third) (i)))) (PreH15 : (((-10000) * i ) <= run)) (PreH16 : (run <= (10000 * i ))) (PreH17 : (0 <= first)) (PreH18 : (first <= i)) (PreH19 : (0 <= ways)) (PreH20 : (ways <= (100000 * i ))) ,
  TT && emp 
|--
  “ (Spec values ways ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (total = (PrefixSum (values) (n_pre)))) (PreH7 : (total = (3 * third ))) (PreH8 : (((-10000) * n_pre ) <= total)) (PreH9 : (total <= (10000 * n_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (run = (PrefixSum (values) (i)))) (PreH13 : (first = (FirstCutCount (values) (third) (i)))) (PreH14 : (ways = (ValidPairCount (values) (third) (i)))) (PreH15 : (((-10000) * i ) <= run)) (PreH16 : (run <= (10000 * i ))) (PreH17 : (0 <= first)) (PreH18 : (first <= i)) (PreH19 : (0 <= ways)) (PreH20 : (ways <= (100000 * i ))) ,
  (Spec values ways )
.

Definition solver_return_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (values)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH5 : (total = (PrefixSum (values) (n_pre)))) (PreH6 : (Spec values 0 )) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (Spec values 0 ) ”
  &&  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (total = (PrefixSum (values) (i)))) (PreH9 : (((-10000) * i ) <= total)) (PreH10 : (total <= (10000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (total = (PrefixSum (values) (i))) ” 
  &&  “ (((-10000) * i ) <= total) ” 
  &&  “ (total <= (10000 * i )) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (ways: Z) (first: Z) (run: Z) (i: Z) (third: Z) (total: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (values)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000)))) (PreH6 : (total = (PrefixSum (values) (n_pre)))) (PreH7 : (total = (3 * third ))) (PreH8 : (((-10000) * n_pre ) <= total)) (PreH9 : (total <= (10000 * n_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (run = (PrefixSum (values) (i)))) (PreH13 : (first = (FirstCutCount (values) (third) (i)))) (PreH14 : (ways = (ValidPairCount (values) (third) (i)))) (PreH15 : (((-10000) * i ) <= run)) (PreH16 : (run <= (10000 * i ))) (PreH17 : (0 <= first)) (PreH18 : (first <= i)) (PreH19 : (0 <= ways)) (PreH20 : (ways <= (100000 * i ))) ,
  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (values)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((-10000) <= (Znth k values 0)) /\ ((Znth k values 0) <= 10000))) ” 
  &&  “ (total = (PrefixSum (values) (n_pre))) ” 
  &&  “ (total = (3 * third )) ” 
  &&  “ (((-10000) * n_pre ) <= total) ” 
  &&  “ (total <= (10000 * n_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (run = (PrefixSum (values) (i))) ” 
  &&  “ (first = (FirstCutCount (values) (third) (i))) ” 
  &&  “ (ways = (ValidPairCount (values) (third) (i))) ” 
  &&  “ (((-10000) * i ) <= run) ” 
  &&  “ (run <= (10000 * i )) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first <= i) ” 
  &&  “ (0 <= ways) ” 
  &&  “ (ways <= (100000 * i )) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
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
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Axiom proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4.
Axiom proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5.
Axiom proof_of_solver_entail_wit_5_6 : solver_entail_wit_5_6.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
