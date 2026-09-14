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
Require Import SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_lib.
Local Open Scope sac.

(*----- Function sort -----*)

Definition sort_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) < 100)))) ,
  ((( &( "value" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "output" ) ) 100 )
  **  (IntArray.undef_full ( &( "count" ) ) 100 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (count_mixed: (@list (@option Z))) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (output_mixed)) = 100)) (PreH5 : ((Zlength (count_mixed)) = 100)) (PreH6 : (0 <= value)) (PreH7 : (value <= 100)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH10 : (CountingZeroedPrefix count_mixed value )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.mixed_full ( &( "count" ) ) 100 count_mixed )
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition sort_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (count_mixed: (@list (@option Z))) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : (0 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH11 : (CountingZeroedPrefix count_mixed value )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.mixed_full ( &( "count" ) ) 100 count_mixed )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (count_mixed: (@list (@option Z))) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : (0 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH11 : (CountingZeroedPrefix count_mixed value )) ,
  (IntArray.mixed_full ( &( "count" ) ) 100 (replace_Znth (value) ((Some (0))) (count_mixed)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ ((value + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (value + 1 )) ”
.

Definition sort_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (output_mixed: (@list (@option Z))) (zeros: (@list Z))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (output_mixed)) = 100)) (PreH5 : ((Zlength (zeros)) = 100)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH8 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((Znth value zeros 0) = 0))) (PreH9 : (CountingHistogramPrefix input zeros 0 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 zeros )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (counts: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth i input 0))) (PreH2 : ((Znth i input 0) < 100)) (PreH3 : (0 <= (Znth (Znth i input 0) counts 0))) (PreH4 : ((Znth (Znth i input 0) counts 0) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed)) = 100)) (PreH12 : ((Zlength (counts)) = 100)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH16 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH18 : (CountingHistogramPrefix input counts i )) ,
  (IntArray.full ( &( "count" ) ) 100 counts )
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (((Znth (Znth i input 0) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i input 0) counts 0) + 1 )) ”
.

Definition sort_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (counts: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth i input 0))) (PreH2 : ((Znth i input 0) < 100)) (PreH3 : (0 <= (Znth (Znth i input 0) counts 0))) (PreH4 : ((Znth (Znth i input 0) counts 0) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed)) = 100)) (PreH12 : ((Zlength (counts)) = 100)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH16 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH18 : (CountingHistogramPrefix input counts i )) ,
  (IntArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth i input 0)) (((Znth (Znth i input 0) counts 0) + 1 )) (counts)) )
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (counts: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH12 : (CountingHistogramPrefix input counts i )) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 counts )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (output_mixed)) = 100)) (PreH5 : ((Zlength (positions)) = 100)) (PreH6 : (1 <= value)) (PreH7 : (value <= 100)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH9 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH10 : ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH12 : (CountingCumulativeState input positions value )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition sort_safety_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions value )) ,
  (IntArray.full ( &( "count" ) ) 100 positions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth value positions 0) + (Znth (value - 1 ) positions 0) )) ”
.

Definition sort_safety_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions value )) ,
  (IntArray.full ( &( "count" ) ) 100 positions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ ((value - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (value - 1 )) ”
.

Definition sort_safety_wit_12 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions value )) ,
  (IntArray.full ( &( "count" ) ) 100 positions )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_13 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions value )) ,
  (IntArray.full ( &( "count" ) ) 100 (replace_Znth (value) (((Znth value positions 0) + (Znth (value - 1 ) positions 0) )) (positions)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ ((value + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (value + 1 )) ”
.

Definition sort_safety_wit_14 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value >= 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions value )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition sort_safety_wit_15 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value >= 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions value )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_16 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (positions: (@list Z)) (sorted: (@list Z))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : ((Zlength (positions)) = 100)) (PreH6 : ((Zlength (bucket_ends)) = 100)) (PreH7 : ((Zlength (output_mixed)) = 100)) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH12 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH13 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH14 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH15 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_17 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth (i) (input) (0)))) (PreH2 : ((Znth (i) (input) (0)) < 100)) (PreH3 : (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0)))) (PreH4 : ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH19 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH20 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH21 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH22 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (IntArray.full ( &( "count" ) ) 100 positions )
  **  ((( &( "value" ) )) # Int  |-> (Znth (i) (input) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (((Znth (Znth (i) (input) (0)) positions 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth (i) (input) (0)) positions 0) - 1 )) ”
.

Definition sort_safety_wit_18 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)))) (PreH2 : ((Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)) < 100)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (0 <= (Znth (i) (input) (0)))) (PreH6 : ((Znth (i) (input) (0)) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0)))) (PreH8 : ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH23 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH24 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH25 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH26 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (IntArray.mixed_full ( &( "output" ) ) 100 (replace_Znth ((Znth (Znth (i) (input) (0)) (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) 0)) ((Some ((Znth (i) (input) (0))))) (output_mixed)) )
  **  (IntArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition sort_safety_wit_19 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (bucket_starts: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : ((Zlength (bucket_starts)) = 100)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) < 100)))) (PreH7 : (CountingSorted input sorted )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_20 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts: (@list Z)) (live: (@list Z)) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) < 100)))) (PreH11 : (CountingSorted input sorted )) (PreH12 : (CountingCopyProgress input sorted live i )) ,
  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - 0 ) sorted 0)) (live)) )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) < 100)))) ,
  (IntArray.undef_full ( &( "output" ) ) 100 )
  **  (IntArray.undef_full ( &( "count" ) ) 100 )
  **  (IntArray.full a_pre n_pre input )
|--
  EX (count_mixed: (@list (@option Z)))  (output_mixed: (@list (@option Z))) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (count_mixed)) = 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingZeroedPrefix count_mixed 0 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.mixed_full ( &( "count" ) ) 100 count_mixed )
) \/
(
forall (n_pre: Z) (input: (@list Z))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) < 100)))) ,
  (IntArray.undef_full ( &( "output" ) ) 100 )
  **  (IntArray.undef_full ( &( "count" ) ) 100 )
|--
  EX (count_mixed: (@list (@option Z)))  (output_mixed: (@list (@option Z))) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (count_mixed)) = 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingZeroedPrefix count_mixed 0 ) ”
  &&  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.mixed_full ( &( "count" ) ) 100 count_mixed )
).

Definition sort_entail_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (count_mixed_2: (@list (@option Z))) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed_2)) = 100)) (PreH7 : (0 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH11 : (CountingZeroedPrefix count_mixed_2 value )) ,
  (IntArray.mixed_full ( &( "count" ) ) 100 (replace_Znth (value) ((Some (0))) (count_mixed_2)) )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed_2 )
|--
  EX (count_mixed: (@list (@option Z)))  (output_mixed: (@list (@option Z))) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (count_mixed)) = 100) ” 
  &&  “ (0 <= (value + 1 )) ” 
  &&  “ ((value + 1 ) <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingZeroedPrefix count_mixed (value + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.mixed_full ( &( "count" ) ) 100 count_mixed )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (value: Z) (count_mixed_2: (@list (@option Z))) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed_2)) = 100)) (PreH7 : (0 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH11 : (CountingZeroedPrefix count_mixed_2 value )) ,
  TT && emp 
|--
  “ (CountingZeroedPrefix (replace_Znth (value) ((Some (0))) (count_mixed_2)) (value + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (value) ((Some (0))) (count_mixed_2)))) = 100) ”
  &&  emp
).

Definition sort_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (value: Z) (count_mixed_2: (@list (@option Z))) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed_2)) = 100)) (PreH7 : (0 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH11 : (CountingZeroedPrefix count_mixed_2 value )) ,
  (CountingZeroedPrefix (replace_Znth (value) ((Some (0))) (count_mixed_2)) (value + 1 ) )
.

Definition sort_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (value: Z) (count_mixed_2: (@list (@option Z))) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed_2)) = 100)) (PreH7 : (0 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH11 : (CountingZeroedPrefix count_mixed_2 value )) ,
  ((Zlength ((replace_Znth (value) ((Some (0))) (count_mixed_2)))) = 100)
.

Definition sort_entail_wit_3 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value_2: Z) (count_mixed: (@list (@option Z))) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value_2 >= 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : (0 <= value_2)) (PreH8 : (value_2 <= 100)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH11 : (CountingZeroedPrefix count_mixed value_2 )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed_2 )
  **  (IntArray.mixed_full ( &( "count" ) ) 100 count_mixed )
|--
  EX (zeros: (@list Z))  (output_mixed: (@list (@option Z))) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (zeros)) = 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((Znth value zeros 0) = 0)) ” 
  &&  “ (CountingHistogramPrefix input zeros 0 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 zeros )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (value_2: Z) (count_mixed: (@list (@option Z))) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value_2 >= 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : (0 <= value_2)) (PreH8 : (value_2 <= 100)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH11 : (CountingZeroedPrefix count_mixed value_2 )) ,
  (IntArray.mixed_full ( &( "count" ) ) 100 count_mixed )
|--
  EX (zeros: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed_2)) = 100) ” 
  &&  “ ((Zlength (zeros)) = 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None)) ” 
  &&  “ forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((Znth value zeros 0) = 0)) ” 
  &&  “ (CountingHistogramPrefix input zeros 0 ) ”
  &&  (IntArray.full ( &( "count" ) ) 100 zeros )
).

Definition sort_entail_wit_4 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (output_mixed_2: (@list (@option Z))) (zeros: (@list Z))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (output_mixed_2)) = 100)) (PreH5 : ((Zlength (zeros)) = 100)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH8 : forall (value_2: Z) , (((0 <= value_2) /\ (value_2 < 100)) -> ((Znth value_2 zeros 0) = 0))) (PreH9 : (CountingHistogramPrefix input zeros 0 )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed_2 )
  **  (IntArray.full ( &( "count" ) ) 100 zeros )
|--
  EX (counts: (@list Z))  (output_mixed: (@list (@option Z))) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (counts)) = 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= 0))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingHistogramPrefix input counts 0 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 counts )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (output_mixed_2: (@list (@option Z))) (zeros: (@list Z))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (output_mixed_2)) = 100)) (PreH5 : ((Zlength (zeros)) = 100)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH8 : forall (value_2: Z) , (((0 <= value_2) /\ (value_2 < 100)) -> ((Znth value_2 zeros 0) = 0))) (PreH9 : (CountingHistogramPrefix input zeros 0 )) ,
  TT && emp 
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None)) ” 
  &&  “ forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value zeros 0)) /\ ((Znth value zeros 0) <= 0))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ”
  &&  emp
).

Definition sort_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (output_mixed_2: (@list (@option Z))) (zeros: (@list Z))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (output_mixed_2)) = 100)) (PreH5 : ((Zlength (zeros)) = 100)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH8 : forall (value_2: Z) , (((0 <= value_2) /\ (value_2 < 100)) -> ((Znth value_2 zeros 0) = 0))) (PreH9 : (CountingHistogramPrefix input zeros 0 )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))
.

Definition sort_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (output_mixed_2: (@list (@option Z))) (zeros: (@list Z))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (output_mixed_2)) = 100)) (PreH5 : ((Zlength (zeros)) = 100)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH8 : forall (value_2: Z) , (((0 <= value_2) /\ (value_2 < 100)) -> ((Znth value_2 zeros 0) = 0))) (PreH9 : (CountingHistogramPrefix input zeros 0 )) ,
  forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value zeros 0)) /\ ((Znth value zeros 0) <= 0)))
.

Definition sort_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (output_mixed_2: (@list (@option Z))) (zeros: (@list Z))  __default__App_option_Z (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (output_mixed_2)) = 100)) (PreH5 : ((Zlength (zeros)) = 100)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH8 : forall (value_2: Z) , (((0 <= value_2) /\ (value_2 < 100)) -> ((Znth value_2 zeros 0) = 0))) (PreH9 : (CountingHistogramPrefix input zeros 0 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))
.

Definition sort_entail_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (counts: (@list Z))  __default__App_option_Z (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH12 : (CountingHistogramPrefix input counts i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 counts )
|--
  “ (0 <= (Znth i input 0)) ” 
  &&  “ ((Znth i input 0) < 100) ” 
  &&  “ (0 <= (Znth (Znth i input 0) counts 0)) ” 
  &&  “ ((Znth (Znth i input 0) counts 0) < 100) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (counts)) = 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingHistogramPrefix input counts i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 counts )
.

Definition sort_entail_wit_6 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed_2: (@list (@option Z))) (counts_2: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth i input 0))) (PreH2 : ((Znth i input 0) < 100)) (PreH3 : (0 <= (Znth (Znth i input 0) counts_2 0))) (PreH4 : ((Znth (Znth i input 0) counts_2 0) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed_2)) = 100)) (PreH12 : ((Zlength (counts_2)) = 100)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH16 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts_2 0)) /\ ((Znth value counts_2 0) <= i)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH18 : (CountingHistogramPrefix input counts_2 i )) ,
  (IntArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth i input 0)) (((Znth (Znth i input 0) counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed_2 )
|--
  EX (counts: (@list Z))  (output_mixed: (@list (@option Z))) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (counts)) = 100) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= (i + 1 )))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingHistogramPrefix input counts (i + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 counts )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed_2: (@list (@option Z))) (counts_2: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth i input 0))) (PreH2 : ((Znth i input 0) < 100)) (PreH3 : (0 <= (Znth (Znth i input 0) counts_2 0))) (PreH4 : ((Znth (Znth i input 0) counts_2 0) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed_2)) = 100)) (PreH12 : ((Zlength (counts_2)) = 100)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH16 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts_2 0)) /\ ((Znth value counts_2 0) <= i)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH18 : (CountingHistogramPrefix input counts_2 i )) ,
  TT && emp 
|--
  “ (CountingHistogramPrefix input (replace_Znth ((Znth i input 0)) (((Znth (Znth i input 0) counts_2 0) + 1 )) (counts_2)) (i + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth ((Znth i input 0)) (((Znth (Znth i input 0) counts_2 0) + 1 )) (counts_2)))) = 100) ”
  &&  emp
).

Definition sort_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed_2: (@list (@option Z))) (counts_2: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth i input 0))) (PreH2 : ((Znth i input 0) < 100)) (PreH3 : (0 <= (Znth (Znth i input 0) counts_2 0))) (PreH4 : ((Znth (Znth i input 0) counts_2 0) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed_2)) = 100)) (PreH12 : ((Zlength (counts_2)) = 100)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH16 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts_2 0)) /\ ((Znth value counts_2 0) <= i)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH18 : (CountingHistogramPrefix input counts_2 i )) ,
  (CountingHistogramPrefix input (replace_Znth ((Znth i input 0)) (((Znth (Znth i input 0) counts_2 0) + 1 )) (counts_2)) (i + 1 ) )
.

Definition sort_entail_wit_6_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed_2: (@list (@option Z))) (counts_2: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth i input 0))) (PreH2 : ((Znth i input 0) < 100)) (PreH3 : (0 <= (Znth (Znth i input 0) counts_2 0))) (PreH4 : ((Znth (Znth i input 0) counts_2 0) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed_2)) = 100)) (PreH12 : ((Zlength (counts_2)) = 100)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH16 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts_2 0)) /\ ((Znth value counts_2 0) <= i)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH18 : (CountingHistogramPrefix input counts_2 i )) ,
  ((Zlength ((replace_Znth ((Znth i input 0)) (((Znth (Znth i input 0) counts_2 0) + 1 )) (counts_2)))) = 100)
.

Definition sort_entail_wit_7 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (counts: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH10 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH12 : (CountingHistogramPrefix input counts i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed_2 )
  **  (IntArray.full ( &( "count" ) ) 100 counts )
|--
  EX (positions: (@list Z))  (output_mixed: (@list (@option Z))) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((1 < 100) -> (((Znth 1 positions 0) + (Znth (1 - 1 ) positions 0) ) <= n_pre)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingCumulativeState input positions 1 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (counts: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH10 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH12 : (CountingHistogramPrefix input counts i )) ,
  TT && emp 
|--
  “ (CountingCumulativeState input counts 1 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None)) ” 
  &&  “ ((1 < 100) -> (((Znth 1 counts 0) + (Znth (1 - 1 ) counts 0) ) <= n_pre)) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket counts 0)) /\ ((Znth bucket counts 0) <= n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ”
  &&  emp
).

Definition sort_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (counts: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH10 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH12 : (CountingHistogramPrefix input counts i )) ,
  (CountingCumulativeState input counts 1 )
.

Definition sort_entail_wit_7_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (counts: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH10 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH12 : (CountingHistogramPrefix input counts i )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))
.

Definition sort_entail_wit_7_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (counts: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH10 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH12 : (CountingHistogramPrefix input counts i )) ,
  ((1 < 100) -> (((Znth 1 counts 0) + (Znth (1 - 1 ) counts 0) ) <= n_pre))
.

Definition sort_entail_wit_7_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (counts: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH10 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH12 : (CountingHistogramPrefix input counts i )) ,
  forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket counts 0)) /\ ((Znth bucket counts 0) <= n_pre)))
.

Definition sort_entail_wit_7_split_goal_5 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (counts: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 input 0)) /\ ((Znth k_3 input 0) < 100)))) (PreH10 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed_2 __default__App_option_Z) = None))) (PreH12 : (CountingHistogramPrefix input counts i )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))
.

Definition sort_entail_wit_8 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions_2: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions_2 0)) /\ ((Znth bucket positions_2 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions_2 value )) ,
  (IntArray.full ( &( "count" ) ) 100 (replace_Znth (value) (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) )) (positions_2)) )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed_2 )
|--
  EX (positions: (@list Z))  (output_mixed: (@list (@option Z))) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ (1 <= (value + 1 )) ” 
  &&  “ ((value + 1 ) <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ (((value + 1 ) < 100) -> (((Znth (value + 1 ) positions 0) + (Znth ((value + 1 ) - 1 ) positions 0) ) <= n_pre)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingCumulativeState input positions (value + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (value: Z) (positions_2: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions_2 0)) /\ ((Znth bucket positions_2 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions_2 value )) ,
  TT && emp 
|--
  “ (CountingCumulativeState input (replace_Znth (value) (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) )) (positions_2)) (value + 1 ) ) ” 
  &&  “ (((value + 1 ) < 100) -> (((Znth (value + 1 ) (replace_Znth (value) (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) )) (positions_2)) 0) + (Znth ((value + 1 ) - 1 ) (replace_Znth (value) (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) )) (positions_2)) 0) ) <= n_pre)) ” 
  &&  “ ((Zlength ((replace_Znth (value) (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) )) (positions_2)))) = 100) ”
  &&  emp
).

Definition sort_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (value: Z) (positions_2: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions_2 0)) /\ ((Znth bucket positions_2 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions_2 value )) ,
  (CountingCumulativeState input (replace_Znth (value) (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) )) (positions_2)) (value + 1 ) )
.

Definition sort_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (value: Z) (positions_2: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions_2 0)) /\ ((Znth bucket positions_2 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions_2 value )) ,
  (((value + 1 ) < 100) -> (((Znth (value + 1 ) (replace_Znth (value) (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) )) (positions_2)) 0) + (Znth ((value + 1 ) - 1 ) (replace_Znth (value) (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) )) (positions_2)) 0) ) <= n_pre))
.

Definition sort_entail_wit_8_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (value: Z) (positions_2: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions_2 0)) /\ ((Znth bucket positions_2 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed_2 __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions_2 value )) ,
  ((Zlength ((replace_Znth (value) (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) )) (positions_2)))) = 100)
.

Definition sort_entail_wit_9 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions_2: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value >= 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 input 0)) /\ ((Znth k_4 input 0) < 100)))) (PreH10 : forall (bucket_2: Z) , (((0 <= bucket_2) /\ (bucket_2 < 100)) -> ((0 <= (Znth bucket_2 positions_2 0)) /\ ((Znth bucket_2 positions_2 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) ) <= n_pre))) (PreH12 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 100)) -> ((Znth k_5 output_mixed_2 __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions_2 value )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed_2 )
  **  (IntArray.full ( &( "count" ) ) 100 positions_2 )
|--
  EX (output_mixed: (@list (@option Z)))  (bucket_ends: (@list Z))  (positions: (@list Z))  (sorted: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ (((n_pre - 1 ) >= 0) -> (1 <= (Znth (Znth (n_pre - 1 ) input 0) positions 0))) ” 
  &&  “ forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted (n_pre - 1 ) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (value: Z) (positions_2: (@list Z)) (output_mixed_2: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value >= 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 input 0)) /\ ((Znth k_4 input 0) < 100)))) (PreH10 : forall (bucket_2: Z) , (((0 <= bucket_2) /\ (bucket_2 < 100)) -> ((0 <= (Znth bucket_2 positions_2 0)) /\ ((Znth bucket_2 positions_2 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions_2 0) + (Znth (value - 1 ) positions_2 0) ) <= n_pre))) (PreH12 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 100)) -> ((Znth k_5 output_mixed_2 __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions_2 value )) ,
  TT && emp 
|--
  EX (bucket_ends: (@list Z))  (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (input))) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((-1) <= ((Zlength (input)) - 1 )) ” 
  &&  “ (((Zlength (input)) - 1 ) < (Zlength (input))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (input)))) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ ((((Zlength (input)) - 1 ) >= 0) -> (1 <= (Znth (Znth ((Zlength (input)) - 1 ) input 0) positions_2 0))) ” 
  &&  “ forall (k_3: Z) , ((((Zlength (input)) <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed_2 __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input positions_2 bucket_ends output_mixed_2 sorted ((Zlength (input)) - 1 ) ) ”
  &&  emp
).

Definition sort_entail_wit_10 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (i >= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : ((Zlength (bucket_ends)) = 100)) (PreH8 : ((Zlength (output_mixed)) = 100)) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH13 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH14 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH15 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH16 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "value" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
|--
  “ (0 <= (Znth (i) (input) (0))) ” 
  &&  “ ((Znth (i) (input) (0)) < 100) ” 
  &&  “ ((Znth (i) (input) (0)) = (Znth (i) (input) (0))) ” 
  &&  “ (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0))) ” 
  &&  “ ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0))) ” 
  &&  “ forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i ) ”
  &&  ((( &( "value" ) )) # Int  |-> (Znth (i) (input) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Znth i input 0) <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((Znth i input 0) >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH19 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH20 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH21 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH22 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  TT && emp 
|--
  “ ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre) ” 
  &&  “ ((Znth (i) (input) (0)) < 100) ” 
  &&  “ (0 <= (Znth (i) (input) (0))) ”
  &&  emp
).

Definition sort_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Znth i input 0) <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((Znth i input 0) >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH19 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH20 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH21 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH22 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)
.

Definition sort_entail_wit_10_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Znth i input 0) <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((Znth i input 0) >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH19 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH20 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH21 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH22 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  ((Znth (i) (input) (0)) < 100)
.

Definition sort_entail_wit_10_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Znth i input 0) <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((Znth i input 0) >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH19 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH20 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH21 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH22 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (0 <= (Znth (i) (input) (0)))
.

Definition sort_entail_wit_11 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth (i) (input) (0)))) (PreH2 : ((Znth (i) (input) (0)) < 100)) (PreH3 : (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0)))) (PreH4 : ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH19 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH20 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH21 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH22 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (IntArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) )
  **  ((( &( "value" ) )) # Int  |-> (Znth (i) (input) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (0 <= (Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0))) ” 
  &&  “ ((Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)) < 100) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= (Znth (i) (input) (0))) ” 
  &&  “ ((Znth (i) (input) (0)) < 100) ” 
  &&  “ (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0))) ” 
  &&  “ ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0))) ” 
  &&  “ forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i ) ”
  &&  ((( &( "value" ) )) # Int  |-> (Znth (i) (input) (0)))
  **  (IntArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth (i) (input) (0)) <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : ((Znth (i) (input) (0)) >= INT_MIN)) (PreH5 : (0 <= (Znth (i) (input) (0)))) (PreH6 : ((Znth (i) (input) (0)) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0)))) (PreH8 : ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH23 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH24 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH25 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH26 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  TT && emp 
|--
  “ ((Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)) < 100) ” 
  &&  “ (0 <= (Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0))) ”
  &&  emp
).

Definition sort_entail_wit_11_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth (i) (input) (0)) <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : ((Znth (i) (input) (0)) >= INT_MIN)) (PreH5 : (0 <= (Znth (i) (input) (0)))) (PreH6 : ((Znth (i) (input) (0)) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0)))) (PreH8 : ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH23 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH24 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH25 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH26 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  ((Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)) < 100)
.

Definition sort_entail_wit_11_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth (i) (input) (0)) <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : ((Znth (i) (input) (0)) >= INT_MIN)) (PreH5 : (0 <= (Znth (i) (input) (0)))) (PreH6 : ((Znth (i) (input) (0)) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0)))) (PreH8 : ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH23 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH24 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH25 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH26 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (0 <= (Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)))
.

Definition sort_entail_wit_12 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed_2: (@list (@option Z))) (bucket_ends_2: (@list Z)) (sorted_2: (@list Z)) (positions_2: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions_2) (0)) - 1 )) (positions_2))) (0)))) (PreH2 : ((Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions_2) (0)) - 1 )) (positions_2))) (0)) < 100)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (0 <= (Znth (i) (input) (0)))) (PreH6 : ((Znth (i) (input) (0)) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) (0))) (positions_2) (0)))) (PreH8 : ((Znth ((Znth (i) (input) (0))) (positions_2) (0)) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted_2)) = n_pre)) (PreH16 : ((Zlength (positions_2)) = 100)) (PreH17 : ((Zlength (bucket_ends_2)) = 100)) (PreH18 : ((Zlength (output_mixed_2)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted_2 0)) /\ ((Znth k_2 sorted_2 0) < 100)))) (PreH23 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions_2 0)) /\ ((Znth bucket positions_2 0) <= n_pre)))) (PreH24 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions_2 0)))) (PreH25 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed_2 __default__App_option_Z) = None))) (PreH26 : (CountingPlacementProgress input positions_2 bucket_ends_2 output_mixed_2 sorted_2 i )) ,
  (IntArray.mixed_full ( &( "output" ) ) 100 (replace_Znth ((Znth (Znth (i) (input) (0)) (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions_2 0) - 1 )) (positions_2)) 0)) ((Some ((Znth (i) (input) (0))))) (output_mixed_2)) )
  **  (IntArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions_2 0) - 1 )) (positions_2)) )
  **  (IntArray.full a_pre n_pre input )
|--
  EX (output_mixed: (@list (@option Z)))  (bucket_ends: (@list Z))  (positions: (@list Z))  (sorted: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ (((i - 1 ) >= 0) -> (1 <= (Znth (Znth (i - 1 ) input 0) positions 0))) ” 
  &&  “ forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted (i - 1 ) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed_2: (@list (@option Z))) (bucket_ends_2: (@list Z)) (sorted_2: (@list Z)) (positions_2: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions_2) (0)) - 1 )) (positions_2))) (0)))) (PreH2 : ((Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions_2) (0)) - 1 )) (positions_2))) (0)) < 100)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (0 <= (Znth (i) (input) (0)))) (PreH6 : ((Znth (i) (input) (0)) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) (0))) (positions_2) (0)))) (PreH8 : ((Znth ((Znth (i) (input) (0))) (positions_2) (0)) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted_2)) = n_pre)) (PreH16 : ((Zlength (positions_2)) = 100)) (PreH17 : ((Zlength (bucket_ends_2)) = 100)) (PreH18 : ((Zlength (output_mixed_2)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted_2 0)) /\ ((Znth k_2 sorted_2 0) < 100)))) (PreH23 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions_2 0)) /\ ((Znth bucket positions_2 0) <= n_pre)))) (PreH24 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions_2 0)))) (PreH25 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed_2 __default__App_option_Z) = None))) (PreH26 : (CountingPlacementProgress input positions_2 bucket_ends_2 output_mixed_2 sorted_2 i )) ,
  TT && emp 
|--
  EX (bucket_ends: (@list Z))  (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (input))) ” 
  &&  “ ((Zlength ((replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions_2 0) - 1 )) (positions_2)))) = 100) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((Zlength ((replace_Znth ((Znth (Znth (i) (input) (0)) (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions_2 0) - 1 )) (positions_2)) 0)) ((Some ((Znth (i) (input) (0))))) (output_mixed_2)))) = 100) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < (Zlength (input))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (input)))) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions_2 0) - 1 )) (positions_2)) 0)) /\ ((Znth bucket (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions_2 0) - 1 )) (positions_2)) 0) <= (Zlength (input))))) ” 
  &&  “ (((i - 1 ) >= 0) -> (1 <= (Znth (Znth (i - 1 ) input 0) (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions_2 0) - 1 )) (positions_2)) 0))) ” 
  &&  “ forall (k_3: Z) , ((((Zlength (input)) <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 (replace_Znth ((Znth (Znth (i) (input) (0)) (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions_2 0) - 1 )) (positions_2)) 0)) ((Some ((Znth (i) (input) (0))))) (output_mixed_2)) __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions_2 0) - 1 )) (positions_2)) bucket_ends (replace_Znth ((Znth (Znth (i) (input) (0)) (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions_2 0) - 1 )) (positions_2)) 0)) ((Some ((Znth (i) (input) (0))))) (output_mixed_2)) sorted (i - 1 ) ) ”
  &&  emp
).

Definition sort_entail_wit_13 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (positions: (@list Z)) (sorted_2: (@list Z))  __default__App_option_Z (PreH1 : (i < 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : ((Zlength (bucket_ends)) = 100)) (PreH8 : ((Zlength (output_mixed)) = 100)) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 input 0)) /\ ((Znth k_2 input 0) < 100)))) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 sorted_2 0)) /\ ((Znth k_3 sorted_2 0) < 100)))) (PreH13 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH14 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH15 : forall (k_4: Z) , (((n_pre <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed __default__App_option_Z) = None))) (PreH16 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted_2 i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
|--
  EX (bucket_starts: (@list Z))  (sorted: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (bucket_starts)) = 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) < 100))) ” 
  &&  “ (CountingSorted input sorted ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (positions: (@list Z)) (sorted_2: (@list Z))  __default__App_option_Z (PreH1 : (i < 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : ((Zlength (bucket_ends)) = 100)) (PreH8 : ((Zlength (output_mixed)) = 100)) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 input 0)) /\ ((Znth k_2 input 0) < 100)))) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 sorted_2 0)) /\ ((Znth k_3 sorted_2 0) < 100)))) (PreH13 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH14 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH15 : forall (k_4: Z) , (((n_pre <= k_4) /\ (k_4 < 100)) -> ((Znth k_4 output_mixed __default__App_option_Z) = None))) (PreH16 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted_2 i )) ,
  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  EX (sorted: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) < 100))) ” 
  &&  “ (CountingSorted input sorted ) ”
  &&  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
).

Definition sort_entail_wit_14 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (bucket_starts_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted_2)) = n_pre)) (PreH5 : ((Zlength (bucket_starts_2)) = 100)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted_2 0)) /\ ((Znth k_2 sorted_2 0) < 100)))) (PreH7 : (CountingSorted input sorted_2 )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts_2 )
|--
  EX (bucket_starts: (@list Z))  (live: (@list Z))  (sorted: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (live)) = n_pre) ” 
  &&  “ ((Zlength (bucket_starts)) = 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) < 100))) ” 
  &&  “ (CountingSorted input sorted ) ” 
  &&  “ (CountingCopyProgress input sorted live 0 ) ”
  &&  (IntArray.full a_pre n_pre live )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (bucket_starts_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted_2)) = n_pre)) (PreH5 : ((Zlength (bucket_starts_2)) = 100)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted_2 0)) /\ ((Znth k_2 sorted_2 0) < 100)))) (PreH7 : (CountingSorted input sorted_2 )) ,
  TT && emp 
|--
  “ (CountingCopyProgress input sorted_2 input 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) < 100))) ”
  &&  emp
).

Definition sort_entail_wit_14_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (bucket_starts_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted_2)) = n_pre)) (PreH5 : ((Zlength (bucket_starts_2)) = 100)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted_2 0)) /\ ((Znth k_2 sorted_2 0) < 100)))) (PreH7 : (CountingSorted input sorted_2 )) ,
  (CountingCopyProgress input sorted_2 input 0 )
.

Definition sort_entail_wit_14_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (bucket_starts_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted_2)) = n_pre)) (PreH5 : ((Zlength (bucket_starts_2)) = 100)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted_2 0)) /\ ((Znth k_2 sorted_2 0) < 100)))) (PreH7 : (CountingSorted input sorted_2 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) < 100)))
.

Definition sort_entail_wit_15 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts_2: (@list Z)) (live_2: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live_2)) = n_pre)) (PreH7 : ((Zlength (bucket_starts_2)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) < 100)))) (PreH11 : (CountingSorted input sorted_2 )) (PreH12 : (CountingCopyProgress input sorted_2 live_2 i )) ,
  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - 0 ) sorted_2 0)) (live_2)) )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts_2 )
|--
  EX (bucket_starts: (@list Z))  (live: (@list Z))  (sorted: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (live)) = n_pre) ” 
  &&  “ ((Zlength (bucket_starts)) = 100) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) < 100))) ” 
  &&  “ (CountingSorted input sorted ) ” 
  &&  “ (CountingCopyProgress input sorted live (i + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre live )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts_2: (@list Z)) (live_2: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live_2)) = n_pre)) (PreH7 : ((Zlength (bucket_starts_2)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) < 100)))) (PreH11 : (CountingSorted input sorted_2 )) (PreH12 : (CountingCopyProgress input sorted_2 live_2 i )) ,
  TT && emp 
|--
  “ (CountingCopyProgress input sorted_2 (replace_Znth (i) ((Znth (i - 0 ) sorted_2 0)) (live_2)) (i + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (i) ((Znth (i - 0 ) sorted_2 0)) (live_2)))) = n_pre) ”
  &&  emp
).

Definition sort_entail_wit_15_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts_2: (@list Z)) (live_2: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live_2)) = n_pre)) (PreH7 : ((Zlength (bucket_starts_2)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) < 100)))) (PreH11 : (CountingSorted input sorted_2 )) (PreH12 : (CountingCopyProgress input sorted_2 live_2 i )) ,
  (CountingCopyProgress input sorted_2 (replace_Znth (i) ((Znth (i - 0 ) sorted_2 0)) (live_2)) (i + 1 ) )
.

Definition sort_entail_wit_15_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts_2: (@list Z)) (live_2: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live_2)) = n_pre)) (PreH7 : ((Zlength (bucket_starts_2)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) < 100)))) (PreH11 : (CountingSorted input sorted_2 )) (PreH12 : (CountingCopyProgress input sorted_2 live_2 i )) ,
  ((Zlength ((replace_Znth (i) ((Znth (i - 0 ) sorted_2 0)) (live_2)))) = n_pre)
.

Definition sort_entail_wit_16 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts: (@list Z)) (live: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) < 100)))) (PreH11 : (CountingSorted input sorted_2 )) (PreH12 : (CountingCopyProgress input sorted_2 live i )) ,
  (IntArray.full a_pre n_pre live )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
|--
  EX (sorted: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (CountingSorted input sorted ) ”
  &&  (IntArray.full a_pre n_pre sorted )
  **  (IntArray.undef_full ( &( "output" ) ) 100 )
  **  (IntArray.undef_full ( &( "count" ) ) 100 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts: (@list Z)) (live: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) < 100)))) (PreH11 : (CountingSorted input sorted_2 )) (PreH12 : (CountingCopyProgress input sorted_2 live i )) ,
  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
|--
  “ (CountingSorted input live ) ”
  &&  (IntArray.undef_full ( &( "output" ) ) 100 )
  **  (IntArray.undef_full ( &( "count" ) ) 100 )
).

Definition sort_entail_wit_16_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts: (@list Z)) (live: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) < 100)))) (PreH11 : (CountingSorted input sorted_2 )) (PreH12 : (CountingCopyProgress input sorted_2 live i )) ,
  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
|--
  “ (CountingSorted input live ) ”
.

Definition sort_entail_wit_16_split_goal_spatial := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts: (@list Z)) (live: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) < 100)))) (PreH11 : (CountingSorted input sorted_2 )) (PreH12 : (CountingCopyProgress input sorted_2 live i )) ,
  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
|--
  (IntArray.undef_full ( &( "output" ) ) 100 )
  **  (IntArray.undef_full ( &( "count" ) ) 100 )
.

Definition sort_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (CountingSorted input sorted )) ,
  (IntArray.full a_pre n_pre sorted )
|--
  EX (output: (@list Z)) ,
  “ ((Zlength (output)) = n_pre) ” 
  &&  “ (Permutation input output ) ” 
  &&  “ (increasing output ) ”
  &&  (IntArray.full a_pre n_pre output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (CountingSorted input sorted )) ,
  TT && emp 
|--
  “ (increasing sorted ) ” 
  &&  “ (Permutation input sorted ) ”
  &&  emp
).

Definition sort_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (CountingSorted input sorted )) ,
  (increasing sorted )
.

Definition sort_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (CountingSorted input sorted )) ,
  (Permutation input sorted )
.

Definition sort_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (count_mixed: (@list (@option Z))) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : (0 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH11 : (CountingZeroedPrefix count_mixed value )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.mixed_full ( &( "count" ) ) 100 count_mixed )
|--
  “ (value < 100) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (count_mixed)) = 100) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingZeroedPrefix count_mixed value ) ”
  &&  (((( &( "count" ) ) + (value * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i ( &( "count" ) ) value 0 100 count_mixed )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
.

Definition sort_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (counts: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth i input 0))) (PreH2 : ((Znth i input 0) < 100)) (PreH3 : (0 <= (Znth (Znth i input 0) counts 0))) (PreH4 : ((Znth (Znth i input 0) counts 0) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed)) = 100)) (PreH12 : ((Zlength (counts)) = 100)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH16 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH18 : (CountingHistogramPrefix input counts i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 counts )
|--
  “ (0 <= (Znth i input 0)) ” 
  &&  “ ((Znth i input 0) < 100) ” 
  &&  “ (0 <= (Znth (Znth i input 0) counts 0)) ” 
  &&  “ ((Znth (Znth i input 0) counts 0) < 100) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (counts)) = 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingHistogramPrefix input counts i ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 counts )
.

Definition sort_partial_solve_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (counts: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth i input 0))) (PreH2 : ((Znth i input 0) < 100)) (PreH3 : (0 <= (Znth (Znth i input 0) counts 0))) (PreH4 : ((Znth (Znth i input 0) counts 0) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed)) = 100)) (PreH12 : ((Zlength (counts)) = 100)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH16 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH18 : (CountingHistogramPrefix input counts i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 counts )
|--
  “ (0 <= (Znth i input 0)) ” 
  &&  “ ((Znth i input 0) < 100) ” 
  &&  “ (0 <= (Znth (Znth i input 0) counts 0)) ” 
  &&  “ ((Znth (Znth i input 0) counts 0) < 100) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (counts)) = 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingHistogramPrefix input counts i ) ”
  &&  (((( &( "count" ) ) + ((Znth i input 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i input 0) counts 0))
  **  (IntArray.missing_i ( &( "count" ) ) (Znth i input 0) 0 100 counts )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
.

Definition sort_partial_solve_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (counts: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth i input 0))) (PreH2 : ((Znth i input 0) < 100)) (PreH3 : (0 <= (Znth (Znth i input 0) counts 0))) (PreH4 : ((Znth (Znth i input 0) counts 0) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed)) = 100)) (PreH12 : ((Zlength (counts)) = 100)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH16 : forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH18 : (CountingHistogramPrefix input counts i )) ,
  (IntArray.full ( &( "count" ) ) 100 counts )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (0 <= (Znth i input 0)) ” 
  &&  “ ((Znth i input 0) < 100) ” 
  &&  “ (0 <= (Znth (Znth i input 0) counts 0)) ” 
  &&  “ ((Znth (Znth i input 0) counts 0) < 100) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (counts)) = 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (value: Z) , (((0 <= value) /\ (value < 100)) -> ((0 <= (Znth value counts 0)) /\ ((Znth value counts 0) <= i))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingHistogramPrefix input counts i ) ”
  &&  (((( &( "count" ) ) + ((Znth i input 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "count" ) ) (Znth i input 0) 0 100 counts )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
.

Definition sort_partial_solve_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions value )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
|--
  “ (value < 100) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ (1 <= value) ” 
  &&  “ (value <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingCumulativeState input positions value ) ”
  &&  (((( &( "count" ) ) + (value * sizeof(INT)))) # Int  |-> (Znth value positions 0))
  **  (IntArray.missing_i ( &( "count" ) ) value 0 100 positions )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
.

Definition sort_partial_solve_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions value )) ,
  (IntArray.full ( &( "count" ) ) 100 positions )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (value < 100) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ (1 <= value) ” 
  &&  “ (value <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingCumulativeState input positions value ) ”
  &&  (((( &( "count" ) ) + ((value - 1 ) * sizeof(INT)))) # Int  |-> (Znth (value - 1 ) positions 0))
  **  (IntArray.missing_i ( &( "count" ) ) (value - 1 ) 0 100 positions )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
.

Definition sort_partial_solve_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (value: Z) (positions: (@list Z)) (output_mixed: (@list (@option Z)))  __default__App_option_Z (PreH1 : (value < 100)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH10 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH11 : ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None))) (PreH13 : (CountingCumulativeState input positions value )) ,
  (IntArray.full ( &( "count" ) ) 100 positions )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (value < 100) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ (1 <= value) ” 
  &&  “ (value <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((value < 100) -> (((Znth value positions 0) + (Znth (value - 1 ) positions 0) ) <= n_pre)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 100)) -> ((Znth k_2 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingCumulativeState input positions value ) ”
  &&  (((( &( "count" ) ) + (value * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "count" ) ) value 0 100 positions )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
.

Definition sort_partial_solve_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (i >= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : ((Zlength (bucket_ends)) = 100)) (PreH8 : ((Zlength (output_mixed)) = 100)) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH13 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH14 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH15 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH16 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
|--
  “ (i >= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0))) ” 
  &&  “ forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
.

Definition sort_partial_solve_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth (i) (input) (0)))) (PreH2 : ((Znth (i) (input) (0)) < 100)) (PreH3 : ((Znth (i) (input) (0)) = (Znth (i) (input) (0)))) (PreH4 : (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0)))) (PreH5 : ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= 0)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : ((Zlength (input)) = n_pre)) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (positions)) = 100)) (PreH14 : ((Zlength (bucket_ends)) = 100)) (PreH15 : ((Zlength (output_mixed)) = 100)) (PreH16 : ((-1) <= i)) (PreH17 : (i < n_pre)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH20 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH21 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH22 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH23 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 positions )
|--
  “ (0 <= (Znth (i) (input) (0))) ” 
  &&  “ ((Znth (i) (input) (0)) < 100) ” 
  &&  “ (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0))) ” 
  &&  “ ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0))) ” 
  &&  “ forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i ) ”
  &&  (((( &( "count" ) ) + ((Znth (i) (input) (0)) * sizeof(INT)))) # Int  |-> (Znth (Znth (i) (input) (0)) positions 0))
  **  (IntArray.missing_i ( &( "count" ) ) (Znth (i) (input) (0)) 0 100 positions )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
.

Definition sort_partial_solve_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth (i) (input) (0)))) (PreH2 : ((Znth (i) (input) (0)) < 100)) (PreH3 : (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0)))) (PreH4 : ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH19 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH20 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH21 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH22 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (IntArray.full ( &( "count" ) ) 100 positions )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (0 <= (Znth (i) (input) (0))) ” 
  &&  “ ((Znth (i) (input) (0)) < 100) ” 
  &&  “ (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0))) ” 
  &&  “ ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0))) ” 
  &&  “ forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i ) ”
  &&  (((( &( "count" ) ) + ((Znth (i) (input) (0)) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "count" ) ) (Znth (i) (input) (0)) 0 100 positions )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
.

Definition sort_partial_solve_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)))) (PreH2 : ((Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)) < 100)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (0 <= (Znth (i) (input) (0)))) (PreH6 : ((Znth (i) (input) (0)) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0)))) (PreH8 : ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH23 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH24 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH25 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH26 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (IntArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (0 <= (Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0))) ” 
  &&  “ ((Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)) < 100) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= (Znth (i) (input) (0))) ” 
  &&  “ ((Znth (i) (input) (0)) < 100) ” 
  &&  “ (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0))) ” 
  &&  “ ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0))) ” 
  &&  “ forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i ) ”
  &&  (((( &( "count" ) ) + ((Znth (i) (input) (0)) * sizeof(INT)))) # Int  |-> (Znth (Znth (i) (input) (0)) (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) 0))
  **  (IntArray.missing_i ( &( "count" ) ) (Znth (i) (input) (0)) 0 100 (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
.

Definition sort_partial_solve_wit_12 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (output_mixed: (@list (@option Z))) (bucket_ends: (@list Z)) (sorted: (@list Z)) (positions: (@list Z))  __default__App_option_Z (PreH1 : (0 <= (Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)))) (PreH2 : ((Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)) < 100)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (0 <= (Znth (i) (input) (0)))) (PreH6 : ((Znth (i) (input) (0)) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0)))) (PreH8 : ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100)))) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100)))) (PreH23 : forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre)))) (PreH24 : ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0)))) (PreH25 : forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None))) (PreH26 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i )) ,
  (IntArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) )
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.mixed_full ( &( "output" ) ) 100 output_mixed )
|--
  “ (0 <= (Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0))) ” 
  &&  “ ((Znth ((Znth (i) (input) (0))) ((replace_Znth ((Znth (i) (input) (0))) (((Znth ((Znth (i) (input) (0))) (positions) (0)) - 1 )) (positions))) (0)) < 100) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= (Znth (i) (input) (0))) ” 
  &&  “ ((Znth (i) (input) (0)) < 100) ” 
  &&  “ (1 <= (Znth ((Znth (i) (input) (0))) (positions) (0))) ” 
  &&  “ ((Znth ((Znth (i) (input) (0))) (positions) (0)) <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (positions)) = 100) ” 
  &&  “ ((Zlength (bucket_ends)) = 100) ” 
  &&  “ ((Zlength (output_mixed)) = 100) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k input 0)) /\ ((Znth k input 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 sorted 0)) /\ ((Znth k_2 sorted 0) < 100))) ” 
  &&  “ forall (bucket: Z) , (((0 <= bucket) /\ (bucket < 100)) -> ((0 <= (Znth bucket positions 0)) /\ ((Znth bucket positions 0) <= n_pre))) ” 
  &&  “ ((i >= 0) -> (1 <= (Znth (Znth i input 0) positions 0))) ” 
  &&  “ forall (k_3: Z) , (((n_pre <= k_3) /\ (k_3 < 100)) -> ((Znth k_3 output_mixed __default__App_option_Z) = None)) ” 
  &&  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i ) ”
  &&  (((( &( "output" ) ) + ((Znth (Znth (i) (input) (0)) (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i ( &( "output" ) ) (Znth (Znth (i) (input) (0)) (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) 0) 0 100 output_mixed )
  **  (IntArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) (0))) (((Znth (Znth (i) (input) (0)) positions 0) - 1 )) (positions)) )
  **  (IntArray.full a_pre n_pre input )
.

Definition sort_partial_solve_wit_13 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts: (@list Z)) (live: (@list Z)) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) < 100)))) (PreH11 : (CountingSorted input sorted )) (PreH12 : (CountingCopyProgress input sorted live i )) ,
  (IntArray.full a_pre n_pre live )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (live)) = n_pre) ” 
  &&  “ ((Zlength (bucket_starts)) = 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) < 100))) ” 
  &&  “ (CountingSorted input sorted ) ” 
  &&  “ (CountingCopyProgress input sorted live i ) ”
  &&  (((( &( "output" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) sorted 0))
  **  (IntArray.missing_i ( &( "output" ) ) i 0 n_pre sorted )
  **  (IntArray.full a_pre n_pre live )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
.

Definition sort_partial_solve_wit_14 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (bucket_starts: (@list Z)) (live: (@list Z)) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) < 100)))) (PreH11 : (CountingSorted input sorted )) (PreH12 : (CountingCopyProgress input sorted live i )) ,
  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted )
  **  (IntArray.full a_pre n_pre live )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (live)) = n_pre) ” 
  &&  “ ((Zlength (bucket_starts)) = 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) < 100))) ” 
  &&  “ (CountingSorted input sorted ) ” 
  &&  “ (CountingCopyProgress input sorted live i ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre i 0 n_pre live )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre sorted )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 100 )
  **  (IntArray.full ( &( "count" ) ) 100 bucket_starts )
.

Module Type VC_Correct.


Axiom proof_of_sort_safety_wit_1 : sort_safety_wit_1.
Axiom proof_of_sort_safety_wit_2 : sort_safety_wit_2.
Axiom proof_of_sort_safety_wit_3 : sort_safety_wit_3.
Axiom proof_of_sort_safety_wit_4 : sort_safety_wit_4.
Axiom proof_of_sort_safety_wit_5 : sort_safety_wit_5.
Axiom proof_of_sort_safety_wit_6 : sort_safety_wit_6.
Axiom proof_of_sort_safety_wit_7 : sort_safety_wit_7.
Axiom proof_of_sort_safety_wit_8 : sort_safety_wit_8.
Axiom proof_of_sort_safety_wit_9 : sort_safety_wit_9.
Axiom proof_of_sort_safety_wit_10 : sort_safety_wit_10.
Axiom proof_of_sort_safety_wit_11 : sort_safety_wit_11.
Axiom proof_of_sort_safety_wit_12 : sort_safety_wit_12.
Axiom proof_of_sort_safety_wit_13 : sort_safety_wit_13.
Axiom proof_of_sort_safety_wit_14 : sort_safety_wit_14.
Axiom proof_of_sort_safety_wit_15 : sort_safety_wit_15.
Axiom proof_of_sort_safety_wit_16 : sort_safety_wit_16.
Axiom proof_of_sort_safety_wit_17 : sort_safety_wit_17.
Axiom proof_of_sort_safety_wit_18 : sort_safety_wit_18.
Axiom proof_of_sort_safety_wit_19 : sort_safety_wit_19.
Axiom proof_of_sort_safety_wit_20 : sort_safety_wit_20.
Axiom proof_of_sort_entail_wit_1 : sort_entail_wit_1.
Axiom proof_of_sort_entail_wit_2 : sort_entail_wit_2.
Axiom proof_of_sort_entail_wit_3 : sort_entail_wit_3.
Axiom proof_of_sort_entail_wit_4 : sort_entail_wit_4.
Axiom proof_of_sort_entail_wit_5 : sort_entail_wit_5.
Axiom proof_of_sort_entail_wit_6 : sort_entail_wit_6.
Axiom proof_of_sort_entail_wit_7 : sort_entail_wit_7.
Axiom proof_of_sort_entail_wit_8 : sort_entail_wit_8.
Axiom proof_of_sort_entail_wit_9 : sort_entail_wit_9.
Axiom proof_of_sort_entail_wit_10 : sort_entail_wit_10.
Axiom proof_of_sort_entail_wit_11 : sort_entail_wit_11.
Axiom proof_of_sort_entail_wit_12 : sort_entail_wit_12.
Axiom proof_of_sort_entail_wit_13 : sort_entail_wit_13.
Axiom proof_of_sort_entail_wit_14 : sort_entail_wit_14.
Axiom proof_of_sort_entail_wit_15 : sort_entail_wit_15.
Axiom proof_of_sort_entail_wit_16 : sort_entail_wit_16.
Axiom proof_of_sort_return_wit_1 : sort_return_wit_1.
Axiom proof_of_sort_partial_solve_wit_1 : sort_partial_solve_wit_1.
Axiom proof_of_sort_partial_solve_wit_2 : sort_partial_solve_wit_2.
Axiom proof_of_sort_partial_solve_wit_3 : sort_partial_solve_wit_3.
Axiom proof_of_sort_partial_solve_wit_4 : sort_partial_solve_wit_4.
Axiom proof_of_sort_partial_solve_wit_5 : sort_partial_solve_wit_5.
Axiom proof_of_sort_partial_solve_wit_6 : sort_partial_solve_wit_6.
Axiom proof_of_sort_partial_solve_wit_7 : sort_partial_solve_wit_7.
Axiom proof_of_sort_partial_solve_wit_8 : sort_partial_solve_wit_8.
Axiom proof_of_sort_partial_solve_wit_9 : sort_partial_solve_wit_9.
Axiom proof_of_sort_partial_solve_wit_10 : sort_partial_solve_wit_10.
Axiom proof_of_sort_partial_solve_wit_11 : sort_partial_solve_wit_11.
Axiom proof_of_sort_partial_solve_wit_12 : sort_partial_solve_wit_12.
Axiom proof_of_sort_partial_solve_wit_13 : sort_partial_solve_wit_13.
Axiom proof_of_sort_partial_solve_wit_14 : sort_partial_solve_wit_14.

End VC_Correct.
