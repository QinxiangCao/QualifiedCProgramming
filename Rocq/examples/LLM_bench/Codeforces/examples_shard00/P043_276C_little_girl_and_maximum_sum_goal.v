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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P043_276C_little_girl_and_maximum_sum_lib.
Local Open Scope sac.

(*----- Function cmp_ll -----*)

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 200000)) (PreH3 : (1 <= (Zlength (queries)))) (PreH4 : ((Zlength (queries)) <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : (q_pre = (Zlength (queries)))) (PreH9 : ((Zlength (lefts)) = q_pre)) (PreH10 : ((Zlength (rights)) = q_pre)) (PreH11 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  ((( &( "diff" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : (1 <= (Zlength (queries)))) (PreH5 : ((Zlength (queries)) <= 200000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (q_pre = (Zlength (queries)))) (PreH10 : ((Zlength (lefts)) = q_pre)) (PreH11 : ((Zlength (rights)) = q_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  ((( &( "diff" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (IntArray.full left_pre q_pre lefts )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
|--
  “ (((Znth i lefts 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i lefts 0) - 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (IntArray.full left_pre q_pre lefts )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (Int64Array.full diff (n_pre + 1 ) diff_data )
  **  (IntArray.full left_pre q_pre lefts )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) ”
.

Definition solver_safety_wit_6 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (Int64Array.full diff (n_pre + 1 ) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) )
  **  (IntArray.full right_pre q_pre rights )
  **  (IntArray.full left_pre q_pre lefts )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (((Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) 0) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) 0) - 1 )) ”
) \/
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (Int64Array.full diff (n_pre + 1 ) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) )
  **  (IntArray.full right_pre q_pre rights )
  **  (IntArray.full left_pre q_pre lefts )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (((Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) 0) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) 0) - 1 )) ”
).

Definition solver_safety_wit_6_split_goal_1 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (Int64Array.full diff (n_pre + 1 ) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) )
  **  (IntArray.full right_pre q_pre rights )
  **  (IntArray.full left_pre q_pre lefts )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (((Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) 0) - 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_6_split_goal_2 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (Int64Array.full diff (n_pre + 1 ) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) )
  **  (IntArray.full right_pre q_pre rights )
  **  (IntArray.full left_pre q_pre lefts )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((INT64_MIN) <= ((Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) 0) - 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (Int64Array.full diff (n_pre + 1 ) (replace_Znth ((Znth i rights 0)) (((Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) 0) - 1 )) ((replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)))) )
  **  (IntArray.full right_pre q_pre rights )
  **  (IntArray.full left_pre q_pre lefts )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= q_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (0 <= i)) (PreH15 : (i <= q_pre)) (PreH16 : (DifferencePrefix queries n_pre i diff_data )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre)))) ,
  (Int64Array.full diff (n_pre + 1 ) (replace_Znth (i) (((Znth i diff_data 0) + (Znth (i - 1 ) diff_data 0) )) (diff_data)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre)))) ,
  (Int64Array.full diff (n_pre + 1 ) diff_data )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (((Znth i diff_data 0) + (Znth (i - 1 ) diff_data 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i diff_data 0) + (Znth (i - 1 ) diff_data 0) )) ”
.

Definition solver_safety_wit_11 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre)))) ,
  (Int64Array.full diff (n_pre + 1 ) diff_data )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre)))) ,
  (Int64Array.full diff (n_pre + 1 ) diff_data )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (values_sorted: (@list Z)) (frequencies: (@list Z)) (frequencies_sorted: (@list Z)) (tail: (@list Z)) (diff: Z)  __default__Prod_Z_Z (PreH1 : (diff <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (q_pre = (Zlength (queries)))) (PreH4 : ((Zlength (lefts)) = q_pre)) (PreH5 : ((Zlength (rights)) = q_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 200000)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH12 : ((Zlength (values_sorted)) = n_pre)) (PreH13 : ((Zlength (frequencies)) = n_pre)) (PreH14 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH15 : ((Zlength (tail)) = 1)) (PreH16 : (Permutation values values_sorted )) (PreH17 : (increasing values_sorted )) (PreH18 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH19 : (CoverageProfile queries n_pre frequencies )) (PreH20 : (Permutation frequencies frequencies_sorted )) (PreH21 : (increasing frequencies_sorted )) (PreH22 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) ,
  ((( &( "answer" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (values_sorted: (@list Z)) (frequencies: (@list Z)) (frequencies_sorted: (@list Z)) (tail: (@list Z)) (diff: Z)  __default__Prod_Z_Z (PreH1 : (diff <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (q_pre = (Zlength (queries)))) (PreH4 : ((Zlength (lefts)) = q_pre)) (PreH5 : ((Zlength (rights)) = q_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 200000)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH12 : ((Zlength (values_sorted)) = n_pre)) (PreH13 : ((Zlength (frequencies)) = n_pre)) (PreH14 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH15 : ((Zlength (tail)) = 1)) (PreH16 : (Permutation values values_sorted )) (PreH17 : (increasing values_sorted )) (PreH18 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH19 : (CoverageProfile queries n_pre frequencies )) (PreH20 : (Permutation frequencies frequencies_sorted )) (PreH21 : (increasing frequencies_sorted )) (PreH22 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + ((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) ) ))
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ ((answer + ((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (answer + ((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) ) )) ”
) \/
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ ((answer + ((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (answer + ((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) ) )) ”
).

Definition solver_safety_wit_16_split_goal_1 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ ((answer + ((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_16_split_goal_2 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ ((INT64_MIN) <= (answer + ((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) ) )) ”
.

Definition solver_safety_wit_17 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) )) ”
) \/
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) )) ”
).

Definition solver_safety_wit_17_split_goal_1 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_17_split_goal_2 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ ((INT64_MIN) <= ((Znth i values_sorted 0) * (Znth i (app (frequencies_sorted) (tail)) 0) )) ”
.

Definition solver_entail_wit_1 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : (1 <= (Zlength (queries)))) (PreH5 : ((Zlength (queries)) <= 200000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (q_pre = (Zlength (queries)))) (PreH10 : ((Zlength (lefts)) = q_pre)) (PreH11 : ((Zlength (rights)) = q_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  (Int64Array.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  EX (diff_data: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (DifferencePrefix queries n_pre 0 diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-0) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= 0))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full retval (n_pre + 1 ) diff_data )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : (1 <= (Zlength (queries)))) (PreH5 : ((Zlength (queries)) <= 200000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (q_pre = (Zlength (queries)))) (PreH10 : ((Zlength (lefts)) = q_pre)) (PreH11 : ((Zlength (rights)) = q_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  TT && emp 
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-0) <= (Znth k_4 (repeat_Z (0) ((n_pre + 1 ))) 0)) /\ ((Znth k_4 (repeat_Z (0) ((n_pre + 1 ))) 0) <= 0))) ” 
  &&  “ (DifferencePrefix queries n_pre 0 (repeat_Z (0) ((n_pre + 1 ))) ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : (1 <= (Zlength (queries)))) (PreH5 : ((Zlength (queries)) <= 200000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (q_pre = (Zlength (queries)))) (PreH10 : ((Zlength (lefts)) = q_pre)) (PreH11 : ((Zlength (rights)) = q_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-0) <= (Znth k_4 (repeat_Z (0) ((n_pre + 1 ))) 0)) /\ ((Znth k_4 (repeat_Z (0) ((n_pre + 1 ))) 0) <= 0)))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : (1 <= (Zlength (queries)))) (PreH5 : ((Zlength (queries)) <= 200000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (q_pre = (Zlength (queries)))) (PreH10 : ((Zlength (lefts)) = q_pre)) (PreH11 : ((Zlength (rights)) = q_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  (DifferencePrefix queries n_pre 0 (repeat_Z (0) ((n_pre + 1 ))) )
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : (1 <= (Zlength (queries)))) (PreH5 : ((Zlength (queries)) <= 200000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (q_pre = (Zlength (queries)))) (PreH10 : ((Zlength (lefts)) = q_pre)) (PreH11 : ((Zlength (rights)) = q_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : (1 <= (Zlength (queries)))) (PreH5 : ((Zlength (queries)) <= 200000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (q_pre = (Zlength (queries)))) (PreH10 : ((Zlength (lefts)) = q_pre)) (PreH11 : ((Zlength (rights)) = q_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))
.

Definition solver_entail_wit_1_split_goal_5 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : (1 <= (Zlength (queries)))) (PreH5 : ((Zlength (queries)) <= 200000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : (q_pre = (Zlength (queries)))) (PreH10 : ((Zlength (lefts)) = q_pre)) (PreH11 : ((Zlength (rights)) = q_pre)) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))
.

Definition solver_entail_wit_2 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < q_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (0 <= i)) (PreH15 : (i <= q_pre)) (PreH16 : (DifferencePrefix queries n_pre i diff_data )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
|--
  “ (0 <= ((Znth i lefts 0) - 1 )) ” 
  &&  “ (((Znth i lefts 0) - 1 ) < n_pre) ” 
  &&  “ (0 <= (Znth i rights 0)) ” 
  &&  “ ((Znth i rights 0) <= n_pre) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (DifferencePrefix queries n_pre i diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i <= INT_MAX)) (PreH2 : (q_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (q_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < q_pre)) (PreH8 : (diff <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (q_pre = (Zlength (queries)))) (PreH11 : ((Zlength (lefts)) = q_pre)) (PreH12 : ((Zlength (rights)) = q_pre)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= 200000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (DifferencePrefix queries n_pre i diff_data )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  TT && emp 
|--
  “ ((Znth i rights 0) <= n_pre) ” 
  &&  “ (0 <= (Znth i rights 0)) ” 
  &&  “ (((Znth i lefts 0) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth i lefts 0) - 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i <= INT_MAX)) (PreH2 : (q_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (q_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < q_pre)) (PreH8 : (diff <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (q_pre = (Zlength (queries)))) (PreH11 : ((Zlength (lefts)) = q_pre)) (PreH12 : ((Zlength (rights)) = q_pre)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= 200000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (DifferencePrefix queries n_pre i diff_data )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  ((Znth i rights 0) <= n_pre)
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i <= INT_MAX)) (PreH2 : (q_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (q_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < q_pre)) (PreH8 : (diff <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (q_pre = (Zlength (queries)))) (PreH11 : ((Zlength (lefts)) = q_pre)) (PreH12 : ((Zlength (rights)) = q_pre)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= 200000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (DifferencePrefix queries n_pre i diff_data )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (0 <= (Znth i rights 0))
.

Definition solver_entail_wit_2_split_goal_3 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i <= INT_MAX)) (PreH2 : (q_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (q_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < q_pre)) (PreH8 : (diff <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (q_pre = (Zlength (queries)))) (PreH11 : ((Zlength (lefts)) = q_pre)) (PreH12 : ((Zlength (rights)) = q_pre)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= 200000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (DifferencePrefix queries n_pre i diff_data )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (((Znth i lefts 0) - 1 ) < n_pre)
.

Definition solver_entail_wit_2_split_goal_4 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i <= INT_MAX)) (PreH2 : (q_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (q_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < q_pre)) (PreH8 : (diff <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (q_pre = (Zlength (queries)))) (PreH11 : ((Zlength (lefts)) = q_pre)) (PreH12 : ((Zlength (rights)) = q_pre)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (1 <= q_pre)) (PreH16 : (q_pre <= 200000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (DifferencePrefix queries n_pre i diff_data )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (0 <= ((Znth i lefts 0) - 1 ))
.

Definition solver_entail_wit_3 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data_2 )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data_2 0)) /\ ((Znth k_4 diff_data_2 0) <= i)))) ,
  (Int64Array.full diff (n_pre + 1 ) (replace_Znth ((Znth i rights 0)) (((Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data_2 0) + 1 )) (diff_data_2)) 0) - 1 )) ((replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data_2 0) + 1 )) (diff_data_2)))) )
  **  (IntArray.full right_pre q_pre rights )
  **  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
|--
  EX (diff_data: (@list Z)) ,
  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= q_pre) ” 
  &&  “ (DifferencePrefix queries n_pre (i + 1 ) diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-(i + 1 )) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= (i + 1 )))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data_2 )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data_2 0)) /\ ((Znth k_4 diff_data_2 0) <= i)))) ,
  TT && emp 
|--
  “ (DifferencePrefix queries n_pre (i + 1 ) (replace_Znth ((Znth i rights 0)) (((Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data_2 0) + 1 )) (diff_data_2)) 0) - 1 )) ((replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data_2 0) + 1 )) (diff_data_2)))) ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data_2 )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data_2 0)) /\ ((Znth k_4 diff_data_2 0) <= i)))) ,
  (DifferencePrefix queries n_pre (i + 1 ) (replace_Znth ((Znth i rights 0)) (((Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data_2 0) + 1 )) (diff_data_2)) 0) - 1 )) ((replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data_2 0) + 1 )) (diff_data_2)))) )
.

Definition solver_entail_wit_4 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= q_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < q_pre)) -> (((fst ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 lefts 0) - 1 )) /\ ((snd ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 rights 0) - 1 ))))) (PreH14 : (0 <= i)) (PreH15 : (i <= q_pre)) (PreH16 : (DifferencePrefix queries n_pre i diff_data_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (n_pre + 1 ))) -> (((-i) <= (Znth k_8 diff_data_2 0)) /\ ((Znth k_8 diff_data_2 0) <= i)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data_2 )
|--
  EX (diff_data: (@list Z)) ,
  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (CoveragePrefixState queries n_pre 1 diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= q_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < q_pre)) -> (((fst ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 lefts 0) - 1 )) /\ ((snd ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 rights 0) - 1 ))))) (PreH14 : (0 <= i)) (PreH15 : (i <= q_pre)) (PreH16 : (DifferencePrefix queries n_pre i diff_data_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (n_pre + 1 ))) -> (((-i) <= (Znth k_8 diff_data_2 0)) /\ ((Znth k_8 diff_data_2 0) <= i)))) ,
  TT && emp 
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data_2 0)) /\ ((Znth k_4 diff_data_2 0) <= q_pre))) ” 
  &&  “ (CoveragePrefixState queries n_pre 1 diff_data_2 ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= q_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < q_pre)) -> (((fst ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 lefts 0) - 1 )) /\ ((snd ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 rights 0) - 1 ))))) (PreH14 : (0 <= i)) (PreH15 : (i <= q_pre)) (PreH16 : (DifferencePrefix queries n_pre i diff_data_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (n_pre + 1 ))) -> (((-i) <= (Znth k_8 diff_data_2 0)) /\ ((Znth k_8 diff_data_2 0) <= i)))) ,
  forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data_2 0)) /\ ((Znth k_4 diff_data_2 0) <= q_pre)))
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= q_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < q_pre)) -> (((fst ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 lefts 0) - 1 )) /\ ((snd ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 rights 0) - 1 ))))) (PreH14 : (0 <= i)) (PreH15 : (i <= q_pre)) (PreH16 : (DifferencePrefix queries n_pre i diff_data_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (n_pre + 1 ))) -> (((-i) <= (Znth k_8 diff_data_2 0)) /\ ((Znth k_8 diff_data_2 0) <= i)))) ,
  (CoveragePrefixState queries n_pre 1 diff_data_2 )
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= q_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < q_pre)) -> (((fst ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 lefts 0) - 1 )) /\ ((snd ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 rights 0) - 1 ))))) (PreH14 : (0 <= i)) (PreH15 : (i <= q_pre)) (PreH16 : (DifferencePrefix queries n_pre i diff_data_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (n_pre + 1 ))) -> (((-i) <= (Znth k_8 diff_data_2 0)) /\ ((Znth k_8 diff_data_2 0) <= i)))) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))
.

Definition solver_entail_wit_4_split_goal_4 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= q_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < q_pre)) -> (((fst ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 lefts 0) - 1 )) /\ ((snd ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 rights 0) - 1 ))))) (PreH14 : (0 <= i)) (PreH15 : (i <= q_pre)) (PreH16 : (DifferencePrefix queries n_pre i diff_data_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (n_pre + 1 ))) -> (((-i) <= (Znth k_8 diff_data_2 0)) /\ ((Znth k_8 diff_data_2 0) <= i)))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))
.

Definition solver_entail_wit_4_split_goal_5 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= q_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < q_pre)) -> (((fst ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 lefts 0) - 1 )) /\ ((snd ((Znth k_7 queries __default__Prod_Z_Z))) = ((Znth k_7 rights 0) - 1 ))))) (PreH14 : (0 <= i)) (PreH15 : (i <= q_pre)) (PreH16 : (DifferencePrefix queries n_pre i diff_data_2 )) (PreH17 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (n_pre + 1 ))) -> (((-i) <= (Znth k_8 diff_data_2 0)) /\ ((Znth k_8 diff_data_2 0) <= i)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))
.

Definition solver_entail_wit_5 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data_2 )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data_2 0)) /\ ((Znth k_4 diff_data_2 0) <= q_pre)))) ,
  (Int64Array.full diff (n_pre + 1 ) (replace_Znth (i) (((Znth i diff_data_2 0) + (Znth (i - 1 ) diff_data_2 0) )) (diff_data_2)) )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  EX (diff_data: (@list Z)) ,
  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (CoveragePrefixState queries n_pre (i + 1 ) diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data_2 )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data_2 0)) /\ ((Znth k_4 diff_data_2 0) <= q_pre)))) ,
  TT && emp 
|--
  “ (CoveragePrefixState queries n_pre (i + 1 ) (replace_Znth (i) (((Znth i diff_data_2 0) + (Znth (i - 1 ) diff_data_2 0) )) (diff_data_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data_2 )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data_2 0)) /\ ((Znth k_4 diff_data_2 0) <= q_pre)))) ,
  (CoveragePrefixState queries n_pre (i + 1 ) (replace_Znth (i) (((Znth i diff_data_2 0) + (Znth (i - 1 ) diff_data_2 0) )) (diff_data_2)) )
.

Definition solver_entail_wit_6 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 values 0)) /\ ((Znth k_4 values 0) <= 200000)))) (PreH12 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < q_pre)) -> (((0 <= (fst ((Znth k_5 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_5 queries __default__Prod_Z_Z))) <= (snd ((Znth k_5 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_5 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((fst ((Znth k_6 queries __default__Prod_Z_Z))) = ((Znth k_6 lefts 0) - 1 )) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) = ((Znth k_6 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data )) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_7 diff_data 0)) /\ ((Znth k_7 diff_data 0) <= q_pre)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
|--
  EX (tail: (@list Z))  (frequencies: (@list Z)) ,
  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 frequencies 0)) /\ ((Znth k_3 frequencies 0) <= q_pre))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff n_pre frequencies )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 values 0)) /\ ((Znth k_4 values 0) <= 200000)))) (PreH12 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < q_pre)) -> (((0 <= (fst ((Znth k_5 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_5 queries __default__Prod_Z_Z))) <= (snd ((Znth k_5 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_5 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((fst ((Znth k_6 queries __default__Prod_Z_Z))) = ((Znth k_6 lefts 0) - 1 )) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) = ((Znth k_6 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data )) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_7 diff_data 0)) /\ ((Znth k_7 diff_data 0) <= q_pre)))) ,
  (Int64Array.full diff (n_pre + 1 ) diff_data )
|--
  EX (tail: (@list Z))  (frequencies: (@list Z)) ,
  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 frequencies 0)) /\ ((Znth k_3 frequencies 0) <= q_pre))) ”
  &&  (Int64Array.full diff n_pre frequencies )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail )
).

Definition solver_entail_wit_7 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (frequencies_2: (@list Z)) (tail_2: (@list Z)) (diff: Z) (sorted: (@list Z))  __default__Prod_Z_Z (PreH1 : (Permutation values sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (diff <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (q_pre = (Zlength (queries)))) (PreH7 : ((Zlength (lefts)) = q_pre)) (PreH8 : ((Zlength (rights)) = q_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= q_pre)) (PreH12 : (q_pre <= 200000)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH15 : ((Zlength (frequencies_2)) = n_pre)) (PreH16 : ((Zlength (tail_2)) = 1)) (PreH17 : (CoverageProfile queries n_pre frequencies_2 )) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((0 <= (Znth k_7 frequencies_2 0)) /\ ((Znth k_7 frequencies_2 0) <= q_pre)))) ,
  (Int64Array.full a_pre n_pre sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff n_pre frequencies_2 )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail_2 )
|--
  EX (tail: (@list Z))  (frequencies: (@list Z))  (values_sorted: (@list Z)) ,
  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ ((Zlength (values_sorted)) = n_pre) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (Permutation values values_sorted ) ” 
  &&  “ (increasing values_sorted ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000))) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies 0)) /\ ((Znth k_4 frequencies 0) <= q_pre))) ”
  &&  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff n_pre frequencies )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (frequencies_2: (@list Z)) (tail_2: (@list Z)) (diff: Z) (sorted: (@list Z))  __default__Prod_Z_Z (PreH1 : (Permutation values sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (diff <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (q_pre = (Zlength (queries)))) (PreH7 : ((Zlength (lefts)) = q_pre)) (PreH8 : ((Zlength (rights)) = q_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= q_pre)) (PreH12 : (q_pre <= 200000)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH15 : ((Zlength (frequencies_2)) = n_pre)) (PreH16 : ((Zlength (tail_2)) = 1)) (PreH17 : (CoverageProfile queries n_pre frequencies_2 )) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((0 <= (Znth k_7 frequencies_2 0)) /\ ((Znth k_7 frequencies_2 0) <= q_pre)))) ,
  TT && emp 
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_2 0)) /\ ((Znth k_4 frequencies_2 0) <= q_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 sorted 0)) /\ ((Znth k_3 sorted 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (frequencies_2: (@list Z)) (tail_2: (@list Z)) (diff: Z) (sorted: (@list Z))  __default__Prod_Z_Z (PreH1 : (Permutation values sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (diff <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (q_pre = (Zlength (queries)))) (PreH7 : ((Zlength (lefts)) = q_pre)) (PreH8 : ((Zlength (rights)) = q_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= q_pre)) (PreH12 : (q_pre <= 200000)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH15 : ((Zlength (frequencies_2)) = n_pre)) (PreH16 : ((Zlength (tail_2)) = 1)) (PreH17 : (CoverageProfile queries n_pre frequencies_2 )) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((0 <= (Znth k_7 frequencies_2 0)) /\ ((Znth k_7 frequencies_2 0) <= q_pre)))) ,
  forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_2 0)) /\ ((Znth k_4 frequencies_2 0) <= q_pre)))
.

Definition solver_entail_wit_7_split_goal_2 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (frequencies_2: (@list Z)) (tail_2: (@list Z)) (diff: Z) (sorted: (@list Z))  __default__Prod_Z_Z (PreH1 : (Permutation values sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (diff <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (q_pre = (Zlength (queries)))) (PreH7 : ((Zlength (lefts)) = q_pre)) (PreH8 : ((Zlength (rights)) = q_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= q_pre)) (PreH12 : (q_pre <= 200000)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH15 : ((Zlength (frequencies_2)) = n_pre)) (PreH16 : ((Zlength (tail_2)) = 1)) (PreH17 : (CoverageProfile queries n_pre frequencies_2 )) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((0 <= (Znth k_7 frequencies_2 0)) /\ ((Znth k_7 frequencies_2 0) <= q_pre)))) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 sorted 0)) /\ ((Znth k_3 sorted 0) <= 200000)))
.

Definition solver_entail_wit_7_split_goal_3 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (frequencies_2: (@list Z)) (tail_2: (@list Z)) (diff: Z) (sorted: (@list Z))  __default__Prod_Z_Z (PreH1 : (Permutation values sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (diff <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (q_pre = (Zlength (queries)))) (PreH7 : ((Zlength (lefts)) = q_pre)) (PreH8 : ((Zlength (rights)) = q_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= q_pre)) (PreH12 : (q_pre <= 200000)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH15 : ((Zlength (frequencies_2)) = n_pre)) (PreH16 : ((Zlength (tail_2)) = 1)) (PreH17 : (CoverageProfile queries n_pre frequencies_2 )) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((0 <= (Znth k_7 frequencies_2 0)) /\ ((Znth k_7 frequencies_2 0) <= q_pre)))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))
.

Definition solver_entail_wit_7_split_goal_4 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (frequencies_2: (@list Z)) (tail_2: (@list Z)) (diff: Z) (sorted: (@list Z))  __default__Prod_Z_Z (PreH1 : (Permutation values sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (diff <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (q_pre = (Zlength (queries)))) (PreH7 : ((Zlength (lefts)) = q_pre)) (PreH8 : ((Zlength (rights)) = q_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= q_pre)) (PreH12 : (q_pre <= 200000)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH15 : ((Zlength (frequencies_2)) = n_pre)) (PreH16 : ((Zlength (tail_2)) = 1)) (PreH17 : (CoverageProfile queries n_pre frequencies_2 )) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((0 <= (Znth k_7 frequencies_2 0)) /\ ((Znth k_7 frequencies_2 0) <= q_pre)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))
.

Definition solver_entail_wit_8 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (values_sorted_2: (@list Z)) (frequencies_2: (@list Z)) (tail_2: (@list Z)) (diff: Z) (sorted: (@list Z))  __default__Prod_Z_Z (PreH1 : (Permutation frequencies_2 sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (diff <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (q_pre = (Zlength (queries)))) (PreH7 : ((Zlength (lefts)) = q_pre)) (PreH8 : ((Zlength (rights)) = q_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= q_pre)) (PreH12 : (q_pre <= 200000)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH15 : ((Zlength (values_sorted_2)) = n_pre)) (PreH16 : ((Zlength (frequencies_2)) = n_pre)) (PreH17 : ((Zlength (tail_2)) = 1)) (PreH18 : (Permutation values values_sorted_2 )) (PreH19 : (increasing values_sorted_2 )) (PreH20 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 values_sorted_2 0)) /\ ((Znth k_7 values_sorted_2 0) <= 200000)))) (PreH21 : (CoverageProfile queries n_pre frequencies_2 )) (PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((0 <= (Znth k_8 frequencies_2 0)) /\ ((Znth k_8 frequencies_2 0) <= q_pre)))) ,
  (Int64Array.full diff n_pre sorted )
  **  (Int64Array.full a_pre n_pre values_sorted_2 )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail_2 )
|--
  EX (tail: (@list Z))  (frequencies_sorted: (@list Z))  (frequencies: (@list Z))  (values_sorted: (@list Z)) ,
  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ ((Zlength (values_sorted)) = n_pre) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (frequencies_sorted)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (Permutation values values_sorted ) ” 
  &&  “ (increasing values_sorted ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000))) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ (Permutation frequencies frequencies_sorted ) ” 
  &&  “ (increasing frequencies_sorted ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre))) ”
  &&  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (values_sorted_2: (@list Z)) (frequencies_2: (@list Z)) (tail_2: (@list Z)) (diff: Z) (sorted: (@list Z))  __default__Prod_Z_Z (PreH1 : (Permutation frequencies_2 sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (diff <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (q_pre = (Zlength (queries)))) (PreH7 : ((Zlength (lefts)) = q_pre)) (PreH8 : ((Zlength (rights)) = q_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= q_pre)) (PreH12 : (q_pre <= 200000)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH15 : ((Zlength (values_sorted_2)) = n_pre)) (PreH16 : ((Zlength (frequencies_2)) = n_pre)) (PreH17 : ((Zlength (tail_2)) = 1)) (PreH18 : (Permutation values values_sorted_2 )) (PreH19 : (increasing values_sorted_2 )) (PreH20 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 values_sorted_2 0)) /\ ((Znth k_7 values_sorted_2 0) <= 200000)))) (PreH21 : (CoverageProfile queries n_pre frequencies_2 )) (PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((0 <= (Znth k_8 frequencies_2 0)) /\ ((Znth k_8 frequencies_2 0) <= q_pre)))) ,
  (Int64Array.full diff n_pre sorted )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail_2 )
|--
  EX (tail: (@list Z))  (frequencies_sorted: (@list Z))  (frequencies: (@list Z)) ,
  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ ((Zlength (values_sorted_2)) = n_pre) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (frequencies_sorted)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (Permutation values values_sorted_2 ) ” 
  &&  “ (increasing values_sorted_2 ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted_2 0)) /\ ((Znth k_3 values_sorted_2 0) <= 200000))) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ (Permutation frequencies frequencies_sorted ) ” 
  &&  “ (increasing frequencies_sorted ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre))) ”
  &&  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
).

Definition solver_entail_wit_9 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (values_sorted_2: (@list Z)) (frequencies_2: (@list Z)) (frequencies_sorted_2: (@list Z)) (tail_2: (@list Z)) (diff: Z)  __default__Prod_Z_Z (PreH1 : (diff <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (q_pre = (Zlength (queries)))) (PreH4 : ((Zlength (lefts)) = q_pre)) (PreH5 : ((Zlength (rights)) = q_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 200000)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH12 : ((Zlength (values_sorted_2)) = n_pre)) (PreH13 : ((Zlength (frequencies_2)) = n_pre)) (PreH14 : ((Zlength (frequencies_sorted_2)) = n_pre)) (PreH15 : ((Zlength (tail_2)) = 1)) (PreH16 : (Permutation values values_sorted_2 )) (PreH17 : (increasing values_sorted_2 )) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 values_sorted_2 0)) /\ ((Znth k_7 values_sorted_2 0) <= 200000)))) (PreH19 : (CoverageProfile queries n_pre frequencies_2 )) (PreH20 : (Permutation frequencies_2 frequencies_sorted_2 )) (PreH21 : (increasing frequencies_sorted_2 )) (PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((0 <= (Znth k_8 frequencies_sorted_2 0)) /\ ((Znth k_8 frequencies_sorted_2 0) <= q_pre)))) ,
  (Int64Array.full a_pre n_pre values_sorted_2 )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted_2) (tail_2)) )
|--
  EX (tail: (@list Z))  (frequencies_sorted: (@list Z))  (frequencies: (@list Z))  (values_sorted: (@list Z)) ,
  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (values_sorted)) = n_pre) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (frequencies_sorted)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (Permutation values values_sorted ) ” 
  &&  “ (increasing values_sorted ) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ (Permutation frequencies frequencies_sorted ) ” 
  &&  “ (increasing frequencies_sorted ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((0 * 200000 ) * q_pre )) ” 
  &&  “ (DotProductPrefix values_sorted frequencies_sorted 0 0 ) ”
  &&  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (values_sorted_2: (@list Z)) (frequencies_2: (@list Z)) (frequencies_sorted_2: (@list Z)) (tail_2: (@list Z)) (diff: Z)  __default__Prod_Z_Z (PreH1 : (diff <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (q_pre = (Zlength (queries)))) (PreH4 : ((Zlength (lefts)) = q_pre)) (PreH5 : ((Zlength (rights)) = q_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 200000)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 values 0)) /\ ((Znth k_5 values 0) <= 200000)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < q_pre)) -> (((0 <= (fst ((Znth k_6 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_6 queries __default__Prod_Z_Z))) <= (snd ((Znth k_6 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_6 queries __default__Prod_Z_Z))) < n_pre)))) (PreH12 : ((Zlength (values_sorted_2)) = n_pre)) (PreH13 : ((Zlength (frequencies_2)) = n_pre)) (PreH14 : ((Zlength (frequencies_sorted_2)) = n_pre)) (PreH15 : ((Zlength (tail_2)) = 1)) (PreH16 : (Permutation values values_sorted_2 )) (PreH17 : (increasing values_sorted_2 )) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 values_sorted_2 0)) /\ ((Znth k_7 values_sorted_2 0) <= 200000)))) (PreH19 : (CoverageProfile queries n_pre frequencies_2 )) (PreH20 : (Permutation frequencies_2 frequencies_sorted_2 )) (PreH21 : (increasing frequencies_sorted_2 )) (PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < n_pre)) -> ((0 <= (Znth k_8 frequencies_sorted_2 0)) /\ ((Znth k_8 frequencies_sorted_2 0) <= q_pre)))) ,
  TT && emp 
|--
  EX (tail: (@list Z))  (frequencies_sorted: (@list Z))  (frequencies: (@list Z)) ,
  “ ((app (frequencies_sorted_2) (tail_2)) = (app (frequencies_sorted) (tail))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (values))) ” 
  &&  “ ((Zlength (frequencies)) = (Zlength (values))) ” 
  &&  “ ((Zlength (frequencies_sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (CoverageProfile queries (Zlength (values)) frequencies ) ” 
  &&  “ (Permutation frequencies frequencies_sorted ) ” 
  &&  “ (increasing frequencies_sorted ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (values)))) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= (Zlength (queries))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((0 * 200000 ) * (Zlength (queries)) )) ” 
  &&  “ (DotProductPrefix values_sorted_2 frequencies_sorted 0 0 ) ”
  &&  emp
).

Definition solver_entail_wit_10 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail_2: (@list Z)) (frequencies_sorted_2: (@list Z)) (frequencies_2: (@list Z)) (values_sorted_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted_2)) = n_pre)) (PreH16 : ((Zlength (frequencies_2)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted_2)) = n_pre)) (PreH18 : ((Zlength (tail_2)) = 1)) (PreH19 : (Permutation values values_sorted_2 )) (PreH20 : (increasing values_sorted_2 )) (PreH21 : (CoverageProfile queries n_pre frequencies_2 )) (PreH22 : (Permutation frequencies_2 frequencies_sorted_2 )) (PreH23 : (increasing frequencies_sorted_2 )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted_2 0)) /\ ((Znth k_3 values_sorted_2 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted_2 0)) /\ ((Znth k_4 frequencies_sorted_2 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted_2 frequencies_sorted_2 i answer )) ,
  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted_2) (tail_2)) )
  **  (Int64Array.full a_pre n_pre values_sorted_2 )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  EX (tail: (@list Z))  (frequencies_sorted: (@list Z))  (frequencies: (@list Z))  (values_sorted: (@list Z)) ,
  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (values_sorted)) = n_pre) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (frequencies_sorted)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (Permutation values values_sorted ) ” 
  &&  “ (increasing values_sorted ) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ (Permutation frequencies frequencies_sorted ) ” 
  &&  “ (increasing frequencies_sorted ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre))) ” 
  &&  “ (0 <= (answer + ((Znth i values_sorted_2 0) * (Znth i (app (frequencies_sorted_2) (tail_2)) 0) ) )) ” 
  &&  “ ((answer + ((Znth i values_sorted_2 0) * (Znth i (app (frequencies_sorted_2) (tail_2)) 0) ) ) <= (((i + 1 ) * 200000 ) * q_pre )) ” 
  &&  “ (DotProductPrefix values_sorted frequencies_sorted (i + 1 ) (answer + ((Znth i values_sorted_2 0) * (Znth i (app (frequencies_sorted_2) (tail_2)) 0) ) ) ) ”
  &&  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail_2: (@list Z)) (frequencies_sorted_2: (@list Z)) (frequencies_2: (@list Z)) (values_sorted_2: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted_2)) = n_pre)) (PreH16 : ((Zlength (frequencies_2)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted_2)) = n_pre)) (PreH18 : ((Zlength (tail_2)) = 1)) (PreH19 : (Permutation values values_sorted_2 )) (PreH20 : (increasing values_sorted_2 )) (PreH21 : (CoverageProfile queries n_pre frequencies_2 )) (PreH22 : (Permutation frequencies_2 frequencies_sorted_2 )) (PreH23 : (increasing frequencies_sorted_2 )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted_2 0)) /\ ((Znth k_3 values_sorted_2 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted_2 0)) /\ ((Znth k_4 frequencies_sorted_2 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted_2 frequencies_sorted_2 i answer )) ,
  TT && emp 
|--
  EX (tail: (@list Z))  (frequencies_sorted: (@list Z))  (frequencies: (@list Z)) ,
  “ ((app (frequencies_sorted_2) (tail_2)) = (app (frequencies_sorted) (tail))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (values))) ” 
  &&  “ ((Zlength (frequencies)) = (Zlength (values))) ” 
  &&  “ ((Zlength (frequencies_sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (CoverageProfile queries (Zlength (values)) frequencies ) ” 
  &&  “ (Permutation frequencies frequencies_sorted ) ” 
  &&  “ (increasing frequencies_sorted ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (values)))) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= (Zlength (queries))))) ” 
  &&  “ (0 <= (answer + ((Znth i values_sorted_2 0) * (Znth i (app (frequencies_sorted_2) (tail_2)) 0) ) )) ” 
  &&  “ ((answer + ((Znth i values_sorted_2 0) * (Znth i (app (frequencies_sorted_2) (tail_2)) 0) ) ) <= (((i + 1 ) * 200000 ) * (Zlength (queries)) )) ” 
  &&  “ (DotProductPrefix values_sorted_2 frequencies_sorted (i + 1 ) (answer + ((Znth i values_sorted_2 0) * (Znth i (app (frequencies_sorted_2) (tail_2)) 0) ) ) ) ”
  &&  emp
).

Definition solver_return_wit_1 := 
(
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  EX (values_after: (@list Z)) ,
  “ (Spec values queries answer ) ” 
  &&  “ (Permutation values values_after ) ”
  &&  (Int64Array.full a_pre n_pre values_after )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
) \/
(
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  TT && emp 
|--
  “ (Spec values queries answer ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Spec values queries answer )
.

Definition solver_partial_solve_wit_1_pure := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 200000)) (PreH3 : (1 <= (Zlength (queries)))) (PreH4 : ((Zlength (queries)) <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : (q_pre = (Zlength (queries)))) (PreH9 : ((Zlength (lefts)) = q_pre)) (PreH10 : ((Zlength (rights)) = q_pre)) (PreH11 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  ((( &( "diff" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (0 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 200000)) (PreH3 : (1 <= (Zlength (queries)))) (PreH4 : ((Zlength (queries)) <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values)))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : (q_pre = (Zlength (queries)))) (PreH9 : ((Zlength (lefts)) = q_pre)) (PreH10 : ((Zlength (rights)) = q_pre)) (PreH11 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 ))))) ,
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (0 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (1 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 200000) ” 
  &&  “ (1 <= (Zlength (queries))) ” 
  &&  “ ((Zlength (queries)) <= 200000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (queries)))) -> (((0 <= (fst ((Znth i_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 queries __default__Prod_Z_Z))) <= (snd ((Znth i_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 queries __default__Prod_Z_Z))) < (Zlength (values))))) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> (((fst ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 lefts 0) - 1 )) /\ ((snd ((Znth i_3 queries __default__Prod_Z_Z))) = ((Znth i_3 rights 0) - 1 )))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
|--
  “ (0 <= ((Znth i lefts 0) - 1 )) ” 
  &&  “ (((Znth i lefts 0) - 1 ) < n_pre) ” 
  &&  “ (0 <= (Znth i rights 0)) ” 
  &&  “ ((Znth i rights 0) <= n_pre) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (DifferencePrefix queries n_pre i diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i))) ”
  &&  (((left_pre + (i * sizeof(INT)))) # Int  |-> (Znth i lefts 0))
  **  (IntArray.missing_i left_pre i 0 q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
.

Definition solver_partial_solve_wit_3 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
|--
  “ (0 <= ((Znth i lefts 0) - 1 )) ” 
  &&  “ (((Znth i lefts 0) - 1 ) < n_pre) ” 
  &&  “ (0 <= (Znth i rights 0)) ” 
  &&  “ ((Znth i rights 0) <= n_pre) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (DifferencePrefix queries n_pre i diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i))) ”
  &&  (((diff + (((Znth i lefts 0) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((Znth i lefts 0) - 1 ) diff_data 0))
  **  (Int64Array.missing_i diff ((Znth i lefts 0) - 1 ) 0 (n_pre + 1 ) diff_data )
  **  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full right_pre q_pre rights )
.

Definition solver_partial_solve_wit_4 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (Int64Array.full diff (n_pre + 1 ) diff_data )
  **  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (0 <= ((Znth i lefts 0) - 1 )) ” 
  &&  “ (((Znth i lefts 0) - 1 ) < n_pre) ” 
  &&  “ (0 <= (Znth i rights 0)) ” 
  &&  “ ((Znth i rights 0) <= n_pre) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (DifferencePrefix queries n_pre i diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i))) ”
  &&  (((diff + (((Znth i lefts 0) - 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i diff ((Znth i lefts 0) - 1 ) 0 (n_pre + 1 ) diff_data )
  **  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full right_pre q_pre rights )
.

Definition solver_partial_solve_wit_5 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (Int64Array.full diff (n_pre + 1 ) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) )
  **  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (0 <= ((Znth i lefts 0) - 1 )) ” 
  &&  “ (((Znth i lefts 0) - 1 ) < n_pre) ” 
  &&  “ (0 <= (Znth i rights 0)) ” 
  &&  “ ((Znth i rights 0) <= n_pre) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (DifferencePrefix queries n_pre i diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i))) ”
  &&  (((right_pre + (i * sizeof(INT)))) # Int  |-> (Znth i rights 0))
  **  (IntArray.missing_i right_pre i 0 q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) )
  **  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_6 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) )
  **  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= ((Znth i lefts 0) - 1 )) ” 
  &&  “ (((Znth i lefts 0) - 1 ) < n_pre) ” 
  &&  “ (0 <= (Znth i rights 0)) ” 
  &&  “ ((Znth i rights 0) <= n_pre) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (DifferencePrefix queries n_pre i diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i))) ”
  &&  (((diff + ((Znth i rights 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i rights 0) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) 0))
  **  (Int64Array.missing_i diff (Znth i rights 0) 0 (n_pre + 1 ) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) )
  **  (IntArray.full right_pre q_pre rights )
  **  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_7 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (0 <= ((Znth i lefts 0) - 1 ))) (PreH2 : (((Znth i lefts 0) - 1 ) < n_pre)) (PreH3 : (0 <= (Znth i rights 0))) (PreH4 : ((Znth i rights 0) <= n_pre)) (PreH5 : (q_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < q_pre)) (PreH10 : (diff <> 0)) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : (q_pre = (Zlength (queries)))) (PreH13 : ((Zlength (lefts)) = q_pre)) (PreH14 : ((Zlength (rights)) = q_pre)) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= q_pre)) (PreH18 : (q_pre <= 200000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH22 : (0 <= i)) (PreH23 : (i <= q_pre)) (PreH24 : (DifferencePrefix queries n_pre i diff_data )) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i)))) ,
  (Int64Array.full diff (n_pre + 1 ) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) )
  **  (IntArray.full right_pre q_pre rights )
  **  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (0 <= ((Znth i lefts 0) - 1 )) ” 
  &&  “ (((Znth i lefts 0) - 1 ) < n_pre) ” 
  &&  “ (0 <= (Znth i rights 0)) ” 
  &&  “ ((Znth i rights 0) <= n_pre) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (DifferencePrefix queries n_pre i diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-i) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= i))) ”
  &&  (((diff + ((Znth i rights 0) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i diff (Znth i rights 0) 0 (n_pre + 1 ) (replace_Znth (((Znth i lefts 0) - 1 )) (((Znth ((Znth i lefts 0) - 1 ) diff_data 0) + 1 )) (diff_data)) )
  **  (IntArray.full right_pre q_pre rights )
  **  (IntArray.full left_pre q_pre lefts )
  **  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_8 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) diff_data )
|--
  “ (i < n_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (CoveragePrefixState queries n_pre i diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre))) ”
  &&  (((diff + (i * sizeof(INT64)))) # Int64  |-> (Znth i diff_data 0))
  **  (Int64Array.missing_i diff i 0 (n_pre + 1 ) diff_data )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
.

Definition solver_partial_solve_wit_9 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre)))) ,
  (Int64Array.full diff (n_pre + 1 ) diff_data )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (i < n_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (CoveragePrefixState queries n_pre i diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre))) ”
  &&  (((diff + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (i - 1 ) diff_data 0))
  **  (Int64Array.missing_i diff (i - 1 ) 0 (n_pre + 1 ) diff_data )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
.

Definition solver_partial_solve_wit_10 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (diff_data: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 ))))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (CoveragePrefixState queries n_pre i diff_data )) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre)))) ,
  (Int64Array.full diff (n_pre + 1 ) diff_data )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
|--
  “ (i < n_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_pre)) -> (((fst ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 lefts 0) - 1 )) /\ ((snd ((Znth k_3 queries __default__Prod_Z_Z))) = ((Znth k_3 rights 0) - 1 )))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (CoveragePrefixState queries n_pre i diff_data ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> (((-q_pre) <= (Znth k_4 diff_data 0)) /\ ((Znth k_4 diff_data 0) <= q_pre))) ”
  &&  (((diff + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i diff i 0 (n_pre + 1 ) diff_data )
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
.

Definition solver_partial_solve_wit_11_pure := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (frequencies: (@list Z)) (tail: (@list Z)) (diff: Z)  __default__Prod_Z_Z (PreH1 : (diff <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (q_pre = (Zlength (queries)))) (PreH4 : ((Zlength (lefts)) = q_pre)) (PreH5 : ((Zlength (rights)) = q_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 200000)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH12 : ((Zlength (frequencies)) = n_pre)) (PreH13 : ((Zlength (tail)) = 1)) (PreH14 : (CoverageProfile queries n_pre frequencies )) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 frequencies 0)) /\ ((Znth k_3 frequencies 0) <= q_pre)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff n_pre frequencies )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_11_aux := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (frequencies: (@list Z)) (tail: (@list Z)) (diff: Z)  __default__Prod_Z_Z (PreH1 : (diff <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (q_pre = (Zlength (queries)))) (PreH4 : ((Zlength (lefts)) = q_pre)) (PreH5 : ((Zlength (rights)) = q_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 200000)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH12 : ((Zlength (frequencies)) = n_pre)) (PreH13 : ((Zlength (tail)) = 1)) (PreH14 : (CoverageProfile queries n_pre frequencies )) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 frequencies 0)) /\ ((Znth k_3 frequencies 0) <= q_pre)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff n_pre frequencies )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 frequencies 0)) /\ ((Znth k_3 frequencies 0) <= q_pre))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff n_pre frequencies )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail )
.

Definition solver_partial_solve_wit_11 := solver_partial_solve_wit_11_pure -> solver_partial_solve_wit_11_aux.

Definition solver_partial_solve_wit_12_pure := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (values_sorted: (@list Z)) (frequencies: (@list Z)) (tail: (@list Z)) (diff: Z)  __default__Prod_Z_Z (PreH1 : (diff <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (q_pre = (Zlength (queries)))) (PreH4 : ((Zlength (lefts)) = q_pre)) (PreH5 : ((Zlength (rights)) = q_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 200000)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH12 : ((Zlength (values_sorted)) = n_pre)) (PreH13 : ((Zlength (frequencies)) = n_pre)) (PreH14 : ((Zlength (tail)) = 1)) (PreH15 : (Permutation values values_sorted )) (PreH16 : (increasing values_sorted )) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH18 : (CoverageProfile queries n_pre frequencies )) (PreH19 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies 0)) /\ ((Znth k_4 frequencies 0) <= q_pre)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Ptr  |-> left_pre)
  **  ((( &( "right" ) )) # Ptr  |-> right_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "diff" ) )) # Ptr  |-> diff)
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff n_pre frequencies )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail )
|--
  “ (n_pre = (Zlength (frequencies))) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_12_aux := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (values_sorted: (@list Z)) (frequencies: (@list Z)) (tail: (@list Z)) (diff: Z)  __default__Prod_Z_Z (PreH1 : (diff <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (q_pre = (Zlength (queries)))) (PreH4 : ((Zlength (lefts)) = q_pre)) (PreH5 : ((Zlength (rights)) = q_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 200000)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH12 : ((Zlength (values_sorted)) = n_pre)) (PreH13 : ((Zlength (frequencies)) = n_pre)) (PreH14 : ((Zlength (tail)) = 1)) (PreH15 : (Permutation values values_sorted )) (PreH16 : (increasing values_sorted )) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH18 : (CoverageProfile queries n_pre frequencies )) (PreH19 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies 0)) /\ ((Znth k_4 frequencies 0) <= q_pre)))) ,
  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff n_pre frequencies )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail )
|--
  “ (n_pre = (Zlength (frequencies))) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ ((Zlength (values_sorted)) = n_pre) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (Permutation values values_sorted ) ” 
  &&  “ (increasing values_sorted ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000))) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies 0)) /\ ((Znth k_4 frequencies 0) <= q_pre))) ”
  &&  (Int64Array.full diff n_pre frequencies )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full (diff + (n_pre * sizeof(INT64))) 1 tail )
.

Definition solver_partial_solve_wit_12 := solver_partial_solve_wit_12_pure -> solver_partial_solve_wit_12_aux.

Definition solver_partial_solve_wit_13 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
|--
  “ (i < n_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (values_sorted)) = n_pre) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (frequencies_sorted)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (Permutation values values_sorted ) ” 
  &&  “ (increasing values_sorted ) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ (Permutation frequencies frequencies_sorted ) ” 
  &&  “ (increasing frequencies_sorted ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre))) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= ((i * 200000 ) * q_pre )) ” 
  &&  “ (DotProductPrefix values_sorted frequencies_sorted i answer ) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values_sorted 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
.

Definition solver_partial_solve_wit_14 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
|--
  “ (i < n_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (values_sorted)) = n_pre) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (frequencies_sorted)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (Permutation values values_sorted ) ” 
  &&  “ (increasing values_sorted ) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ (Permutation frequencies frequencies_sorted ) ” 
  &&  “ (increasing frequencies_sorted ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre))) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= ((i * 200000 ) * q_pre )) ” 
  &&  “ (DotProductPrefix values_sorted frequencies_sorted i answer ) ”
  &&  (((diff + (i * sizeof(INT64)))) # Int64  |-> (Znth i (app (frequencies_sorted) (tail)) 0))
  **  (Int64Array.missing_i diff i 0 (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
.

Definition solver_partial_solve_wit_15 := 
forall (q_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (a_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries: (@list (Z * Z))) (values: (@list Z)) (answer: Z) (tail: (@list Z)) (frequencies_sorted: (@list Z)) (frequencies: (@list Z)) (values_sorted: (@list Z)) (i: Z) (diff: Z)  __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (diff <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (q_pre = (Zlength (queries)))) (PreH5 : ((Zlength (lefts)) = q_pre)) (PreH6 : ((Zlength (rights)) = q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (values_sorted)) = n_pre)) (PreH16 : ((Zlength (frequencies)) = n_pre)) (PreH17 : ((Zlength (frequencies_sorted)) = n_pre)) (PreH18 : ((Zlength (tail)) = 1)) (PreH19 : (Permutation values values_sorted )) (PreH20 : (increasing values_sorted )) (PreH21 : (CoverageProfile queries n_pre frequencies )) (PreH22 : (Permutation frequencies frequencies_sorted )) (PreH23 : (increasing frequencies_sorted )) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000)))) (PreH25 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre)))) (PreH26 : (0 <= answer)) (PreH27 : (answer <= ((i * 200000 ) * q_pre ))) (PreH28 : (DotProductPrefix values_sorted frequencies_sorted i answer )) ,
  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
  **  (Int64Array.full diff (n_pre + 1 ) (app (frequencies_sorted) (tail)) )
|--
  “ (i >= n_pre) ” 
  &&  “ (diff <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (q_pre = (Zlength (queries))) ” 
  &&  “ ((Zlength (lefts)) = q_pre) ” 
  &&  “ ((Zlength (rights)) = q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_pre)) -> (((0 <= (fst ((Znth k_2 queries __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 queries __default__Prod_Z_Z))) <= (snd ((Znth k_2 queries __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 queries __default__Prod_Z_Z))) < n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (values_sorted)) = n_pre) ” 
  &&  “ ((Zlength (frequencies)) = n_pre) ” 
  &&  “ ((Zlength (frequencies_sorted)) = n_pre) ” 
  &&  “ ((Zlength (tail)) = 1) ” 
  &&  “ (Permutation values values_sorted ) ” 
  &&  “ (increasing values_sorted ) ” 
  &&  “ (CoverageProfile queries n_pre frequencies ) ” 
  &&  “ (Permutation frequencies frequencies_sorted ) ” 
  &&  “ (increasing frequencies_sorted ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values_sorted 0)) /\ ((Znth k_3 values_sorted 0) <= 200000))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 frequencies_sorted 0)) /\ ((Znth k_4 frequencies_sorted 0) <= q_pre))) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= ((i * 200000 ) * q_pre )) ” 
  &&  “ (DotProductPrefix values_sorted frequencies_sorted i answer ) ”
  &&  (Int64Array.full diff ((Zlength (values)) + 1 ) (app (frequencies_sorted) (tail)) )
  **  (Int64Array.full a_pre n_pre values_sorted )
  **  (IntArray.full left_pre q_pre lefts )
  **  (IntArray.full right_pre q_pre rights )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.

End VC_Correct.
