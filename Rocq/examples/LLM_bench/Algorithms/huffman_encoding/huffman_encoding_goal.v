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
Require Import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_lib.
Local Open Scope sac.

(*----- Function huffman_cost -----*)

Definition huffman_cost_safety_wit_1 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (HuffmanInputBounded weights_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_full work_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition huffman_cost_safety_wit_2 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (weights_l = (app (copied) (remaining)))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) ,
  (IntArray.seg work_pre 0 (i + 1 ) (app (copied) ((cons ((Znth i weights_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg work_pre (i + 1 ) n_pre )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition huffman_cost_safety_wit_3 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (weights_l = (app (copied) (remaining)))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) ,
  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "active" ) )) # Int  |-> n_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg work_pre 0 i copied )
  **  (IntArray.undef_seg work_pre i n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition huffman_cost_safety_wit_4 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (1 <= active)) (PreH7 : (active <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= 56000)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH11 : (HuffmanProgress weights_l work_l active total )) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition huffman_cost_safety_wit_5 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total )) ,
  ((( &( "first" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition huffman_cost_safety_wit_6 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "first" ) )) # Int  |-> 0)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition huffman_cost_safety_wit_7 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : ((Znth i work_l 0) < (Znth first work_l 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l )) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : (0 <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l active total )) (PreH22 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full work_pre n_pre work_l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition huffman_cost_safety_wit_8 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : ((Znth i work_l 0) >= (Znth first work_l 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l )) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : (0 <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l active total )) (PreH22 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full work_pre n_pre work_l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition huffman_cost_safety_wit_9 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (2 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= first)) (PreH13 : (first < i)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= 56000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH18 : (HuffmanProgress weights_l work_l active total )) (PreH19 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full work_pre n_pre work_l )
  **  ((( &( "x" ) )) # Int  |-> (Znth first work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ ((active - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (active - 1 )) ”
.

Definition huffman_cost_safety_wit_10 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (work_l: (@list Z)) (active: Z) (first: Z) (x: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : (0 <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l active x total )) ,
  ((( &( "second" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition huffman_cost_safety_wit_11 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (work_l: (@list Z)) (active: Z) (first: Z) (x: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : (0 <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l active x total )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "second" ) )) # Int  |-> 0)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition huffman_cost_safety_wit_12 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : ((Znth i work_l 0) < (Znth second work_l 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH24 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full work_pre n_pre work_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition huffman_cost_safety_wit_13 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : ((Znth i work_l 0) >= (Znth second work_l 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH24 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full work_pre n_pre work_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition huffman_cost_safety_wit_14 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active < n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= first)) (PreH13 : (first < n_pre)) (PreH14 : (0 <= second)) (PreH15 : (second < i)) (PreH16 : (second < n_pre)) (PreH17 : (1 <= x)) (PreH18 : (x <= 8000)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH22 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH23 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full work_pre n_pre work_l )
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ ((active - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (active - 1 )) ”
.

Definition huffman_cost_safety_wit_15 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (work_l: (@list Z)) (active: Z) (first: Z) (second: Z) (x: Z) (y: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (0 <= active)) (PreH7 : (active <= (n_pre - 2 ))) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (0 <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y ) <= 8000)) (PreH17 : (0 <= total)) (PreH18 : (((total + x ) + y ) <= 56000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l active x y total )) ,
  ((( &( "merged" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition huffman_cost_safety_wit_16 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (work_l: (@list Z)) (active: Z) (first: Z) (second: Z) (x: Z) (y: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (0 <= active)) (PreH7 : (active <= (n_pre - 2 ))) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (0 <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y ) <= 8000)) (PreH17 : (0 <= total)) (PreH18 : (((total + x ) + y ) <= 56000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l active x y total )) ,
  ((( &( "merged" ) )) # Int  |-> (x + y ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ ((total + (x + y ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total + (x + y ) )) ”
.

Definition huffman_cost_safety_wit_17 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (work_l: (@list Z)) (active: Z) (first: Z) (second: Z) (x: Z) (y: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (0 <= active)) (PreH7 : (active <= (n_pre - 2 ))) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (0 <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y ) <= 8000)) (PreH17 : (0 <= total)) (PreH18 : (((total + x ) + y ) <= 56000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l active x y total )) ,
  (IntArray.full work_pre n_pre (replace_Znth (active) ((x + y )) (work_l)) )
  **  ((( &( "merged" ) )) # Int  |-> (x + y ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "work" ) )) # Ptr  |-> work_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "total" ) )) # Int  |-> (total + (x + y ) ))
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ ((active + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (active + 1 )) ”
.

Definition huffman_cost_entail_wit_1 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (HuffmanInputBounded weights_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_full work_pre n_pre )
|--
  EX (copied: (@list Z))  (remaining: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (weights_l = (app (copied) (remaining))) ” 
  &&  “ ((Zlength (copied)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg work_pre 0 0 copied )
  **  (IntArray.undef_seg work_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (HuffmanInputBounded weights_l )) ,
  TT && emp 
|--
  EX (remaining: (@list Z)) ,
  “ (weights_l = (app ((@nil Z)) (remaining))) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (weights_l))) ”
  &&  emp
).

Definition huffman_cost_entail_wit_2 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied_2: (@list Z)) (remaining_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (weights_l = (app (copied_2) (remaining_2)))) (PreH7 : ((Zlength (copied_2)) = i)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) ,
  (IntArray.seg work_pre 0 (i + 1 ) (app (copied_2) ((cons ((Znth i weights_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg work_pre (i + 1 ) n_pre )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (copied: (@list Z))  (remaining: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (weights_l = (app (copied) (remaining))) ” 
  &&  “ ((Zlength (copied)) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg work_pre 0 (i + 1 ) copied )
  **  (IntArray.undef_seg work_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (i: Z) (copied_2: (@list Z)) (remaining_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (weights_l = (app (copied_2) (remaining_2)))) (PreH7 : ((Zlength (copied_2)) = i)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) ,
  TT && emp 
|--
  EX (remaining: (@list Z)) ,
  “ ((app (copied_2) (remaining_2)) = (app ((app (copied_2) ((cons ((Znth (Zlength (copied_2)) (app (copied_2) (remaining_2)) 0)) ((@nil Z)))))) (remaining))) ” 
  &&  “ ((Zlength ((app (copied_2) ((cons ((Znth (Zlength (copied_2)) (app (copied_2) (remaining_2)) 0)) ((@nil Z))))))) = ((Zlength (copied_2)) + 1 )) ” 
  &&  “ (0 <= ((Zlength (copied_2)) + 1 )) ” 
  &&  “ (((Zlength (copied_2)) + 1 ) <= (Zlength ((app (copied_2) (remaining_2))))) ”
  &&  emp
).

Definition huffman_cost_entail_wit_3 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (weights_l = (app (copied) (remaining)))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg work_pre 0 i copied )
  **  (IntArray.undef_seg work_pre i n_pre )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l n_pre 0 ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
) \/
(
forall (work_pre: Z) (n_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (weights_l = (app (copied) (remaining)))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) ,
  (IntArray.seg work_pre 0 i copied )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l n_pre 0 ) ”
  &&  (IntArray.full work_pre n_pre work_l )
).

Definition huffman_cost_entail_wit_4 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l_2 active total )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l_2 )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (2 <= active) ” 
  &&  “ (active <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 1) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l 1 0 ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l_2 active total )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 1 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000))) ”
  &&  emp
).

Definition huffman_cost_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l_2 active total )) ,
  (HuffmanMinScan work_l_2 1 0 )
.

Definition huffman_cost_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l_2 active total )) ,
  forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))
.

Definition huffman_cost_entail_wit_5 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (2 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= first)) (PreH13 : (first < i)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= 56000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH18 : (HuffmanProgress weights_l work_l active total )) (PreH19 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i < active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (2 <= active) ” 
  &&  “ (active <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < i) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
.

Definition huffman_cost_entail_wit_6_1 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l )) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : (0 <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total )) (PreH22 : (HuffmanMinScan work_l_2 i first )) ,
  (IntArray.full work_pre n_pre work_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (2 <= active) ” 
  &&  “ (active <= n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= active) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l (i + 1 ) i ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l )) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : (0 <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total )) (PreH22 : (HuffmanMinScan work_l_2 i first )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1 ) i ) ”
  &&  emp
).

Definition huffman_cost_entail_wit_6_1_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l )) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : (0 <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total )) (PreH22 : (HuffmanMinScan work_l_2 i first )) ,
  (HuffmanMinScan work_l_2 (i + 1 ) i )
.

Definition huffman_cost_entail_wit_6_2 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l )) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : (0 <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total )) (PreH22 : (HuffmanMinScan work_l_2 i first )) ,
  (IntArray.full work_pre n_pre work_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (2 <= active) ” 
  &&  “ (active <= n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= active) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < (i + 1 )) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l (i + 1 ) first ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l )) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : (0 <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total )) (PreH22 : (HuffmanMinScan work_l_2 i first )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1 ) first ) ”
  &&  emp
).

Definition huffman_cost_entail_wit_6_2_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (HuffmanInputBounded weights_l )) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : (0 <= total)) (PreH19 : (total <= 56000)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH21 : (HuffmanProgress weights_l work_l_2 active total )) (PreH22 : (HuffmanMinScan work_l_2 i first )) ,
  (HuffmanMinScan work_l_2 (i + 1 ) first )
.

Definition huffman_cost_entail_wit_7 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (2 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= first)) (PreH13 : (first < i)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= 56000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH18 : (HuffmanProgress weights_l work_l active total )) (PreH19 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full work_pre n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ (0 <= (active - 1 )) ” 
  &&  “ ((active - 1 ) < n_pre) ” 
  &&  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (2 <= active) ” 
  &&  “ (active <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < i) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (IntArray.full work_pre n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_entail_wit_8 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full work_pre n_pre (replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (work_l_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l_2)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= (active - 1 )) ” 
  &&  “ ((active - 1 ) < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (1 <= (Znth first work_l 0)) ” 
  &&  “ ((Znth first work_l 0) <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (active - 1 ))) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000))) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l_2 (active - 1 ) (Znth first work_l 0) total ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l_2 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  TT && emp 
|--
  “ (HuffmanFirstHeld weights_l (replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)) (active - 1 ) (Znth first work_l 0) total ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (active - 1 ))) -> ((1 <= (Znth (k) ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l))) (0))) /\ ((Znth (k) ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l))) (0)) <= 8000))) ” 
  &&  “ ((Znth first work_l 0) <= 8000) ” 
  &&  “ (1 <= (Znth first work_l 0)) ” 
  &&  “ ((Zlength ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)))) = n_pre) ”
  &&  emp
).

Definition huffman_cost_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (HuffmanFirstHeld weights_l (replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)) (active - 1 ) (Znth first work_l 0) total )
.

Definition huffman_cost_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  forall (k: Z) , (((0 <= k) /\ (k < (active - 1 ))) -> ((1 <= (Znth (k) ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l))) (0))) /\ ((Znth (k) ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l))) (0)) <= 8000)))
.

Definition huffman_cost_entail_wit_8_split_goal_3 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  ((Znth first work_l 0) <= 8000)
.

Definition huffman_cost_entail_wit_8_split_goal_4 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (1 <= (Znth first work_l 0))
.

Definition huffman_cost_entail_wit_8_split_goal_5 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  ((Zlength ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)))) = n_pre)
.

Definition huffman_cost_entail_wit_9 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (work_l_2: (@list Z)) (active: Z) (first: Z) (x: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : (0 <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l_2 active x total )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l_2 )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= active) ” 
  &&  “ (active < n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= active) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 1) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l 1 0 ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (work_l_2: (@list Z)) (active: Z) (first: Z) (x: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : (0 <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l_2 active x total )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 1 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000))) ”
  &&  emp
).

Definition huffman_cost_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (work_l_2: (@list Z)) (active: Z) (first: Z) (x: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : (0 <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l_2 active x total )) ,
  (HuffmanMinScan work_l_2 1 0 )
.

Definition huffman_cost_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (weights_l: (@list Z)) (work_l_2: (@list Z)) (active: Z) (first: Z) (x: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (1 <= active)) (PreH7 : (active < n_pre)) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (1 <= x)) (PreH11 : (x <= 8000)) (PreH12 : (0 <= total)) (PreH13 : (total <= 56000)) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH15 : (HuffmanFirstHeld weights_l work_l_2 active x total )) ,
  forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))
.

Definition huffman_cost_entail_wit_10_1 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH24 : (HuffmanMinScan work_l_2 i second )) ,
  (IntArray.full work_pre n_pre work_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= active) ” 
  &&  “ (active < n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= active) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l (i + 1 ) i ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH24 : (HuffmanMinScan work_l_2 i second )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1 ) i ) ”
  &&  emp
).

Definition huffman_cost_entail_wit_10_1_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH24 : (HuffmanMinScan work_l_2 i second )) ,
  (HuffmanMinScan work_l_2 (i + 1 ) i )
.

Definition huffman_cost_entail_wit_10_2 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH24 : (HuffmanMinScan work_l_2 i second )) ,
  (IntArray.full work_pre n_pre work_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= active) ” 
  &&  “ (active < n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= active) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= second) ” 
  &&  “ (second < (i + 1 )) ” 
  &&  “ (second < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l (i + 1 ) second ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH24 : (HuffmanMinScan work_l_2 i second )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1 ) second ) ”
  &&  emp
).

Definition huffman_cost_entail_wit_10_2_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (HuffmanInputBounded weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000)))) (PreH23 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH24 : (HuffmanMinScan work_l_2 i second )) ,
  (HuffmanMinScan work_l_2 (i + 1 ) second )
.

Definition huffman_cost_entail_wit_11 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active < n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= first)) (PreH13 : (first < n_pre)) (PreH14 : (0 <= second)) (PreH15 : (second < i)) (PreH16 : (second < n_pre)) (PreH17 : (1 <= x)) (PreH18 : (x <= 8000)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH22 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH23 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full work_pre n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ (0 <= (active - 1 )) ” 
  &&  “ ((active - 1 ) < n_pre) ” 
  &&  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= active) ” 
  &&  “ (active < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= second) ” 
  &&  “ (second < i) ” 
  &&  “ (second < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (IntArray.full work_pre n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_entail_wit_12 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full work_pre n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (work_l_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l_2)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (0 <= (active - 1 )) ” 
  &&  “ ((active - 1 ) <= (n_pre - 2 )) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= second) ” 
  &&  “ (second < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (1 <= (Znth second work_l 0)) ” 
  &&  “ ((Znth second work_l 0) <= 8000) ” 
  &&  “ ((x + (Znth second work_l 0) ) <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (((total + x ) + (Znth second work_l 0) ) <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (active - 1 ))) -> ((1 <= (Znth (k) (work_l_2) (0))) /\ ((Znth (k) (work_l_2) (0)) <= 8000))) ” 
  &&  “ (HuffmanPairReady weights_l work_l_2 (active - 1 ) x (Znth second work_l 0) total ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l_2 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  TT && emp 
|--
  “ (HuffmanPairReady weights_l (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) (active - 1 ) x (Znth second work_l 0) total ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (active - 1 ))) -> ((1 <= (Znth (k) ((replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l))) (0))) /\ ((Znth (k) ((replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l))) (0)) <= 8000))) ” 
  &&  “ (((total + x ) + (Znth second work_l 0) ) <= 56000) ” 
  &&  “ ((x + (Znth second work_l 0) ) <= 8000) ” 
  &&  “ ((Znth second work_l 0) <= 8000) ” 
  &&  “ (1 <= (Znth second work_l 0)) ” 
  &&  “ ((Zlength ((replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)))) = n_pre) ”
  &&  emp
).

Definition huffman_cost_entail_wit_12_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (HuffmanPairReady weights_l (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) (active - 1 ) x (Znth second work_l 0) total )
.

Definition huffman_cost_entail_wit_12_split_goal_2 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  forall (k: Z) , (((0 <= k) /\ (k < (active - 1 ))) -> ((1 <= (Znth (k) ((replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l))) (0))) /\ ((Znth (k) ((replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l))) (0)) <= 8000)))
.

Definition huffman_cost_entail_wit_12_split_goal_3 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (((total + x ) + (Znth second work_l 0) ) <= 56000)
.

Definition huffman_cost_entail_wit_12_split_goal_4 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((x + (Znth second work_l 0) ) <= 8000)
.

Definition huffman_cost_entail_wit_12_split_goal_5 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((Znth second work_l 0) <= 8000)
.

Definition huffman_cost_entail_wit_12_split_goal_6 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (1 <= (Znth second work_l 0))
.

Definition huffman_cost_entail_wit_12_split_goal_7 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l) (0))) /\ ((Znth (k_2) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((Zlength ((replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)))) = n_pre)
.

Definition huffman_cost_entail_wit_13 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (work_l_2: (@list Z)) (active: Z) (first: Z) (second: Z) (x: Z) (y: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (0 <= active)) (PreH7 : (active <= (n_pre - 2 ))) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (0 <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y ) <= 8000)) (PreH17 : (0 <= total)) (PreH18 : (((total + x ) + y ) <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l_2 active x y total )) ,
  (IntArray.full work_pre n_pre (replace_Znth (active) ((x + y )) (work_l_2)) )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= (active + 1 )) ” 
  &&  “ ((active + 1 ) <= n_pre) ” 
  &&  “ (0 <= (total + (x + y ) )) ” 
  &&  “ ((total + (x + y ) ) <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (active + 1 ))) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l (active + 1 ) (total + (x + y ) ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (work_l_2: (@list Z)) (active: Z) (first: Z) (second: Z) (x: Z) (y: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (0 <= active)) (PreH7 : (active <= (n_pre - 2 ))) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (0 <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y ) <= 8000)) (PreH17 : (0 <= total)) (PreH18 : (((total + x ) + y ) <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l_2 active x y total )) ,
  TT && emp 
|--
  “ (HuffmanProgress weights_l (replace_Znth (active) ((x + y )) (work_l_2)) (active + 1 ) (total + (x + y ) ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (active + 1 ))) -> ((1 <= (Znth (k) ((replace_Znth (active) ((x + y )) (work_l_2))) (0))) /\ ((Znth (k) ((replace_Znth (active) ((x + y )) (work_l_2))) (0)) <= 8000))) ” 
  &&  “ ((Zlength ((replace_Znth (active) ((x + y )) (work_l_2)))) = n_pre) ”
  &&  emp
).

Definition huffman_cost_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (work_l_2: (@list Z)) (active: Z) (first: Z) (second: Z) (x: Z) (y: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (0 <= active)) (PreH7 : (active <= (n_pre - 2 ))) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (0 <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y ) <= 8000)) (PreH17 : (0 <= total)) (PreH18 : (((total + x ) + y ) <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l_2 active x y total )) ,
  (HuffmanProgress weights_l (replace_Znth (active) ((x + y )) (work_l_2)) (active + 1 ) (total + (x + y ) ) )
.

Definition huffman_cost_entail_wit_13_split_goal_2 := 
forall (n_pre: Z) (weights_l: (@list Z)) (work_l_2: (@list Z)) (active: Z) (first: Z) (second: Z) (x: Z) (y: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (0 <= active)) (PreH7 : (active <= (n_pre - 2 ))) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (0 <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y ) <= 8000)) (PreH17 : (0 <= total)) (PreH18 : (((total + x ) + y ) <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l_2 active x y total )) ,
  forall (k: Z) , (((0 <= k) /\ (k < (active + 1 ))) -> ((1 <= (Znth (k) ((replace_Znth (active) ((x + y )) (work_l_2))) (0))) /\ ((Znth (k) ((replace_Znth (active) ((x + y )) (work_l_2))) (0)) <= 8000)))
.

Definition huffman_cost_entail_wit_13_split_goal_3 := 
forall (n_pre: Z) (weights_l: (@list Z)) (work_l_2: (@list Z)) (active: Z) (first: Z) (second: Z) (x: Z) (y: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l_2)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (0 <= active)) (PreH7 : (active <= (n_pre - 2 ))) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (0 <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y ) <= 8000)) (PreH17 : (0 <= total)) (PreH18 : (((total + x ) + y ) <= 56000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < active)) -> ((1 <= (Znth (k_2) (work_l_2) (0))) /\ ((Znth (k_2) (work_l_2) (0)) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l_2 active x y total )) ,
  ((Zlength ((replace_Znth (active) ((x + y )) (work_l_2)))) = n_pre)
.

Definition huffman_cost_entail_wit_14 := 
(
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  EX (final_work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (final_work_l)) = n_pre) ” 
  &&  “ (active = 1) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ (HuffmanOptimalCost weights_l total ) ” 
  &&  “ (HuffmanScratchFinal weights_l final_work_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre final_work_l )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total )) ,
  TT && emp 
|--
  “ (HuffmanScratchFinal weights_l work_l ) ” 
  &&  “ (HuffmanOptimalCost weights_l total ) ”
  &&  emp
).

Definition huffman_cost_entail_wit_14_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total )) ,
  (HuffmanScratchFinal weights_l work_l )
.

Definition huffman_cost_entail_wit_14_split_goal_2 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH12 : (HuffmanProgress weights_l work_l active total )) ,
  (HuffmanOptimalCost weights_l total )
.

Definition huffman_cost_return_wit_1 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (final_work_l: (@list Z)) (active: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (final_work_l)) = n_pre)) (PreH5 : (active = 1)) (PreH6 : (0 <= total)) (PreH7 : (total <= 56000)) (PreH8 : (HuffmanOptimalCost weights_l total )) (PreH9 : (HuffmanScratchFinal weights_l final_work_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre final_work_l )
|--
  EX (work_l: (@list Z)) ,
  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanOptimalCost weights_l total ) ” 
  &&  “ (HuffmanScratchFinal weights_l work_l ) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
.

Definition huffman_cost_partial_solve_wit_1 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (weights_l = (app (copied) (remaining)))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg work_pre 0 i copied )
  **  (IntArray.undef_seg work_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (weights_l = (app (copied) (remaining))) ” 
  &&  “ ((Zlength (copied)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((weights_pre + (i * sizeof(INT)))) # Int  |-> (Znth i weights_l 0))
  **  (IntArray.missing_i weights_pre i 0 n_pre weights_l )
  **  (IntArray.seg work_pre 0 i copied )
  **  (IntArray.undef_seg work_pre i n_pre )
.

Definition huffman_cost_partial_solve_wit_2 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (weights_l = (app (copied) (remaining)))) (PreH7 : ((Zlength (copied)) = i)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg work_pre 0 i copied )
  **  (IntArray.undef_seg work_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (weights_l = (app (copied) (remaining))) ” 
  &&  “ ((Zlength (copied)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((work_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg work_pre (i + 1 ) n_pre )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg work_pre 0 i copied )
.

Definition huffman_cost_partial_solve_wit_3 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (i < active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i < active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (2 <= active) ” 
  &&  “ (active <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < i) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (((work_pre + (i * sizeof(INT)))) # Int  |-> (Znth i work_l 0))
  **  (IntArray.missing_i work_pre i 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_4 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (i < active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full work_pre n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i < active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (2 <= active) ” 
  &&  “ (active <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < i) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (((work_pre + (first * sizeof(INT)))) # Int  |-> (Znth first work_l 0))
  **  (IntArray.missing_i work_pre first 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_5 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (2 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= first)) (PreH13 : (first < i)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= 56000)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH18 : (HuffmanProgress weights_l work_l active total )) (PreH19 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (2 <= active) ” 
  &&  “ (active <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < i) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (((work_pre + (first * sizeof(INT)))) # Int  |-> (Znth first work_l 0))
  **  (IntArray.missing_i work_pre first 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_6 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full work_pre n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ (0 <= (active - 1 )) ” 
  &&  “ ((active - 1 ) < n_pre) ” 
  &&  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (2 <= active) ” 
  &&  “ (active <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < i) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (((work_pre + ((active - 1 ) * sizeof(INT)))) # Int  |-> (Znth (active - 1 ) work_l 0))
  **  (IntArray.missing_i work_pre (active - 1 ) 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_7 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (2 <= active)) (PreH10 : (active <= n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < i)) (PreH16 : (first < n_pre)) (PreH17 : (0 <= total)) (PreH18 : (total <= 56000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full work_pre n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ (0 <= (active - 1 )) ” 
  &&  “ ((active - 1 ) < n_pre) ” 
  &&  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (2 <= active) ” 
  &&  “ (active <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < i) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (((work_pre + (first * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i work_pre first 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_8 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active < n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= first)) (PreH13 : (first < n_pre)) (PreH14 : (0 <= second)) (PreH15 : (second < i)) (PreH16 : (second < n_pre)) (PreH17 : (1 <= x)) (PreH18 : (x <= 8000)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH22 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH23 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (i < active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= active) ” 
  &&  “ (active < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= second) ” 
  &&  “ (second < i) ” 
  &&  “ (second < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((work_pre + (i * sizeof(INT)))) # Int  |-> (Znth i work_l 0))
  **  (IntArray.missing_i work_pre i 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_9 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active < n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= first)) (PreH13 : (first < n_pre)) (PreH14 : (0 <= second)) (PreH15 : (second < i)) (PreH16 : (second < n_pre)) (PreH17 : (1 <= x)) (PreH18 : (x <= 8000)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH22 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH23 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full work_pre n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ (i < active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= active) ” 
  &&  “ (active < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= second) ” 
  &&  “ (second < i) ” 
  &&  “ (second < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((work_pre + (second * sizeof(INT)))) # Int  |-> (Znth second work_l 0))
  **  (IntArray.missing_i work_pre second 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_10 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (HuffmanInputBounded weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active < n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= active)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= first)) (PreH13 : (first < n_pre)) (PreH14 : (0 <= second)) (PreH15 : (second < i)) (PreH16 : (second < n_pre)) (PreH17 : (1 <= x)) (PreH18 : (x <= 8000)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH22 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH23 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= active) ” 
  &&  “ (active < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= second) ” 
  &&  “ (second < i) ” 
  &&  “ (second < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((work_pre + (second * sizeof(INT)))) # Int  |-> (Znth second work_l 0))
  **  (IntArray.missing_i work_pre second 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_11 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full work_pre n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ (0 <= (active - 1 )) ” 
  &&  “ ((active - 1 ) < n_pre) ” 
  &&  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= active) ” 
  &&  “ (active < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= second) ” 
  &&  “ (second < i) ” 
  &&  “ (second < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((work_pre + ((active - 1 ) * sizeof(INT)))) # Int  |-> (Znth (active - 1 ) work_l 0))
  **  (IntArray.missing_i work_pre (active - 1 ) 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_12 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= (active - 1 ))) (PreH2 : ((active - 1 ) < n_pre)) (PreH3 : (i >= active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (HuffmanInputBounded weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full work_pre n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ (0 <= (active - 1 )) ” 
  &&  “ ((active - 1 ) < n_pre) ” 
  &&  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (1 <= active) ” 
  &&  “ (active < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= active) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= second) ” 
  &&  “ (second < i) ” 
  &&  “ (second < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((work_pre + (second * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i work_pre second 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_13 := 
forall (work_pre: Z) (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (work_l: (@list Z)) (active: Z) (first: Z) (second: Z) (x: Z) (y: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (HuffmanInputBounded weights_l )) (PreH6 : (0 <= active)) (PreH7 : (active <= (n_pre - 2 ))) (PreH8 : (0 <= first)) (PreH9 : (first < n_pre)) (PreH10 : (0 <= second)) (PreH11 : (second < n_pre)) (PreH12 : (1 <= x)) (PreH13 : (x <= 8000)) (PreH14 : (1 <= y)) (PreH15 : (y <= 8000)) (PreH16 : ((x + y ) <= 8000)) (PreH17 : (0 <= total)) (PreH18 : (((total + x ) + y ) <= 56000)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000)))) (PreH20 : (HuffmanPairReady weights_l work_l active x y total )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full work_pre n_pre work_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (HuffmanInputBounded weights_l ) ” 
  &&  “ (0 <= active) ” 
  &&  “ (active <= (n_pre - 2 )) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= second) ” 
  &&  “ (second < n_pre) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= 8000) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= 8000) ” 
  &&  “ ((x + y ) <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (((total + x ) + y ) <= 56000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < active)) -> ((1 <= (Znth (k) (work_l) (0))) /\ ((Znth (k) (work_l) (0)) <= 8000))) ” 
  &&  “ (HuffmanPairReady weights_l work_l active x y total ) ”
  &&  (((work_pre + (active * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i work_pre active 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Module Type VC_Correct.


Axiom proof_of_huffman_cost_safety_wit_1 : huffman_cost_safety_wit_1.
Axiom proof_of_huffman_cost_safety_wit_2 : huffman_cost_safety_wit_2.
Axiom proof_of_huffman_cost_safety_wit_3 : huffman_cost_safety_wit_3.
Axiom proof_of_huffman_cost_safety_wit_4 : huffman_cost_safety_wit_4.
Axiom proof_of_huffman_cost_safety_wit_5 : huffman_cost_safety_wit_5.
Axiom proof_of_huffman_cost_safety_wit_6 : huffman_cost_safety_wit_6.
Axiom proof_of_huffman_cost_safety_wit_7 : huffman_cost_safety_wit_7.
Axiom proof_of_huffman_cost_safety_wit_8 : huffman_cost_safety_wit_8.
Axiom proof_of_huffman_cost_safety_wit_9 : huffman_cost_safety_wit_9.
Axiom proof_of_huffman_cost_safety_wit_10 : huffman_cost_safety_wit_10.
Axiom proof_of_huffman_cost_safety_wit_11 : huffman_cost_safety_wit_11.
Axiom proof_of_huffman_cost_safety_wit_12 : huffman_cost_safety_wit_12.
Axiom proof_of_huffman_cost_safety_wit_13 : huffman_cost_safety_wit_13.
Axiom proof_of_huffman_cost_safety_wit_14 : huffman_cost_safety_wit_14.
Axiom proof_of_huffman_cost_safety_wit_15 : huffman_cost_safety_wit_15.
Axiom proof_of_huffman_cost_safety_wit_16 : huffman_cost_safety_wit_16.
Axiom proof_of_huffman_cost_safety_wit_17 : huffman_cost_safety_wit_17.
Axiom proof_of_huffman_cost_entail_wit_1 : huffman_cost_entail_wit_1.
Axiom proof_of_huffman_cost_entail_wit_2 : huffman_cost_entail_wit_2.
Axiom proof_of_huffman_cost_entail_wit_3 : huffman_cost_entail_wit_3.
Axiom proof_of_huffman_cost_entail_wit_4 : huffman_cost_entail_wit_4.
Axiom proof_of_huffman_cost_entail_wit_5 : huffman_cost_entail_wit_5.
Axiom proof_of_huffman_cost_entail_wit_6_1 : huffman_cost_entail_wit_6_1.
Axiom proof_of_huffman_cost_entail_wit_6_2 : huffman_cost_entail_wit_6_2.
Axiom proof_of_huffman_cost_entail_wit_7 : huffman_cost_entail_wit_7.
Axiom proof_of_huffman_cost_entail_wit_8 : huffman_cost_entail_wit_8.
Axiom proof_of_huffman_cost_entail_wit_9 : huffman_cost_entail_wit_9.
Axiom proof_of_huffman_cost_entail_wit_10_1 : huffman_cost_entail_wit_10_1.
Axiom proof_of_huffman_cost_entail_wit_10_2 : huffman_cost_entail_wit_10_2.
Axiom proof_of_huffman_cost_entail_wit_11 : huffman_cost_entail_wit_11.
Axiom proof_of_huffman_cost_entail_wit_12 : huffman_cost_entail_wit_12.
Axiom proof_of_huffman_cost_entail_wit_13 : huffman_cost_entail_wit_13.
Axiom proof_of_huffman_cost_entail_wit_14 : huffman_cost_entail_wit_14.
Axiom proof_of_huffman_cost_return_wit_1 : huffman_cost_return_wit_1.
Axiom proof_of_huffman_cost_partial_solve_wit_1 : huffman_cost_partial_solve_wit_1.
Axiom proof_of_huffman_cost_partial_solve_wit_2 : huffman_cost_partial_solve_wit_2.
Axiom proof_of_huffman_cost_partial_solve_wit_3 : huffman_cost_partial_solve_wit_3.
Axiom proof_of_huffman_cost_partial_solve_wit_4 : huffman_cost_partial_solve_wit_4.
Axiom proof_of_huffman_cost_partial_solve_wit_5 : huffman_cost_partial_solve_wit_5.
Axiom proof_of_huffman_cost_partial_solve_wit_6 : huffman_cost_partial_solve_wit_6.
Axiom proof_of_huffman_cost_partial_solve_wit_7 : huffman_cost_partial_solve_wit_7.
Axiom proof_of_huffman_cost_partial_solve_wit_8 : huffman_cost_partial_solve_wit_8.
Axiom proof_of_huffman_cost_partial_solve_wit_9 : huffman_cost_partial_solve_wit_9.
Axiom proof_of_huffman_cost_partial_solve_wit_10 : huffman_cost_partial_solve_wit_10.
Axiom proof_of_huffman_cost_partial_solve_wit_11 : huffman_cost_partial_solve_wit_11.
Axiom proof_of_huffman_cost_partial_solve_wit_12 : huffman_cost_partial_solve_wit_12.
Axiom proof_of_huffman_cost_partial_solve_wit_13 : huffman_cost_partial_solve_wit_13.

End VC_Correct.
