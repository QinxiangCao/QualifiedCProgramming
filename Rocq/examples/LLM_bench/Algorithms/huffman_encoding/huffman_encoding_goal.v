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
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (Forall (Z.le (1)) weights_l )) (PreH5 : (Forall (Z.ge (1000)) weights_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "work" ) ) 8 )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition huffman_cost_safety_wit_2 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) weights_l )) (PreH6 : (Forall (Z.ge (1000)) weights_l )) (PreH7 : (weights_l = (app (copied) (remaining)))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) ,
  (IntArray.seg ( &( "work" ) ) 0 (i + 1 ) (app (copied) ((cons ((Znth i weights_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "work" ) ) (i + 1 ) n_pre )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition huffman_cost_safety_wit_3 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) weights_l )) (PreH6 : (Forall (Z.ge (1000)) weights_l )) (PreH7 : (weights_l = (app (copied) (remaining)))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) ,
  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "active" ) )) # Int  |-> n_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg ( &( "work" ) ) 0 i copied )
  **  (IntArray.undef_seg ( &( "work" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition huffman_cost_safety_wit_4 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) weights_l )) (PreH6 : (Forall (Z.ge (1000)) weights_l )) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 56000)) (PreH11 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH12 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH13 : (HuffmanProgress weights_l work_l active total )) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition huffman_cost_safety_wit_5 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH13 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH14 : (HuffmanProgress weights_l work_l active total )) ,
  ((( &( "first" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition huffman_cost_safety_wit_6 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH13 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH14 : (HuffmanProgress weights_l work_l active total )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "first" ) )) # Int  |-> 0)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition huffman_cost_safety_wit_7 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : ((Znth i work_l 0) < (Znth first work_l 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l)) = n_pre)) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.ge (1000)) weights_l )) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH22 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH23 : (HuffmanProgress weights_l work_l active total )) (PreH24 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition huffman_cost_safety_wit_8 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : ((Znth i work_l 0) >= (Znth first work_l 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l)) = n_pre)) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.ge (1000)) weights_l )) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH22 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH23 : (HuffmanProgress weights_l work_l active total )) (PreH24 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition huffman_cost_safety_wit_9 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  ((( &( "x" ) )) # Int  |-> (Znth first work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((active - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (active - 1 )) ”
.

Definition huffman_cost_safety_wit_10 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  ((( &( "second" ) )) # Int  |->_)
  **  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  ((( &( "x" ) )) # Int  |-> (Znth first work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition huffman_cost_safety_wit_11 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "second" ) )) # Int  |-> 0)
  **  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  ((( &( "x" ) )) # Int  |-> (Znth first work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition huffman_cost_safety_wit_12 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : ((Znth i work_l 0) < (Znth second work_l 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge (1000)) weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH24 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH25 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH26 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition huffman_cost_safety_wit_13 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : ((Znth i work_l 0) >= (Znth second work_l 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge (1000)) weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH24 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH25 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH26 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition huffman_cost_safety_wit_14 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> active)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((active - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (active - 1 )) ”
.

Definition huffman_cost_safety_wit_15 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((( &( "merged" ) )) # Int  |->_)
  **  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((x + (Znth second work_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + (Znth second work_l 0) )) ”
) \/
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((( &( "merged" ) )) # Int  |->_)
  **  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((x + (Znth second work_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + (Znth second work_l 0) )) ”
).

Definition huffman_cost_safety_wit_15_split_goal_1 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((( &( "merged" ) )) # Int  |->_)
  **  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((x + (Znth second work_l 0) ) <= INT_MAX) ”
.

Definition huffman_cost_safety_wit_15_split_goal_2 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((( &( "merged" ) )) # Int  |->_)
  **  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((INT_MIN) <= (x + (Znth second work_l 0) )) ”
.

Definition huffman_cost_safety_wit_16 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((( &( "merged" ) )) # Int  |-> (x + (Znth second work_l 0) ))
  **  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((total + (x + (Znth second work_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total + (x + (Znth second work_l 0) ) )) ”
) \/
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((( &( "merged" ) )) # Int  |-> (x + (Znth second work_l 0) ))
  **  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((total + (x + (Znth second work_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total + (x + (Znth second work_l 0) ) )) ”
).

Definition huffman_cost_safety_wit_16_split_goal_1 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((( &( "merged" ) )) # Int  |-> (x + (Znth second work_l 0) ))
  **  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((total + (x + (Znth second work_l 0) ) ) <= INT_MAX) ”
.

Definition huffman_cost_safety_wit_16_split_goal_2 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  ((( &( "merged" ) )) # Int  |-> (x + (Znth second work_l 0) ))
  **  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ ((INT_MIN) <= (total + (x + (Znth second work_l 0) ) )) ”
.

Definition huffman_cost_safety_wit_17 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth ((active - 1 )) ((x + (Znth second work_l 0) )) ((replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)))) )
  **  ((( &( "merged" ) )) # Int  |-> (x + (Znth second work_l 0) ))
  **  ((( &( "y" ) )) # Int  |-> (Znth second work_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "active" ) )) # Int  |-> (active - 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "second" ) )) # Int  |-> second)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> (total + (x + (Znth second work_l 0) ) ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (((active - 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((active - 1 ) + 1 )) ”
.

Definition huffman_cost_entail_wit_1 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (Forall (Z.le (1)) weights_l )) (PreH5 : (Forall (Z.ge (1000)) weights_l )) ,
  (IntArray.undef_full ( &( "work" ) ) 8 )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (copied: (@list Z))  (remaining: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
  &&  “ (weights_l = (app (copied) (remaining))) ” 
  &&  “ ((Zlength (copied)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg ( &( "work" ) ) 0 0 copied )
  **  (IntArray.undef_seg ( &( "work" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (Forall (Z.le (1)) weights_l )) (PreH5 : (Forall (Z.ge (1000)) weights_l )) ,
  (IntArray.undef_full ( &( "work" ) ) 8 )
|--
  EX (remaining: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
  &&  “ (weights_l = (app ((@nil Z)) (remaining))) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (IntArray.undef_seg ( &( "work" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
).

Definition huffman_cost_entail_wit_2 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied_2: (@list Z)) (remaining_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) weights_l )) (PreH6 : (Forall (Z.ge (1000)) weights_l )) (PreH7 : (weights_l = (app (copied_2) (remaining_2)))) (PreH8 : ((Zlength (copied_2)) = i)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) ,
  (IntArray.seg ( &( "work" ) ) 0 (i + 1 ) (app (copied_2) ((cons ((Znth i weights_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "work" ) ) (i + 1 ) n_pre )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  EX (copied: (@list Z))  (remaining: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
  &&  “ (weights_l = (app (copied) (remaining))) ” 
  &&  “ ((Zlength (copied)) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg ( &( "work" ) ) 0 (i + 1 ) copied )
  **  (IntArray.undef_seg ( &( "work" ) ) (i + 1 ) n_pre )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (i: Z) (copied_2: (@list Z)) (remaining_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) weights_l )) (PreH6 : (Forall (Z.ge (1000)) weights_l )) (PreH7 : (weights_l = (app (copied_2) (remaining_2)))) (PreH8 : ((Zlength (copied_2)) = i)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) ,
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
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) weights_l )) (PreH6 : (Forall (Z.ge (1000)) weights_l )) (PreH7 : (weights_l = (app (copied) (remaining)))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg ( &( "work" ) ) 0 i copied )
  **  (IntArray.undef_seg ( &( "work" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 56000) ” 
  &&  “ (Forall (Z.le (1)) (sublist (0) (n_pre) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (n_pre) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l n_pre 0 ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) weights_l )) (PreH6 : (Forall (Z.ge (1000)) weights_l )) (PreH7 : (weights_l = (app (copied) (remaining)))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) ,
  (IntArray.seg ( &( "work" ) ) 0 i copied )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 56000) ” 
  &&  “ (Forall (Z.le (1)) (sublist (0) (n_pre) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (n_pre) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l n_pre 0 ) ”
  &&  (IntArray.full ( &( "work" ) ) n_pre work_l )
).

Definition huffman_cost_entail_wit_4 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH13 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH14 : (HuffmanProgress weights_l work_l_2 active total )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l_2 )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l 1 0 ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH13 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH14 : (HuffmanProgress weights_l work_l_2 active total )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 1 0 ) ”
  &&  emp
).

Definition huffman_cost_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH13 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH14 : (HuffmanProgress weights_l work_l_2 active total )) ,
  (HuffmanMinScan work_l_2 1 0 )
.

Definition huffman_cost_entail_wit_5 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i < active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_entail_wit_6_1 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.ge (1000)) weights_l )) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH22 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (HuffmanProgress weights_l work_l_2 active total )) (PreH24 : (HuffmanMinScan work_l_2 i first )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l (i + 1 ) i ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.ge (1000)) weights_l )) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH22 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (HuffmanProgress weights_l work_l_2 active total )) (PreH24 : (HuffmanMinScan work_l_2 i first )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1 ) i ) ”
  &&  emp
).

Definition huffman_cost_entail_wit_6_1_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.ge (1000)) weights_l )) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH22 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (HuffmanProgress weights_l work_l_2 active total )) (PreH24 : (HuffmanMinScan work_l_2 i first )) ,
  (HuffmanMinScan work_l_2 (i + 1 ) i )
.

Definition huffman_cost_entail_wit_6_2 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.ge (1000)) weights_l )) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH22 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (HuffmanProgress weights_l work_l_2 active total )) (PreH24 : (HuffmanMinScan work_l_2 i first )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l (i + 1 ) first ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.ge (1000)) weights_l )) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH22 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (HuffmanProgress weights_l work_l_2 active total )) (PreH24 : (HuffmanMinScan work_l_2 i first )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1 ) first ) ”
  &&  emp
).

Definition huffman_cost_entail_wit_6_2_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth first work_l_2 0))) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.ge (1000)) weights_l )) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : (0 <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH22 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (HuffmanProgress weights_l work_l_2 active total )) (PreH24 : (HuffmanMinScan work_l_2 i first )) ,
  (HuffmanMinScan work_l_2 (i + 1 ) first )
.

Definition huffman_cost_entail_wit_7 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  EX (work_l_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l_2)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
  &&  “ (1 <= (active - 1 )) ” 
  &&  “ ((active - 1 ) < n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (active - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 1) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (1 <= (Znth first work_l 0)) ” 
  &&  “ ((Znth first work_l 0) <= 8000) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 56000) ” 
  &&  “ (Forall (Z.le (1)) (sublist (0) ((active - 1 )) (work_l_2)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) ((active - 1 )) (work_l_2)) ) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l_2 (active - 1 ) (Znth first work_l 0) total ) ” 
  &&  “ (HuffmanMinScan work_l_2 1 0 ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l_2 )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  TT && emp 
|--
  “ (HuffmanMinScan (replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)) 1 0 ) ” 
  &&  “ (HuffmanFirstHeld weights_l (replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)) (active - 1 ) (Znth first work_l 0) total ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) ((active - 1 )) ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)))) ) ” 
  &&  “ (Forall (Z.le (1)) (sublist (0) ((active - 1 )) ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)))) ) ” 
  &&  “ ((Znth first work_l 0) <= 8000) ” 
  &&  “ (1 <= (Znth first work_l 0)) ” 
  &&  “ ((Zlength ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)))) = n_pre) ”
  &&  emp
).

Definition huffman_cost_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (HuffmanMinScan (replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)) 1 0 )
.

Definition huffman_cost_entail_wit_7_split_goal_2 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (HuffmanFirstHeld weights_l (replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)) (active - 1 ) (Znth first work_l 0) total )
.

Definition huffman_cost_entail_wit_7_split_goal_3 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (Forall (Z.ge (8000)) (sublist (0) ((active - 1 )) ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)))) )
.

Definition huffman_cost_entail_wit_7_split_goal_4 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (Forall (Z.le (1)) (sublist (0) ((active - 1 )) ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)))) )
.

Definition huffman_cost_entail_wit_7_split_goal_5 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  ((Znth first work_l 0) <= 8000)
.

Definition huffman_cost_entail_wit_7_split_goal_6 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (1 <= (Znth first work_l 0))
.

Definition huffman_cost_entail_wit_7_split_goal_7 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  ((Zlength ((replace_Znth (first) ((Znth (active - 1 ) work_l 0)) (work_l)))) = n_pre)
.

Definition huffman_cost_entail_wit_8_1 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge (1000)) weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH26 : (HuffmanMinScan work_l_2 i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l (i + 1 ) i ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge (1000)) weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH26 : (HuffmanMinScan work_l_2 i second )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1 ) i ) ”
  &&  emp
).

Definition huffman_cost_entail_wit_8_1_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) < (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge (1000)) weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH26 : (HuffmanMinScan work_l_2 i second )) ,
  (HuffmanMinScan work_l_2 (i + 1 ) i )
.

Definition huffman_cost_entail_wit_8_2 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge (1000)) weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH26 : (HuffmanMinScan work_l_2 i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l (i + 1 ) second ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge (1000)) weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH26 : (HuffmanMinScan work_l_2 i second )) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1 ) second ) ”
  &&  emp
).

Definition huffman_cost_entail_wit_8_2_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : ((Znth i work_l_2 0) >= (Znth second work_l_2 0))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge (1000)) weights_l )) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= first)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : (0 <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH26 : (HuffmanMinScan work_l_2 i second )) ,
  (HuffmanMinScan work_l_2 (i + 1 ) second )
.

Definition huffman_cost_entail_wit_9 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH25 : (HuffmanMinScan work_l_2 i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth ((active - 1 )) ((x + (Znth second work_l_2 0) )) ((replace_Znth (second) ((Znth (active - 1 ) work_l_2 0)) (work_l_2)))) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  EX (work_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
  &&  “ (1 <= ((active - 1 ) + 1 )) ” 
  &&  “ (((active - 1 ) + 1 ) <= n_pre) ” 
  &&  “ (0 <= (total + (x + (Znth second work_l_2 0) ) )) ” 
  &&  “ ((total + (x + (Znth second work_l_2 0) ) ) <= 56000) ” 
  &&  “ (Forall (Z.le (1)) (sublist (0) (((active - 1 ) + 1 )) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (((active - 1 ) + 1 )) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l ((active - 1 ) + 1 ) (total + (x + (Znth second work_l_2 0) ) ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH25 : (HuffmanMinScan work_l_2 i second )) ,
  TT && emp 
|--
  “ (HuffmanProgress weights_l (replace_Znth ((active - 1 )) ((x + (Znth second work_l_2 0) )) ((replace_Znth (second) ((Znth (active - 1 ) work_l_2 0)) (work_l_2)))) ((active - 1 ) + 1 ) (total + (x + (Znth second work_l_2 0) ) ) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (((active - 1 ) + 1 )) ((replace_Znth ((active - 1 )) ((x + (Znth second work_l_2 0) )) ((replace_Znth (second) ((Znth (active - 1 ) work_l_2 0)) (work_l_2)))))) ) ” 
  &&  “ (Forall (Z.le (1)) (sublist (0) (((active - 1 ) + 1 )) ((replace_Znth ((active - 1 )) ((x + (Znth second work_l_2 0) )) ((replace_Znth (second) ((Znth (active - 1 ) work_l_2 0)) (work_l_2)))))) ) ” 
  &&  “ ((total + (x + (Znth second work_l_2 0) ) ) <= 56000) ” 
  &&  “ (0 <= (total + (x + (Znth second work_l_2 0) ) )) ” 
  &&  “ ((Zlength ((replace_Znth ((active - 1 )) ((x + (Znth second work_l_2 0) )) ((replace_Znth (second) ((Znth (active - 1 ) work_l_2 0)) (work_l_2)))))) = n_pre) ”
  &&  emp
).

Definition huffman_cost_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH25 : (HuffmanMinScan work_l_2 i second )) ,
  (HuffmanProgress weights_l (replace_Znth ((active - 1 )) ((x + (Znth second work_l_2 0) )) ((replace_Znth (second) ((Znth (active - 1 ) work_l_2 0)) (work_l_2)))) ((active - 1 ) + 1 ) (total + (x + (Znth second work_l_2 0) ) ) )
.

Definition huffman_cost_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH25 : (HuffmanMinScan work_l_2 i second )) ,
  (Forall (Z.ge (8000)) (sublist (0) (((active - 1 ) + 1 )) ((replace_Znth ((active - 1 )) ((x + (Znth second work_l_2 0) )) ((replace_Znth (second) ((Znth (active - 1 ) work_l_2 0)) (work_l_2)))))) )
.

Definition huffman_cost_entail_wit_9_split_goal_3 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH25 : (HuffmanMinScan work_l_2 i second )) ,
  (Forall (Z.le (1)) (sublist (0) (((active - 1 ) + 1 )) ((replace_Znth ((active - 1 )) ((x + (Znth second work_l_2 0) )) ((replace_Znth (second) ((Znth (active - 1 ) work_l_2 0)) (work_l_2)))))) )
.

Definition huffman_cost_entail_wit_9_split_goal_4 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH25 : (HuffmanMinScan work_l_2 i second )) ,
  ((total + (x + (Znth second work_l_2 0) ) ) <= 56000)
.

Definition huffman_cost_entail_wit_9_split_goal_5 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH25 : (HuffmanMinScan work_l_2 i second )) ,
  (0 <= (total + (x + (Znth second work_l_2 0) ) ))
.

Definition huffman_cost_entail_wit_9_split_goal_6 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l_2: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l_2)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l_2)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total )) (PreH25 : (HuffmanMinScan work_l_2 i second )) ,
  ((Zlength ((replace_Znth ((active - 1 )) ((x + (Znth second work_l_2 0) )) ((replace_Znth (second) ((Znth (active - 1 ) work_l_2 0)) (work_l_2)))))) = n_pre)
.

Definition huffman_cost_entail_wit_10 := 
(
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH13 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH14 : (HuffmanProgress weights_l work_l active total )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (active = 1) ” 
  &&  “ (HuffmanOptimalCost weights_l total ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_full ( &( "work" ) ) 8 )
) \/
(
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH13 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH14 : (HuffmanProgress weights_l work_l active total )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (HuffmanOptimalCost weights_l total ) ”
  &&  (IntArray.undef_full ( &( "work" ) ) 8 )
).

Definition huffman_cost_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH13 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH14 : (HuffmanProgress weights_l work_l active total )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (HuffmanOptimalCost weights_l total ) ”
.

Definition huffman_cost_entail_wit_10_split_goal_spatial := 
forall (n_pre: Z) (weights_l: (@list Z)) (total: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (0 <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH13 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH14 : (HuffmanProgress weights_l work_l active total )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  (IntArray.undef_full ( &( "work" ) ) 8 )
.

Definition huffman_cost_return_wit_1 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (active: Z) (total: Z) (PreH1 : (active = 1)) (PreH2 : (HuffmanOptimalCost weights_l total )) ,
  (IntArray.full weights_pre n_pre weights_l )
|--
  “ (HuffmanOptimalCost weights_l total ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
.

Definition huffman_cost_partial_solve_wit_1 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) weights_l )) (PreH6 : (Forall (Z.ge (1000)) weights_l )) (PreH7 : (weights_l = (app (copied) (remaining)))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg ( &( "work" ) ) 0 i copied )
  **  (IntArray.undef_seg ( &( "work" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
  &&  “ (weights_l = (app (copied) (remaining))) ” 
  &&  “ ((Zlength (copied)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((weights_pre + (i * sizeof(INT)))) # Int  |-> (Znth i weights_l 0))
  **  (IntArray.missing_i weights_pre i 0 n_pre weights_l )
  **  (IntArray.seg ( &( "work" ) ) 0 i copied )
  **  (IntArray.undef_seg ( &( "work" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_2 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (i: Z) (copied: (@list Z)) (remaining: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) weights_l )) (PreH6 : (Forall (Z.ge (1000)) weights_l )) (PreH7 : (weights_l = (app (copied) (remaining)))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg ( &( "work" ) ) 0 i copied )
  **  (IntArray.undef_seg ( &( "work" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
  &&  “ (weights_l = (app (copied) (remaining))) ” 
  &&  “ ((Zlength (copied)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((( &( "work" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "work" ) ) (i + 1 ) n_pre )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg ( &( "work" ) ) 0 i copied )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_3 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (i < active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (Forall (Z.le (1)) weights_l )) (PreH9 : (Forall (Z.ge (1000)) weights_l )) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : (0 <= total)) (PreH19 : (total <= 56000)) (PreH20 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH21 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH22 : (HuffmanProgress weights_l work_l active total )) (PreH23 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i < active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (((( &( "work" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i work_l 0))
  **  (IntArray.missing_i ( &( "work" ) ) i 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_4 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (i < active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (Forall (Z.le (1)) weights_l )) (PreH9 : (Forall (Z.ge (1000)) weights_l )) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : (0 <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : (0 <= total)) (PreH19 : (total <= 56000)) (PreH20 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH21 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH22 : (HuffmanProgress weights_l work_l active total )) (PreH23 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i < active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (((( &( "work" ) ) + (first * sizeof(INT)))) # Int  |-> (Znth first work_l 0))
  **  (IntArray.missing_i ( &( "work" ) ) first 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_5 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (((( &( "work" ) ) + (first * sizeof(INT)))) # Int  |-> (Znth first work_l 0))
  **  (IntArray.missing_i ( &( "work" ) ) first 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_6 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (((( &( "work" ) ) + ((active - 1 ) * sizeof(INT)))) # Int  |-> (Znth (active - 1 ) work_l 0))
  **  (IntArray.missing_i ( &( "work" ) ) (active - 1 ) 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_7 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : (0 <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH19 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH20 : (HuffmanProgress weights_l work_l active total )) (PreH21 : (HuffmanMinScan work_l i first )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanProgress weights_l work_l active total ) ” 
  &&  “ (HuffmanMinScan work_l i first ) ”
  &&  (((( &( "work" ) ) + (first * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "work" ) ) first 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_8 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i < active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((( &( "work" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i work_l 0))
  **  (IntArray.missing_i ( &( "work" ) ) i 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_9 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i < active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((( &( "work" ) ) + (second * sizeof(INT)))) # Int  |-> (Znth second work_l 0))
  **  (IntArray.missing_i ( &( "work" ) ) second 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_10 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((( &( "work" ) ) + (second * sizeof(INT)))) # Int  |-> (Znth second work_l 0))
  **  (IntArray.missing_i ( &( "work" ) ) second 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_11 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((( &( "work" ) ) + ((active - 1 ) * sizeof(INT)))) # Int  |-> (Znth (active - 1 ) work_l 0))
  **  (IntArray.missing_i ( &( "work" ) ) (active - 1 ) 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_12 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((( &( "work" ) ) + (second * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "work" ) ) second 0 n_pre work_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
.

Definition huffman_cost_partial_solve_wit_13 := 
forall (n_pre: Z) (weights_pre: Z) (weights_l: (@list Z)) (total: Z) (x: Z) (second: Z) (first: Z) (i: Z) (active: Z) (work_l: (@list Z)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) weights_l )) (PreH7 : (Forall (Z.ge (1000)) weights_l )) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= first)) (PreH14 : (first < n_pre)) (PreH15 : (0 <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : (0 <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall (Z.le (1)) (sublist (0) (active) (work_l)) )) (PreH23 : (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) )) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total )) (PreH25 : (HuffmanMinScan work_l i second )) ,
  (IntArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
|--
  “ (i >= active) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (work_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge (1000)) weights_l ) ” 
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
  &&  “ (Forall (Z.le (1)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (Forall (Z.ge (8000)) (sublist (0) (active) (work_l)) ) ” 
  &&  “ (HuffmanFirstHeld weights_l work_l active x total ) ” 
  &&  “ (HuffmanMinScan work_l i second ) ”
  &&  (((( &( "work" ) ) + ((active - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "work" ) ) (active - 1 ) 0 n_pre (replace_Znth (second) ((Znth (active - 1 ) work_l 0)) (work_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "work" ) ) n_pre 8 )
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
Axiom proof_of_huffman_cost_entail_wit_8_1 : huffman_cost_entail_wit_8_1.
Axiom proof_of_huffman_cost_entail_wit_8_2 : huffman_cost_entail_wit_8_2.
Axiom proof_of_huffman_cost_entail_wit_9 : huffman_cost_entail_wit_9.
Axiom proof_of_huffman_cost_entail_wit_10 : huffman_cost_entail_wit_10.
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
