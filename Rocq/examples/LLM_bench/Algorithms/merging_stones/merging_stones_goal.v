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
Require Import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.

(*----- Function mergingStones -----*)

Definition mergingStones_safety_wit_1 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "dp" ) ) 64 )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_2 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_flat: (@list Z)) (k: Z) (PreH1 : (0 <= k)) (PreH2 : (k <= (n_pre * n_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (Forall (Z.le (1)) stones_l )) (PreH7 : (Forall (Z.ge (1000)) stones_l )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) k 64 )
|--
  “ ((n_pre * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * n_pre )) ”
.

Definition mergingStones_safety_wit_3 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_flat: (@list Z)) (k: Z) (PreH1 : (k < (n_pre * n_pre ))) (PreH2 : (0 <= k)) (PreH3 : (k <= (n_pre * n_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) stones_l )) (PreH8 : (Forall (Z.ge (1000)) stones_l )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) k 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_4 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_flat: (@list Z)) (k: Z) (PreH1 : (k < (n_pre * n_pre ))) (PreH2 : (0 <= k)) (PreH3 : (k <= (n_pre * n_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) stones_l )) (PreH8 : (Forall (Z.ge (1000)) stones_l )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (k + 1 ) (app (dp_flat) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 64 )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition mergingStones_safety_wit_5 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_flat: (@list Z)) (k: Z) (PreH1 : (k >= (n_pre * n_pre ))) (PreH2 : (0 <= k)) (PreH3 : (k <= (n_pre * n_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) stones_l )) (PreH8 : (Forall (Z.ge (1000)) stones_l )) ,
  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) k 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_6 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_flat: (@list Z)) (k: Z) (PreH1 : (k >= (n_pre * n_pre ))) (PreH2 : (0 <= k)) (PreH3 : (k <= (n_pre * n_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) stones_l )) (PreH8 : (Forall (Z.ge (1000)) stones_l )) ,
  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) k 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_7 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_flat: (@list Z)) (k: Z) (PreH1 : (k >= (n_pre * n_pre ))) (PreH2 : (0 <= k)) (PreH3 : (k <= (n_pre * n_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) stones_l )) (PreH8 : (Forall (Z.ge (1000)) stones_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (((( &( "prefix" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "prefix" ) ) 1 9 )
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) k 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_8 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mergingStones_safety_wit_9 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergingStones_safety_wit_10 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) )) ”
) \/
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) )) ”
).

Definition mergingStones_safety_wit_10_split_goal_1 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) ) <= INT_MAX) ”
.

Definition mergingStones_safety_wit_10_split_goal_2 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((INT_MIN) <= ((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) )) ”
.

Definition mergingStones_safety_wit_11 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  (IntArray.seg ( &( "prefix" ) ) 0 ((i + 1 ) + 1 ) (app (prefix_l) ((cons (((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "prefix" ) ) ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mergingStones_safety_wit_12 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_13 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (row: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l row )) ,
  ((( &( "col" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_14 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((row * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (row * n_pre )) ”
.

Definition mergingStones_safety_wit_15 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_16 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_17 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col )) ,
  (((( &( "dp" ) ) + (((row * n_pre ) + col ) * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.missing_i (( &( "dp" ) ) + ((row * n_pre ) * sizeof(INT))) col 0 n_pre (Znth row dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) row 0 n_pre n_pre dp_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((col + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (col + 1 )) ”
.

Definition mergingStones_safety_wit_18 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((row + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (row + 1 )) ”
.

Definition mergingStones_safety_wit_19 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (row: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l row )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mergingStones_safety_wit_20 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_21 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left <= ((n_pre - len ) + 1 ))) (PreH11 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((left + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + len )) ”
.

Definition mergingStones_safety_wit_22 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((left + len ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left + len ) - 1 )) ”
.

Definition mergingStones_safety_wit_23 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((left + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + len )) ”
.

Definition mergingStones_safety_wit_24 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergingStones_safety_wit_25 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) )) ”
) \/
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) )) ”
).

Definition mergingStones_safety_wit_25_split_goal_1 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= INT_MAX) ”
.

Definition mergingStones_safety_wit_25_split_goal_2 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((INT_MIN) <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) )) ”
.

Definition mergingStones_safety_wit_26 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((((left + len ) - 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((left + len ) - 1 ) + 1 )) ”
.

Definition mergingStones_safety_wit_27 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergingStones_safety_wit_28 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "best" ) )) # Int  |->_)
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  ((( &( "interval_sum" ) )) # Int  |-> ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ))
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (1000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000) ”
.

Definition mergingStones_safety_wit_29 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  ((( &( "left_value" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((left * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * n_pre )) ”
.

Definition mergingStones_safety_wit_30 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  ((( &( "left_value" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_31 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((split + 1 ) * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((split + 1 ) * n_pre )) ”
.

Definition mergingStones_safety_wit_32 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition mergingStones_safety_wit_33 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_34 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergingStones_safety_wit_35 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum )) ”
) \/
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum )) ”
).

Definition mergingStones_safety_wit_35_split_goal_1 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) <= INT_MAX) ”
.

Definition mergingStones_safety_wit_35_split_goal_2 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((INT_MIN) <= ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum )) ”
.

Definition mergingStones_safety_wit_36 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) )) ”
) \/
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) )) ”
).

Definition mergingStones_safety_wit_36_split_goal_1 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) <= INT_MAX) ”
.

Definition mergingStones_safety_wit_36_split_goal_2 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((INT_MIN) <= (left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) )) ”
.

Definition mergingStones_safety_wit_37 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) < best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH21 : (split < right)) (PreH22 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ))
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition mergingStones_safety_wit_38 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH21 : (split < right)) (PreH22 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition mergingStones_safety_wit_39 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((left * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * n_pre )) ”
.

Definition mergingStones_safety_wit_40 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_41 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (((( &( "dp" ) ) + (((left * n_pre ) + right ) * sizeof(INT)))) # Int  |-> best)
  **  (IntArray.missing_i (( &( "dp" ) ) + ((left * n_pre ) * sizeof(INT))) right 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) left 0 n_pre n_pre dp_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((left + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + 1 )) ”
.

Definition mergingStones_safety_wit_42 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len + 1 )) ”
.

Definition mergingStones_safety_wit_43 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mergingStones_safety_wit_44 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((0 * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 * n_pre )) ”
.

Definition mergingStones_safety_wit_45 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_46 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_47 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergingStones_entail_wit_1 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) ,
  (IntArray.undef_full ( &( "dp" ) ) 64 )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.full stones_pre n_pre stones_l )
|--
  EX (dp_flat: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre * n_pre )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.seg ( &( "dp" ) ) 0 0 dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) 0 64 )
.

Definition mergingStones_entail_wit_2 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_flat_2: (@list Z)) (k: Z) (PreH1 : (k < (n_pre * n_pre ))) (PreH2 : (0 <= k)) (PreH3 : (k <= (n_pre * n_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) stones_l )) (PreH8 : (Forall (Z.ge (1000)) stones_l )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (k + 1 ) (app (dp_flat_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 64 )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
|--
  EX (dp_flat: (@list Z)) ,
  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (n_pre * n_pre )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.seg ( &( "dp" ) ) 0 (k + 1 ) dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 64 )
.

Definition mergingStones_entail_wit_3 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_flat: (@list Z)) (k: Z) (PreH1 : (k >= (n_pre * n_pre ))) (PreH2 : (0 <= k)) (PreH3 : (k <= (n_pre * n_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) stones_l )) (PreH8 : (Forall (Z.ge (1000)) stones_l )) ,
  (((( &( "prefix" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "prefix" ) ) 1 9 )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) k 64 )
|--
  EX (prefix_l: (@list Z))  (dp_init: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_init)) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l 0 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (0 + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (0 + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (dp_flat: (@list Z)) (k: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (k >= (n_pre * n_pre ))) (PreH4 : (0 <= k)) (PreH5 : (k <= (n_pre * n_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 8)) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : (Forall (Z.le (1)) stones_l )) (PreH10 : (Forall (Z.ge (1000)) stones_l )) ,
  (((( &( "prefix" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "prefix" ) ) 1 9 )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
|--
  EX (prefix_l: (@list Z))  (dp_init: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_init)) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l 0 ) ”
  &&  (IntArray.seg ( &( "prefix" ) ) 0 (0 + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (0 + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
).

Definition mergingStones_entail_wit_4 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (dp_init_2: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init_2)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i )) ,
  (IntArray.seg ( &( "prefix" ) ) 0 ((i + 1 ) + 1 ) (app (prefix_l_2) ((cons (((Znth (i - 0 ) prefix_l_2 0) + (Znth i stones_l 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "prefix" ) ) ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_init: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_init)) ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l (i + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 ((i + 1 ) + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (dp_init_2: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init_2)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i )) ,
  TT && emp 
|--
  “ (StonePrefixProgress stones_l (app (prefix_l_2) ((cons (((Znth (i - 0 ) prefix_l_2 0) + (Znth i stones_l 0) )) ((@nil Z))))) (i + 1 ) ) ”
  &&  emp
).

Definition mergingStones_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (dp_init_2: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init_2)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i )) ,
  (StonePrefixProgress stones_l (app (prefix_l_2) ((cons (((Znth (i - 0 ) prefix_l_2 0) + (Znth i stones_l 0) )) ((@nil Z))))) (i + 1 ) )
.

Definition mergingStones_entail_wit_5 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (StoneZeroRows dp_l 0 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i )) ,
  TT && emp 
|--
  “ (StoneZeroRows dp_init 0 ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ”
  &&  emp
).

Definition mergingStones_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i )) ,
  (StoneZeroRows dp_init 0 )
.

Definition mergingStones_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i )) ,
  (StonePrefixDone stones_l prefix_l_2 n_pre )
.

Definition mergingStones_entail_wit_6 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (0 <= row) ” 
  &&  “ (row < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (StoneZeroProgress dp_l row 0 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row )) ,
  TT && emp 
|--
  “ (StoneZeroProgress dp_l_2 row 0 ) ”
  &&  emp
).

Definition mergingStones_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row )) ,
  (StoneZeroProgress dp_l_2 row 0 )
.

Definition mergingStones_entail_wit_7 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z)))  __default__List_Z (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 row col )) ,
  (((( &( "dp" ) ) + (((row * n_pre ) + col ) * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.missing_i (( &( "dp" ) ) + ((row * n_pre ) * sizeof(INT))) col 0 n_pre (Znth row dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) row 0 n_pre n_pre dp_l_2 )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (0 <= row) ” 
  &&  “ (row < n_pre) ” 
  &&  “ (0 <= (col + 1 )) ” 
  &&  “ ((col + 1 ) <= n_pre) ” 
  &&  “ (StoneZeroProgress dp_l row (col + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (col < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall (Z.le (1)) stones_l )) (PreH7 : (Forall (Z.ge (1000)) stones_l )) (PreH8 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (0 <= row)) (PreH11 : (row < n_pre)) (PreH12 : (0 <= col)) (PreH13 : (col <= n_pre)) (PreH14 : (StoneZeroProgress dp_l_2 row col )) ,
  (((( &( "dp" ) ) + (((row * n_pre ) + col ) * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.missing_i (( &( "dp" ) ) + ((row * n_pre ) * sizeof(INT))) col 0 n_pre (Znth row dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) row 0 n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (0 <= row) ” 
  &&  “ (row < n_pre) ” 
  &&  “ (0 <= (col + 1 )) ” 
  &&  “ ((col + 1 ) <= n_pre) ” 
  &&  “ (StoneZeroProgress dp_l row (col + 1 ) ) ”
  &&  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
).

Definition mergingStones_entail_wit_8 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 row col )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (0 <= (row + 1 )) ” 
  &&  “ ((row + 1 ) <= n_pre) ” 
  &&  “ (StoneZeroRows dp_l (row + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 row col )) ,
  TT && emp 
|--
  “ (StoneZeroRows dp_l_2 (row + 1 ) ) ”
  &&  emp
).

Definition mergingStones_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 row col )) ,
  (StoneZeroRows dp_l_2 (row + 1 ) )
.

Definition mergingStones_entail_wit_9 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre 2 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row )) ,
  TT && emp 
|--
  “ (StoneLenDone stones_l dp_l_2 n_pre 2 ) ”
  &&  emp
).

Definition mergingStones_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (row: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row )) ,
  (StoneLenDone stones_l dp_l_2 n_pre 2 )
.

Definition mergingStones_entail_wit_10 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - len ) + 1 )) ” 
  &&  “ (StoneLeftProgress stones_l dp_l n_pre len 0 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  TT && emp 
|--
  “ (StoneLeftProgress stones_l dp_l_2 n_pre len 0 ) ”
  &&  emp
).

Definition mergingStones_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  (StoneLeftProgress stones_l dp_l_2 n_pre len 0 )
.

Definition mergingStones_entail_wit_11 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l_2: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (((left + len ) - 1 ) = ((left + len ) - 1 )) ” 
  &&  “ (left <= left) ” 
  &&  “ (left <= ((left + len ) - 1 )) ” 
  &&  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) = (sum ((sublist (left) ((((left + len ) - 1 ) + 1 )) (stones_l))))) ” 
  &&  “ (2 <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) )) ” 
  &&  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= 8000) ” 
  &&  “ (0 <= 1000000) ” 
  &&  “ (1000000 <= 1000000) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left left 1000000 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  TT && emp 
|--
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left left 1000000 ) ” 
  &&  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= 8000) ” 
  &&  “ (2 <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) )) ” 
  &&  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) = (sum ((sublist (left) ((((left + len ) - 1 ) + 1 )) (stones_l))))) ”
  &&  emp
).

Definition mergingStones_entail_wit_11_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (StoneSplitProgress stones_l dp_l_2 n_pre len left left 1000000 )
.

Definition mergingStones_entail_wit_11_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= 8000)
.

Definition mergingStones_entail_wit_11_split_goal_3 := 
forall (n_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (2 <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ))
.

Definition mergingStones_entail_wit_11_split_goal_4 := 
forall (n_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) = (sum ((sublist (left) ((((left + len ) - 1 ) + 1 )) (stones_l)))))
.

Definition mergingStones_entail_wit_12 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l_2: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (((( &( "dp" ) ) + (((left * n_pre ) + split ) * sizeof(INT)))) # Int  |-> (Znth (split) ((Znth left dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + ((left * n_pre ) * sizeof(INT))) split 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) left 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l_2: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000) ” 
  &&  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best ) ” 
  &&  “ (split < right) ” 
  &&  “ ((Znth (split) ((Znth left dp_l __default__List_Z)) (0)) = (Znth split (Znth left dp_l_2 __default__List_Z) 0)) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l_2: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : ((Znth (split) ((Znth left dp_l __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (split) ((Znth left dp_l __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : (split < right)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall (Z.le (1)) stones_l )) (PreH7 : (Forall (Z.ge (1000)) stones_l )) (PreH8 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (2 <= len)) (PreH11 : (len <= n_pre)) (PreH12 : (0 <= left)) (PreH13 : ((left + len ) <= n_pre)) (PreH14 : (right = ((left + len ) - 1 ))) (PreH15 : (left <= split)) (PreH16 : (split <= right)) (PreH17 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH18 : (2 <= interval_sum)) (PreH19 : (interval_sum <= 8000)) (PreH20 : (0 <= best)) (PreH21 : (best <= 1000000)) (PreH22 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (((( &( "dp" ) ) + (((left * n_pre ) + split ) * sizeof(INT)))) # Int  |-> (Znth (split) ((Znth left dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + ((left * n_pre ) * sizeof(INT))) split 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) left 0 n_pre n_pre dp_l )
|--
  EX (dp_l_2: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000) ” 
  &&  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best ) ” 
  &&  “ (split < right) ” 
  &&  “ ((Znth (split) ((Znth left dp_l __default__List_Z)) (0)) = (Znth split (Znth left dp_l_2 __default__List_Z) 0)) ”
  &&  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2 )
).

Definition mergingStones_entail_wit_13_1 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) ) + interval_sum ) < best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) (PreH21 : (split < right)) (PreH22 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) ,
  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l_2 )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) ) + interval_sum )) ” 
  &&  “ (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) ) + interval_sum ) <= 1000000) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1 ) ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) ) + interval_sum ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : ((Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) ) + interval_sum ) < best)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall (Z.le (1)) stones_l )) (PreH7 : (Forall (Z.ge (1000)) stones_l )) (PreH8 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (2 <= len)) (PreH11 : (len <= n_pre)) (PreH12 : (0 <= left)) (PreH13 : ((left + len ) <= n_pre)) (PreH14 : (right = ((left + len ) - 1 ))) (PreH15 : (left <= split)) (PreH16 : (split <= right)) (PreH17 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH18 : (2 <= interval_sum)) (PreH19 : (interval_sum <= 8000)) (PreH20 : (0 <= best)) (PreH21 : (best <= 1000000)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) (PreH23 : (split < right)) (PreH24 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) ,
  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) ) + interval_sum )) ” 
  &&  “ (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) ) + interval_sum ) <= 1000000) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1 ) ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) ) + interval_sum ) ) ”
  &&  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
).

Definition mergingStones_entail_wit_13_2 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) ) + interval_sum ) >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) (PreH21 : (split < right)) (PreH22 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) ,
  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l_2 )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1 ) best ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : ((Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)) ) + interval_sum ) >= best)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall (Z.le (1)) stones_l )) (PreH7 : (Forall (Z.ge (1000)) stones_l )) (PreH8 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (2 <= len)) (PreH11 : (len <= n_pre)) (PreH12 : (0 <= left)) (PreH13 : ((left + len ) <= n_pre)) (PreH14 : (right = ((left + len ) - 1 ))) (PreH15 : (left <= split)) (PreH16 : (split <= right)) (PreH17 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH18 : (2 <= interval_sum)) (PreH19 : (interval_sum <= 8000)) (PreH20 : (0 <= best)) (PreH21 : (best <= 1000000)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) (PreH23 : (split < right)) (PreH24 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) ,
  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l_2 __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1 ) best ) ”
  &&  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
).

Definition mergingStones_entail_wit_14 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z)))  __default__List_Z (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (((( &( "dp" ) ) + (((left * n_pre ) + right ) * sizeof(INT)))) # Int  |-> best)
  **  (IntArray.missing_i (( &( "dp" ) ) + ((left * n_pre ) * sizeof(INT))) right 0 n_pre (Znth left dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) left 0 n_pre n_pre dp_l_2 )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) <= ((n_pre - len ) + 1 )) ” 
  &&  “ (StoneLeftProgress stones_l dp_l n_pre len (left + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z)))  __default__List_Z (PreH1 : (best <= INT_MAX)) (PreH2 : (best >= INT_MIN)) (PreH3 : (split >= right)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall (Z.le (1)) stones_l )) (PreH7 : (Forall (Z.ge (1000)) stones_l )) (PreH8 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (2 <= len)) (PreH11 : (len <= n_pre)) (PreH12 : (0 <= left)) (PreH13 : ((left + len ) <= n_pre)) (PreH14 : (right = ((left + len ) - 1 ))) (PreH15 : (left <= split)) (PreH16 : (split <= right)) (PreH17 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH18 : (2 <= interval_sum)) (PreH19 : (interval_sum <= 8000)) (PreH20 : (0 <= best)) (PreH21 : (best <= 1000000)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (((( &( "dp" ) ) + (((left * n_pre ) + right ) * sizeof(INT)))) # Int  |-> best)
  **  (IntArray.missing_i (( &( "dp" ) ) + ((left * n_pre ) * sizeof(INT))) right 0 n_pre (Znth left dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) left 0 n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) <= ((n_pre - len ) + 1 )) ” 
  &&  “ (StoneLeftProgress stones_l dp_l n_pre len (left + 1 ) ) ”
  &&  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
).

Definition mergingStones_entail_wit_15 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : ((left + len ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2 )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= (len + 1 )) ” 
  &&  “ ((len + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre (len + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : ((left + len ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  TT && emp 
|--
  “ (StoneLenDone stones_l dp_l_2 n_pre (len + 1 ) ) ”
  &&  emp
).

Definition mergingStones_entail_wit_15_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : ((left + len ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l_2)) )) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (StoneLenDone stones_l dp_l_2 n_pre (len + 1 ) )
.

Definition mergingStones_entail_wit_16 := 
(
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len )) ,
  (((( &( "dp" ) ) + (((0 * n_pre ) + (n_pre - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + ((0 * n_pre ) * sizeof(INT))) (n_pre - 1 ) 0 n_pre (Znth 0 dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) 0 0 n_pre n_pre dp_l )
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (StoneMinimumCost stones_l (Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.undef_full ( &( "dp" ) ) 64 )
  **  ((( &( "width" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : ((Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : (len > n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall (Z.le (1)) stones_l )) (PreH7 : (Forall (Z.ge (1000)) stones_l )) (PreH8 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH9 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH10 : (2 <= len)) (PreH11 : (len <= (n_pre + 1 ))) (PreH12 : (StoneLenDone stones_l dp_l n_pre len )) ,
  (((( &( "dp" ) ) + (((0 * n_pre ) + (n_pre - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + ((0 * n_pre ) * sizeof(INT))) (n_pre - 1 ) 0 n_pre (Znth 0 dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) 0 0 n_pre n_pre dp_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (StoneMinimumCost stones_l (Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)) ) ”
  &&  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.undef_full ( &( "dp" ) ) 64 )
).

Definition mergingStones_entail_wit_16_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : ((Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : (len > n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall (Z.le (1)) stones_l )) (PreH7 : (Forall (Z.ge (1000)) stones_l )) (PreH8 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH9 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH10 : (2 <= len)) (PreH11 : (len <= (n_pre + 1 ))) (PreH12 : (StoneLenDone stones_l dp_l n_pre len )) ,
  (((( &( "dp" ) ) + (((0 * n_pre ) + (n_pre - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + ((0 * n_pre ) * sizeof(INT))) (n_pre - 1 ) 0 n_pre (Znth 0 dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) 0 0 n_pre n_pre dp_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (StoneMinimumCost stones_l (Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)) ) ”
.

Definition mergingStones_entail_wit_16_split_goal_spatial := 
forall (n_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : ((Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : (len > n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall (Z.le (1)) stones_l )) (PreH7 : (Forall (Z.ge (1000)) stones_l )) (PreH8 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH9 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH10 : (2 <= len)) (PreH11 : (len <= (n_pre + 1 ))) (PreH12 : (StoneLenDone stones_l dp_l n_pre len )) ,
  (((( &( "dp" ) ) + (((0 * n_pre ) + (n_pre - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + ((0 * n_pre ) * sizeof(INT))) (n_pre - 1 ) 0 n_pre (Znth 0 dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) 0 0 n_pre n_pre dp_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.undef_full ( &( "dp" ) ) 64 )
.

Definition mergingStones_return_wit_1 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (result: Z) (PreH1 : (StoneMinimumCost stones_l result )) ,
  (IntArray.full stones_pre n_pre stones_l )
|--
  “ (StoneMinimumCost stones_l result ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
.

Definition mergingStones_partial_solve_wit_1 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_flat: (@list Z)) (k: Z) (PreH1 : (k < (n_pre * n_pre ))) (PreH2 : (0 <= k)) (PreH3 : (k <= (n_pre * n_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) stones_l )) (PreH8 : (Forall (Z.ge (1000)) stones_l )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) k 64 )
|--
  “ (k < (n_pre * n_pre )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (n_pre * n_pre )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ”
  &&  (((( &( "dp" ) ) + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 64 )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
.

Definition mergingStones_partial_solve_wit_2 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_flat: (@list Z)) (k: Z) (PreH1 : (k >= (n_pre * n_pre ))) (PreH2 : (0 <= k)) (PreH3 : (k <= (n_pre * n_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) stones_l )) (PreH8 : (Forall (Z.ge (1000)) stones_l )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full ( &( "prefix" ) ) 9 )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) k 64 )
|--
  “ (k >= (n_pre * n_pre )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (n_pre * n_pre )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ”
  &&  (((( &( "prefix" ) ) + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "prefix" ) ) 1 9 )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 k dp_flat )
  **  (IntArray.undef_seg ( &( "dp" ) ) k 64 )
.

Definition mergingStones_partial_solve_wit_3 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_init)) ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l i ) ”
  &&  (((( &( "prefix" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) prefix_l 0))
  **  (IntArray.missing_i ( &( "prefix" ) ) i 0 (i + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
.

Definition mergingStones_partial_solve_wit_4 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_init)) ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l i ) ”
  &&  (((stones_pre + (i * sizeof(INT)))) # Int  |-> (Znth i stones_l 0))
  **  (IntArray.missing_i stones_pre i 0 n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
.

Definition mergingStones_partial_solve_wit_5 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (dp_init: (@list (@list Z))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_init)) )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_init)) ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l i ) ”
  &&  (((( &( "prefix" ) ) + ((i + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "prefix" ) ) ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg ( &( "prefix" ) ) 0 (i + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_init )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
.

Definition mergingStones_partial_solve_wit_6 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (col: Z) (row: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (col < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (0 <= row) ” 
  &&  “ (row < n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col <= n_pre) ” 
  &&  “ (StoneZeroProgress dp_l row col ) ”
  &&  (((( &( "dp" ) ) + (((row * n_pre ) + col ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i (( &( "dp" ) ) + ((row * n_pre ) * sizeof(INT))) col 0 n_pre (Znth row dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) row 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
.

Definition mergingStones_partial_solve_wit_7 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((left + len ) <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= ((n_pre - len ) + 1 )) ” 
  &&  “ (StoneLeftProgress stones_l dp_l n_pre len left ) ”
  &&  (((( &( "prefix" ) ) + ((((left + len ) - 1 ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth (((left + len ) - 1 ) + 1 ) prefix_l 0))
  **  (IntArray.missing_i ( &( "prefix" ) ) (((left + len ) - 1 ) + 1 ) 0 (n_pre + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
.

Definition mergingStones_partial_solve_wit_8 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= ((n_pre - len ) + 1 ))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ ((left + len ) <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= ((n_pre - len ) + 1 )) ” 
  &&  “ (StoneLeftProgress stones_l dp_l n_pre len left ) ”
  &&  (((( &( "prefix" ) ) + (left * sizeof(INT)))) # Int  |-> (Znth left prefix_l 0))
  **  (IntArray.missing_i ( &( "prefix" ) ) left 0 (n_pre + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
.

Definition mergingStones_partial_solve_wit_9 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (split < right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left split best ) ”
  &&  (((( &( "dp" ) ) + (((left * n_pre ) + split ) * sizeof(INT)))) # Int  |-> (Znth (split) ((Znth left dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + ((left * n_pre ) * sizeof(INT))) split 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) left 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
.

Definition mergingStones_partial_solve_wit_10 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z) (left_value: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall (Z.le (1)) stones_l )) (PreH4 : (Forall (Z.ge (1000)) stones_l )) (PreH5 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : ((left + len ) <= n_pre)) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left split best ) ” 
  &&  “ (split < right) ” 
  &&  “ (left_value = (Znth split (Znth left dp_l __default__List_Z) 0)) ”
  &&  (((( &( "dp" ) ) + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) (split + 1 ) 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
.

Definition mergingStones_partial_solve_wit_11 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : ((left + len ) <= n_pre)) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (split >= right) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left split best ) ”
  &&  (((( &( "dp" ) ) + (((left * n_pre ) + right ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i (( &( "dp" ) ) + ((left * n_pre ) * sizeof(INT))) right 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) left 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
.

Definition mergingStones_partial_solve_wit_12 := 
forall (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (len: Z) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall (Z.le (1)) stones_l )) (PreH5 : (Forall (Z.ge (1000)) stones_l )) (PreH6 : (Forall (eq (n_pre)) (map (Zlength) (dp_l)) )) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray2.full ( &( "dp" ) ) n_pre n_pre dp_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
|--
  “ (len > n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (Forall (Z.le (1)) stones_l ) ” 
  &&  “ (Forall (Z.ge (1000)) stones_l ) ” 
  &&  “ (Forall (eq (n_pre)) (map (Zlength) (dp_l)) ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= (n_pre + 1 )) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre len ) ”
  &&  (((( &( "dp" ) ) + (((0 * n_pre ) + (n_pre - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dp" ) ) + ((0 * n_pre ) * sizeof(INT))) (n_pre - 1 ) 0 n_pre (Znth 0 dp_l __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dp" ) ) 0 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full ( &( "prefix" ) ) (n_pre + 1 ) prefix_l )
  **  (IntArray.undef_seg ( &( "prefix" ) ) (n_pre + 1 ) 9 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre ) 64 )
.

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include int_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.

Axiom proof_of_mergingStones_safety_wit_1 : mergingStones_safety_wit_1.
Axiom proof_of_mergingStones_safety_wit_2 : mergingStones_safety_wit_2.
Axiom proof_of_mergingStones_safety_wit_3 : mergingStones_safety_wit_3.
Axiom proof_of_mergingStones_safety_wit_4 : mergingStones_safety_wit_4.
Axiom proof_of_mergingStones_safety_wit_5 : mergingStones_safety_wit_5.
Axiom proof_of_mergingStones_safety_wit_6 : mergingStones_safety_wit_6.
Axiom proof_of_mergingStones_safety_wit_7 : mergingStones_safety_wit_7.
Axiom proof_of_mergingStones_safety_wit_8 : mergingStones_safety_wit_8.
Axiom proof_of_mergingStones_safety_wit_9 : mergingStones_safety_wit_9.
Axiom proof_of_mergingStones_safety_wit_10 : mergingStones_safety_wit_10.
Axiom proof_of_mergingStones_safety_wit_11 : mergingStones_safety_wit_11.
Axiom proof_of_mergingStones_safety_wit_12 : mergingStones_safety_wit_12.
Axiom proof_of_mergingStones_safety_wit_13 : mergingStones_safety_wit_13.
Axiom proof_of_mergingStones_safety_wit_14 : mergingStones_safety_wit_14.
Axiom proof_of_mergingStones_safety_wit_15 : mergingStones_safety_wit_15.
Axiom proof_of_mergingStones_safety_wit_16 : mergingStones_safety_wit_16.
Axiom proof_of_mergingStones_safety_wit_17 : mergingStones_safety_wit_17.
Axiom proof_of_mergingStones_safety_wit_18 : mergingStones_safety_wit_18.
Axiom proof_of_mergingStones_safety_wit_19 : mergingStones_safety_wit_19.
Axiom proof_of_mergingStones_safety_wit_20 : mergingStones_safety_wit_20.
Axiom proof_of_mergingStones_safety_wit_21 : mergingStones_safety_wit_21.
Axiom proof_of_mergingStones_safety_wit_22 : mergingStones_safety_wit_22.
Axiom proof_of_mergingStones_safety_wit_23 : mergingStones_safety_wit_23.
Axiom proof_of_mergingStones_safety_wit_24 : mergingStones_safety_wit_24.
Axiom proof_of_mergingStones_safety_wit_25 : mergingStones_safety_wit_25.
Axiom proof_of_mergingStones_safety_wit_26 : mergingStones_safety_wit_26.
Axiom proof_of_mergingStones_safety_wit_27 : mergingStones_safety_wit_27.
Axiom proof_of_mergingStones_safety_wit_28 : mergingStones_safety_wit_28.
Axiom proof_of_mergingStones_safety_wit_29 : mergingStones_safety_wit_29.
Axiom proof_of_mergingStones_safety_wit_30 : mergingStones_safety_wit_30.
Axiom proof_of_mergingStones_safety_wit_31 : mergingStones_safety_wit_31.
Axiom proof_of_mergingStones_safety_wit_32 : mergingStones_safety_wit_32.
Axiom proof_of_mergingStones_safety_wit_33 : mergingStones_safety_wit_33.
Axiom proof_of_mergingStones_safety_wit_34 : mergingStones_safety_wit_34.
Axiom proof_of_mergingStones_safety_wit_35 : mergingStones_safety_wit_35.
Axiom proof_of_mergingStones_safety_wit_36 : mergingStones_safety_wit_36.
Axiom proof_of_mergingStones_safety_wit_37 : mergingStones_safety_wit_37.
Axiom proof_of_mergingStones_safety_wit_38 : mergingStones_safety_wit_38.
Axiom proof_of_mergingStones_safety_wit_39 : mergingStones_safety_wit_39.
Axiom proof_of_mergingStones_safety_wit_40 : mergingStones_safety_wit_40.
Axiom proof_of_mergingStones_safety_wit_41 : mergingStones_safety_wit_41.
Axiom proof_of_mergingStones_safety_wit_42 : mergingStones_safety_wit_42.
Axiom proof_of_mergingStones_safety_wit_43 : mergingStones_safety_wit_43.
Axiom proof_of_mergingStones_safety_wit_44 : mergingStones_safety_wit_44.
Axiom proof_of_mergingStones_safety_wit_45 : mergingStones_safety_wit_45.
Axiom proof_of_mergingStones_safety_wit_46 : mergingStones_safety_wit_46.
Axiom proof_of_mergingStones_safety_wit_47 : mergingStones_safety_wit_47.
Axiom proof_of_mergingStones_entail_wit_1 : mergingStones_entail_wit_1.
Axiom proof_of_mergingStones_entail_wit_2 : mergingStones_entail_wit_2.
Axiom proof_of_mergingStones_entail_wit_3 : mergingStones_entail_wit_3.
Axiom proof_of_mergingStones_entail_wit_4 : mergingStones_entail_wit_4.
Axiom proof_of_mergingStones_entail_wit_5 : mergingStones_entail_wit_5.
Axiom proof_of_mergingStones_entail_wit_6 : mergingStones_entail_wit_6.
Axiom proof_of_mergingStones_entail_wit_7 : mergingStones_entail_wit_7.
Axiom proof_of_mergingStones_entail_wit_8 : mergingStones_entail_wit_8.
Axiom proof_of_mergingStones_entail_wit_9 : mergingStones_entail_wit_9.
Axiom proof_of_mergingStones_entail_wit_10 : mergingStones_entail_wit_10.
Axiom proof_of_mergingStones_entail_wit_11 : mergingStones_entail_wit_11.
Axiom proof_of_mergingStones_entail_wit_12 : mergingStones_entail_wit_12.
Axiom proof_of_mergingStones_entail_wit_13_1 : mergingStones_entail_wit_13_1.
Axiom proof_of_mergingStones_entail_wit_13_2 : mergingStones_entail_wit_13_2.
Axiom proof_of_mergingStones_entail_wit_14 : mergingStones_entail_wit_14.
Axiom proof_of_mergingStones_entail_wit_15 : mergingStones_entail_wit_15.
Axiom proof_of_mergingStones_entail_wit_16 : mergingStones_entail_wit_16.
Axiom proof_of_mergingStones_return_wit_1 : mergingStones_return_wit_1.
Axiom proof_of_mergingStones_partial_solve_wit_1 : mergingStones_partial_solve_wit_1.
Axiom proof_of_mergingStones_partial_solve_wit_2 : mergingStones_partial_solve_wit_2.
Axiom proof_of_mergingStones_partial_solve_wit_3 : mergingStones_partial_solve_wit_3.
Axiom proof_of_mergingStones_partial_solve_wit_4 : mergingStones_partial_solve_wit_4.
Axiom proof_of_mergingStones_partial_solve_wit_5 : mergingStones_partial_solve_wit_5.
Axiom proof_of_mergingStones_partial_solve_wit_6 : mergingStones_partial_solve_wit_6.
Axiom proof_of_mergingStones_partial_solve_wit_7 : mergingStones_partial_solve_wit_7.
Axiom proof_of_mergingStones_partial_solve_wit_8 : mergingStones_partial_solve_wit_8.
Axiom proof_of_mergingStones_partial_solve_wit_9 : mergingStones_partial_solve_wit_9.
Axiom proof_of_mergingStones_partial_solve_wit_10 : mergingStones_partial_solve_wit_10.
Axiom proof_of_mergingStones_partial_solve_wit_11 : mergingStones_partial_solve_wit_11.
Axiom proof_of_mergingStones_partial_solve_wit_12 : mergingStones_partial_solve_wit_12.

End VC_Correct.
