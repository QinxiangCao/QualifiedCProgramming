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
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre )) (PreH5 : (StoneTableShape dp_init n_pre )) ,
  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_2 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre )) (PreH5 : (StoneTableShape dp_init n_pre )) ,
  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_3 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre )) (PreH5 : (StoneTableShape dp_init n_pre )) (PreH6 : (StonePrefixProgress stones_l (cons (0) ((@nil Z))) n_pre 0 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg prefix_pre 1 (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_4 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i )) (PreH9 : (0 <= (Znth i prefix_l 0))) (PreH10 : ((Znth i prefix_l 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mergingStones_safety_wit_5 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i )) (PreH9 : (0 <= (Znth i prefix_l 0))) (PreH10 : ((Znth i prefix_l 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergingStones_safety_wit_6 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i )) (PreH9 : (0 <= (Znth i prefix_l 0))) (PreH10 : ((Znth i prefix_l 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) )) ”
) \/
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i )) (PreH9 : (0 <= (Znth i prefix_l 0))) (PreH10 : ((Znth i prefix_l 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) )) ”
).

Definition mergingStones_safety_wit_6_split_goal_1 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i )) (PreH9 : (0 <= (Znth i prefix_l 0))) (PreH10 : ((Znth i prefix_l 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) ) <= INT_MAX) ”
.

Definition mergingStones_safety_wit_6_split_goal_2 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i )) (PreH9 : (0 <= (Znth i prefix_l 0))) (PreH10 : ((Znth i prefix_l 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ ((INT_MIN) <= ((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) )) ”
.

Definition mergingStones_safety_wit_7 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i )) (PreH9 : (0 <= (Znth i prefix_l 0))) (PreH10 : ((Znth i prefix_l 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  (IntArray.seg prefix_pre 0 ((i + 1 ) + 1 ) (app (prefix_l) ((cons (((Znth (i - 0 ) prefix_l 0) + (Znth i stones_l 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg prefix_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mergingStones_safety_wit_8 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) ,
  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_9 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (row: Z) (prefix_l: (@list Z)) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH10 : (StoneZeroRows dp_l n_pre row )) ,
  ((( &( "col" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_10 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (col: Z) (row: Z) (prefix_l: (@list Z)) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row < n_pre)) (PreH8 : (0 <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneZeroProgress dp_l n_pre row col )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((row * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (row * n_pre )) ”
.

Definition mergingStones_safety_wit_11 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (col: Z) (row: Z) (prefix_l: (@list Z)) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row < n_pre)) (PreH8 : (0 <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneZeroProgress dp_l n_pre row col )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_12 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (col: Z) (row: Z) (prefix_l: (@list Z))  __default__List_Z (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row < n_pre)) (PreH8 : (0 <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneZeroProgress dp_l n_pre row col )) ,
  (((dp_pre + (((row * n_pre ) + col ) * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.missing_i (dp_pre + ((row * n_pre ) * sizeof(INT))) col 0 n_pre (Znth row dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre row 0 n_pre n_pre dp_l )
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "col" ) )) # Int  |-> col)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
|--
  “ ((col + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (col + 1 )) ”
.

Definition mergingStones_safety_wit_13 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (row: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= row)) (PreH4 : (row < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH9 : (StoneZeroRows dp_l n_pre (row + 1 ) )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((row + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (row + 1 )) ”
.

Definition mergingStones_safety_wit_14 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (StoneZeroRows dp_l n_pre n_pre )) (PreH8 : (StoneLenDone stones_l dp_l n_pre 2 )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mergingStones_safety_wit_15 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (len: Z) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1 ))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH10 : (StoneLenDone stones_l dp_l n_pre len )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_16 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : (left <= ((n_pre - len ) + 1 ))) (PreH7 : ((Zlength (stones_l)) = n_pre)) (PreH8 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH9 : (StoneMassesBounded stones_l n_pre )) (PreH10 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH11 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((left + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + len )) ”
.

Definition mergingStones_safety_wit_17 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (((left + len ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left + len ) - 1 )) ”
.

Definition mergingStones_safety_wit_18 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((left + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + len )) ”
.

Definition mergingStones_safety_wit_19 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergingStones_safety_wit_20 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) )) ”
) \/
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) )) ”
).

Definition mergingStones_safety_wit_20_split_goal_1 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= INT_MAX) ”
.

Definition mergingStones_safety_wit_20_split_goal_2 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((INT_MIN) <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) )) ”
.

Definition mergingStones_safety_wit_21 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((((left + len ) - 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((left + len ) - 1 ) + 1 )) ”
.

Definition mergingStones_safety_wit_22 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "interval_sum" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergingStones_safety_wit_23 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  ((( &( "best" ) )) # Int  |->_)
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  ((( &( "interval_sum" ) )) # Int  |-> ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ))
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (1000000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000) ”
.

Definition mergingStones_safety_wit_24 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH12 : (2 <= interval_sum)) (PreH13 : (interval_sum <= 8000)) (PreH14 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH15 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH16 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH17 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH18 : (StoneMassesBounded stones_l n_pre )) (PreH19 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  ((( &( "left_value" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((left * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * n_pre )) ”
.

Definition mergingStones_safety_wit_25 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH17 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH18 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (((split + 1 ) * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((split + 1 ) * n_pre )) ”
.

Definition mergingStones_safety_wit_26 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH17 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH18 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition mergingStones_safety_wit_27 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH17 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH18 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergingStones_safety_wit_28 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH17 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH18 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (((dp_pre + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
|--
  “ (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum )) ”
.

Definition mergingStones_safety_wit_29 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH17 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH18 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (((dp_pre + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre (split + 1 ) 0 n_pre n_pre dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
|--
  “ ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) )) ”
.

Definition mergingStones_safety_wit_30 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH12 : (right_value = (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l left right split candidate )) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l n_pre len left (split + 1 ) best )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition mergingStones_safety_wit_31 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (interval_sum: Z) (best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < n_pre)) (PreH10 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH11 : (2 <= interval_sum)) (PreH12 : (interval_sum <= 8000)) (PreH13 : (0 <= best)) (PreH14 : (best <= 56000)) (PreH15 : (StoneMassesBounded stones_l n_pre )) (PreH16 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH17 : (StoneSplitProgress stones_l dp_l n_pre len left right best )) (PreH18 : (StoneIntervalMin stones_l left right best )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "interval_sum" ) )) # Int  |-> interval_sum)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((left * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * n_pre )) ”
.

Definition mergingStones_safety_wit_32 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_old: (@list (@list Z))) (dp_new: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (interval_sum: Z) (best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH9 : (2 <= interval_sum)) (PreH10 : (interval_sum <= 8000)) (PreH11 : (0 <= best)) (PreH12 : (best <= 56000)) (PreH13 : (StoneMassesBounded stones_l n_pre )) (PreH14 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH15 : (StoneUpdatedCell stones_l dp_old dp_new left right best )) (PreH16 : (StoneLeftProgress stones_l dp_new n_pre len (left + 1 ) )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_new )
|--
  “ ((left + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + 1 )) ”
.

Definition mergingStones_safety_wit_33 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH7 : (StoneLenDone stones_l dp_l n_pre (len + 1 ) )) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len + 1 )) ”
.

Definition mergingStones_safety_wit_34 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre )) (PreH4 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH5 : (StoneLenDone stones_l dp_l n_pre (n_pre + 1 ) )) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) )) (PreH7 : (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0))) (PreH8 : ((Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) <= 56000)) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mergingStones_safety_wit_35 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre )) (PreH4 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH5 : (StoneLenDone stones_l dp_l n_pre (n_pre + 1 ) )) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) )) (PreH7 : (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0))) (PreH8 : ((Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) <= 56000)) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((0 * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 * n_pre )) ”
.

Definition mergingStones_safety_wit_36 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre )) (PreH4 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH5 : (StoneLenDone stones_l dp_l n_pre (n_pre + 1 ) )) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) )) (PreH7 : (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0))) (PreH8 : ((Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) <= 56000)) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mergingStones_safety_wit_37 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre )) (PreH4 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH5 : (StoneLenDone stones_l dp_l n_pre (n_pre + 1 ) )) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) )) (PreH7 : (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0))) (PreH8 : ((Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) <= 56000)) ,
  ((( &( "stones" ) )) # Ptr  |-> stones_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> n_pre)
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergingStones_entail_wit_1 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre )) (PreH5 : (StoneTableShape dp_init n_pre )) ,
  (((prefix_pre + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg prefix_pre 1 (n_pre + 1 ) )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StoneTableShape dp_init n_pre ) ” 
  &&  “ (StonePrefixProgress stones_l (cons (0) ((@nil Z))) n_pre 0 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg prefix_pre 1 (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
) \/
(
forall (prefix_pre: Z) (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) ,
  (((prefix_pre + (0 * sizeof(INT)))) # Int  |-> 0)
|--
  “ (StonePrefixProgress stones_l (cons (0) ((@nil Z))) n_pre 0 ) ”
  &&  (IntArray.seg prefix_pre 0 1 (cons (0) ((@nil Z))) )
).

Definition mergingStones_entail_wit_1_split_goal_1 := 
forall (prefix_pre: Z) (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) ,
  (((prefix_pre + (0 * sizeof(INT)))) # Int  |-> 0)
|--
  “ (StonePrefixProgress stones_l (cons (0) ((@nil Z))) n_pre 0 ) ”
.

Definition mergingStones_entail_wit_1_split_goal_spatial := 
forall (prefix_pre: Z) (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) ,
  (((prefix_pre + (0 * sizeof(INT)))) # Int  |-> 0)
|--
  (IntArray.seg prefix_pre 0 1 (cons (0) ((@nil Z))) )
.

Definition mergingStones_entail_wit_2 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre )) (PreH5 : (StoneTableShape dp_init n_pre )) (PreH6 : (StonePrefixProgress stones_l (cons (0) ((@nil Z))) n_pre 0 )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg prefix_pre 1 (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  EX (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StoneTableShape dp_init n_pre ) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l n_pre 0 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (0 + 1 ) prefix_l )
  **  (IntArray.undef_seg prefix_pre (0 + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
) \/
(
forall (prefix_pre: Z) (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre )) (PreH5 : (StoneTableShape dp_init n_pre )) (PreH6 : (StonePrefixProgress stones_l (cons (0) ((@nil Z))) n_pre 0 )) ,
  (IntArray.seg prefix_pre 0 1 (cons (0) ((@nil Z))) )
|--
  EX (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StoneTableShape dp_init n_pre ) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l n_pre 0 ) ”
  &&  (IntArray.seg prefix_pre 0 (0 + 1 ) prefix_l )
).

Definition mergingStones_entail_wit_3 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StoneTableShape dp_init n_pre )) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l_2 )
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  EX (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StoneTableShape dp_init n_pre ) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l n_pre i ) ” 
  &&  “ (0 <= (Znth i prefix_l 0)) ” 
  &&  “ ((Znth i prefix_l 0) <= 8000) ” 
  &&  “ (1 <= (Znth i stones_l 0)) ” 
  &&  “ ((Znth i stones_l 0) <= 1000) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
) \/
(
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StoneTableShape dp_init n_pre )) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) ,
  TT && emp 
|--
  “ ((Znth i stones_l 0) <= 1000) ” 
  &&  “ (1 <= (Znth i stones_l 0)) ” 
  &&  “ ((Znth i prefix_l_2 0) <= 8000) ” 
  &&  “ (0 <= (Znth i prefix_l_2 0)) ”
  &&  emp
).

Definition mergingStones_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StoneTableShape dp_init n_pre )) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) ,
  ((Znth i stones_l 0) <= 1000)
.

Definition mergingStones_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StoneTableShape dp_init n_pre )) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) ,
  (1 <= (Znth i stones_l 0))
.

Definition mergingStones_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StoneTableShape dp_init n_pre )) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) ,
  ((Znth i prefix_l_2 0) <= 8000)
.

Definition mergingStones_entail_wit_3_split_goal_4 := 
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StoneTableShape dp_init n_pre )) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) ,
  (0 <= (Znth i prefix_l_2 0))
.

Definition mergingStones_entail_wit_4 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) (PreH9 : (0 <= (Znth i prefix_l_2 0))) (PreH10 : ((Znth i prefix_l_2 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  (IntArray.seg prefix_pre 0 ((i + 1 ) + 1 ) (app (prefix_l_2) ((cons (((Znth (i - 0 ) prefix_l_2 0) + (Znth i stones_l 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg prefix_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  EX (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StoneTableShape dp_init n_pre ) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l n_pre (i + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 ((i + 1 ) + 1 ) prefix_l )
  **  (IntArray.undef_seg prefix_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
) \/
(
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) (PreH9 : (0 <= (Znth i prefix_l_2 0))) (PreH10 : ((Znth i prefix_l_2 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  TT && emp 
|--
  “ (StonePrefixProgress stones_l (app (prefix_l_2) ((cons (((Znth (i - 0 ) prefix_l_2 0) + (Znth i stones_l 0) )) ((@nil Z))))) n_pre (i + 1 ) ) ”
  &&  emp
).

Definition mergingStones_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) (PreH9 : (0 <= (Znth i prefix_l_2 0))) (PreH10 : ((Znth i prefix_l_2 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  (StonePrefixProgress stones_l (app (prefix_l_2) ((cons (((Znth (i - 0 ) prefix_l_2 0) + (Znth i stones_l 0) )) ((@nil Z))))) n_pre (i + 1 ) )
.

Definition mergingStones_entail_wit_5 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StoneTableShape dp_init n_pre )) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l_2 )
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  EX (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneTableShape dp_init n_pre ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
) \/
(
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StoneTableShape dp_init n_pre )) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) ,
  TT && emp 
|--
  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ ((Zlength (prefix_l_2)) = (n_pre + 1 )) ”
  &&  emp
).

Definition mergingStones_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StoneTableShape dp_init n_pre )) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) ,
  (StonePrefixDone stones_l prefix_l_2 n_pre )
.

Definition mergingStones_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StoneTableShape dp_init n_pre )) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 n_pre i )) ,
  ((Zlength (prefix_l_2)) = (n_pre + 1 ))
.

Definition mergingStones_entail_wit_6 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneZeroRows dp_l n_pre 0 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) ,
  TT && emp 
|--
  “ (StoneZeroRows dp_init n_pre 0 ) ”
  &&  emp
).

Definition mergingStones_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) ,
  (StoneZeroRows dp_init n_pre 0 )
.

Definition mergingStones_entail_wit_7 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (row: Z) (prefix_l_2: (@list Z)) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneZeroRows dp_l_2 n_pre row )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (0 <= row) ” 
  &&  “ (row < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneZeroProgress dp_l n_pre row 0 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (row: Z) (prefix_l_2: (@list Z)) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneZeroRows dp_l_2 n_pre row )) ,
  TT && emp 
|--
  “ (StoneZeroProgress dp_l_2 n_pre row 0 ) ”
  &&  emp
).

Definition mergingStones_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (row: Z) (prefix_l_2: (@list Z)) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneZeroRows dp_l_2 n_pre row )) ,
  (StoneZeroProgress dp_l_2 n_pre row 0 )
.

Definition mergingStones_entail_wit_8 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (col: Z) (row: Z) (prefix_l_2: (@list Z))  __default__List_Z (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row < n_pre)) (PreH8 : (0 <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH12 : (StoneZeroProgress dp_l_2 n_pre row col )) ,
  (((dp_pre + (((row * n_pre ) + col ) * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.missing_i (dp_pre + ((row * n_pre ) * sizeof(INT))) col 0 n_pre (Znth row dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i dp_pre row 0 n_pre n_pre dp_l_2 )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (0 <= row) ” 
  &&  “ (row < n_pre) ” 
  &&  “ (0 <= (col + 1 )) ” 
  &&  “ ((col + 1 ) <= n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneZeroProgress dp_l n_pre row (col + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (dp_pre: Z) (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (col: Z) (row: Z) (prefix_l_2: (@list Z))  __default__List_Z (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (col < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH8 : (0 <= row)) (PreH9 : (row < n_pre)) (PreH10 : (0 <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneMassesBounded stones_l n_pre )) (PreH13 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH14 : (StoneZeroProgress dp_l_2 n_pre row col )) ,
  (((dp_pre + (((row * n_pre ) + col ) * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.missing_i (dp_pre + ((row * n_pre ) * sizeof(INT))) col 0 n_pre (Znth row dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i dp_pre row 0 n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l_2)) = (n_pre + 1 )) ” 
  &&  “ (0 <= row) ” 
  &&  “ (row < n_pre) ” 
  &&  “ (0 <= (col + 1 )) ” 
  &&  “ ((col + 1 ) <= n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (StoneZeroProgress dp_l n_pre row (col + 1 ) ) ”
  &&  (IntArray2.full dp_pre n_pre n_pre dp_l )
).

Definition mergingStones_entail_wit_9 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (col: Z) (row: Z) (prefix_l_2: (@list Z)) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row < n_pre)) (PreH8 : (0 <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH12 : (StoneZeroProgress dp_l_2 n_pre row col )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (0 <= row) ” 
  &&  “ (row < n_pre) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneZeroRows dp_l n_pre (row + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (col: Z) (row: Z) (prefix_l_2: (@list Z)) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row < n_pre)) (PreH8 : (0 <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH12 : (StoneZeroProgress dp_l_2 n_pre row col )) ,
  TT && emp 
|--
  “ (StoneZeroRows dp_l_2 n_pre (row + 1 ) ) ”
  &&  emp
).

Definition mergingStones_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (col: Z) (row: Z) (prefix_l_2: (@list Z)) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row < n_pre)) (PreH8 : (0 <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH12 : (StoneZeroProgress dp_l_2 n_pre row col )) ,
  (StoneZeroRows dp_l_2 n_pre (row + 1 ) )
.

Definition mergingStones_entail_wit_10 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (row: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= row)) (PreH4 : (row < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH7 : (StoneMassesBounded stones_l n_pre )) (PreH8 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH9 : (StoneZeroRows dp_l_2 n_pre (row + 1 ) )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (0 <= (row + 1 )) ” 
  &&  “ ((row + 1 ) <= n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneZeroRows dp_l n_pre (row + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
.

Definition mergingStones_entail_wit_11 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (row: Z) (prefix_l_2: (@list Z)) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneZeroRows dp_l_2 n_pre row )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneZeroRows dp_l n_pre n_pre ) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre 2 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (row: Z) (prefix_l_2: (@list Z)) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneZeroRows dp_l_2 n_pre row )) ,
  TT && emp 
|--
  “ (StoneLenDone stones_l dp_l_2 n_pre 2 ) ” 
  &&  “ (StoneZeroRows dp_l_2 n_pre n_pre ) ”
  &&  emp
).

Definition mergingStones_entail_wit_11_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (row: Z) (prefix_l_2: (@list Z)) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneZeroRows dp_l_2 n_pre row )) ,
  (StoneLenDone stones_l dp_l_2 n_pre 2 )
.

Definition mergingStones_entail_wit_11_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (row: Z) (prefix_l_2: (@list Z)) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row <= n_pre)) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneZeroRows dp_l_2 n_pre row )) ,
  (StoneZeroRows dp_l_2 n_pre n_pre )
.

Definition mergingStones_entail_wit_12 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH7 : (StoneZeroRows dp_l_2 n_pre n_pre )) (PreH8 : (StoneLenDone stones_l dp_l_2 n_pre 2 )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre 2 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
.

Definition mergingStones_entail_wit_13 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (len: Z) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1 ))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - len ) + 1 )) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneLeftProgress stones_l dp_l n_pre len 0 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (len: Z) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1 ))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  TT && emp 
|--
  “ (StoneLeftProgress stones_l dp_l_2 n_pre len 0 ) ”
  &&  emp
).

Definition mergingStones_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (len: Z) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1 ))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  (StoneLeftProgress stones_l dp_l_2 n_pre len 0 )
.

Definition mergingStones_entail_wit_14 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (((left + len ) - 1 ) = ((left + len ) - 1 )) ” 
  &&  “ (left < ((left + len ) - 1 )) ” 
  &&  “ (((left + len ) - 1 ) < n_pre) ” 
  &&  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) = (sum ((sublist (left) ((((left + len ) - 1 ) + 1 )) (stones_l))))) ” 
  &&  “ (2 <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) )) ” 
  &&  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= 8000) ” 
  &&  “ (1000000 = 1000000) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l_2)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left left 1000000 ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  TT && emp 
|--
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left left 1000000 ) ” 
  &&  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= 8000) ” 
  &&  “ (2 <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) )) ” 
  &&  “ (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) = (sum ((sublist (left) ((((left + len ) - 1 ) + 1 )) (stones_l))))) ”
  &&  emp
).

Definition mergingStones_entail_wit_14_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (StoneSplitProgress stones_l dp_l_2 n_pre len left left 1000000 )
.

Definition mergingStones_entail_wit_14_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) <= 8000)
.

Definition mergingStones_entail_wit_14_split_goal_3 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (2 <= ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ))
.

Definition mergingStones_entail_wit_14_split_goal_4 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth left prefix_l 0) ) = (sum ((sublist (left) ((((left + len ) - 1 ) + 1 )) (stones_l)))))
.

Definition mergingStones_entail_wit_15 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (interval_sum: Z) (best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < n_pre)) (PreH10 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH11 : (2 <= interval_sum)) (PreH12 : (interval_sum <= 8000)) (PreH13 : (best = 1000000)) (PreH14 : ((Zlength (stones_l)) = n_pre)) (PreH15 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH16 : (StoneMassesBounded stones_l n_pre )) (PreH17 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH18 : (StoneSplitProgress stones_l dp_l_2 n_pre len left left best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (left <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left left best ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
.

Definition mergingStones_entail_wit_16 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z)  __default__List_Z (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= (Znth split (Znth left dp_l __default__List_Z) 0)) ” 
  &&  “ ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000) ” 
  &&  “ (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0)) ” 
  &&  “ ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left split best ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z)  __default__List_Z (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  TT && emp 
|--
  “ ((Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0) <= 56000) ” 
  &&  “ (0 <= (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth split (Znth left dp_l_2 __default__List_Z) 0) <= 56000) ” 
  &&  “ (0 <= (Znth split (Znth left dp_l_2 __default__List_Z) 0)) ”
  &&  emp
).

Definition mergingStones_entail_wit_16_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z)  __default__List_Z (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  ((Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0) <= 56000)
.

Definition mergingStones_entail_wit_16_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z)  __default__List_Z (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (0 <= (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))
.

Definition mergingStones_entail_wit_16_split_goal_3 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z)  __default__List_Z (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  ((Znth split (Znth left dp_l_2 __default__List_Z) 0) <= 56000)
.

Definition mergingStones_entail_wit_16_split_goal_4 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z)  __default__List_Z (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (0 <= (Znth split (Znth left dp_l_2 __default__List_Z) 0))
.

Definition mergingStones_entail_wit_17 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH12 : (2 <= interval_sum)) (PreH13 : (interval_sum <= 8000)) (PreH14 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH15 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH16 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH17 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH18 : (StoneMassesBounded stones_l n_pre )) (PreH19 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (((dp_pre + (((left * n_pre ) + split ) * sizeof(INT)))) # Int  |-> (Znth (split) ((Znth left dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + ((left * n_pre ) * sizeof(INT))) split 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre left 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
|--
  EX (prefix_l: (@list Z))  (dp_l_2: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ ((Znth (split) ((Znth left dp_l __default__List_Z)) (0)) = (Znth split (Znth left dp_l_2 __default__List_Z) 0)) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= (Znth split (Znth left dp_l_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth split (Znth left dp_l_2 __default__List_Z) 0) <= 56000) ” 
  &&  “ (0 <= (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0) <= 56000) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
) \/
(
forall (dp_pre: Z) (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : ((Znth (split) ((Znth left dp_l __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (split) ((Znth left dp_l __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (2 <= len)) (PreH6 : (len <= n_pre)) (PreH7 : (0 <= left)) (PreH8 : ((left + len ) <= n_pre)) (PreH9 : (right = ((left + len ) - 1 ))) (PreH10 : (left <= split)) (PreH11 : (split < right)) (PreH12 : (right < n_pre)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH17 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH18 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH19 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (((dp_pre + (((left * n_pre ) + split ) * sizeof(INT)))) # Int  |-> (Znth (split) ((Znth left dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + ((left * n_pre ) * sizeof(INT))) split 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre left 0 n_pre n_pre dp_l )
|--
  EX (dp_l_2: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ ((Znth (split) ((Znth left dp_l __default__List_Z)) (0)) = (Znth split (Znth left dp_l_2 __default__List_Z) 0)) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= (Znth split (Znth left dp_l_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth split (Znth left dp_l_2 __default__List_Z) 0) <= 56000) ” 
  &&  “ (0 <= (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0) <= 56000) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best ) ”
  &&  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
).

Definition mergingStones_entail_wit_18 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH17 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH18 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (((dp_pre + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre (split + 1 ) 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
|--
  EX (prefix_l: (@list Z))  (dp_l_2: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0)) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) = ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum )) ” 
  &&  “ (0 <= ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum )) ” 
  &&  “ (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) <= 56000) ” 
  &&  “ (StoneSplitCandidate stones_l dp_l_2 left right split ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) ) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
) \/
(
forall (dp_pre: Z) (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : ((Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (2 <= len)) (PreH6 : (len <= n_pre)) (PreH7 : (0 <= left)) (PreH8 : ((left + len ) <= n_pre)) (PreH9 : (right = ((left + len ) - 1 ))) (PreH10 : (left <= split)) (PreH11 : (split < right)) (PreH12 : (right < n_pre)) (PreH13 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH18 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH19 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH20 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH21 : (StoneMassesBounded stones_l n_pre )) (PreH22 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH23 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (((dp_pre + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre (split + 1 ) 0 n_pre n_pre dp_l )
|--
  EX (dp_l_2: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0)) ” 
  &&  “ ((Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0)) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (0 <= ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum )) ” 
  &&  “ (((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) <= 56000) ” 
  &&  “ (StoneSplitCandidate stones_l dp_l_2 left right split ((left_value + (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)) ) + interval_sum ) ) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best ) ”
  &&  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
).

Definition mergingStones_entail_wit_19_1 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (candidate < best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH13 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH16 : (0 <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (left_value = (Znth split (Znth left dp_l __default__List_Z) 0)) ” 
  &&  “ (right_value = (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0)) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (candidate = ((left_value + right_value ) + interval_sum )) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 56000) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 1000000) ” 
  &&  “ (StoneSplitCandidate stones_l dp_l left right split candidate ) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1 ) candidate ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (candidate < best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH13 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH16 : (0 <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  TT && emp 
|--
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1 ) candidate ) ”
  &&  emp
).

Definition mergingStones_entail_wit_19_1_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (candidate < best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH13 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH16 : (0 <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1 ) candidate )
.

Definition mergingStones_entail_wit_19_2 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (candidate >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH13 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH16 : (0 <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (prefix_l: (@list Z))  (dp_l: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (left_value = (Znth split (Znth left dp_l __default__List_Z) 0)) ” 
  &&  “ (right_value = (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0)) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (candidate = ((left_value + right_value ) + interval_sum )) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 56000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000) ” 
  &&  “ (StoneSplitCandidate stones_l dp_l left right split candidate ) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1 ) best ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (candidate >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH13 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH16 : (0 <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  TT && emp 
|--
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1 ) best ) ” 
  &&  “ (0 <= best) ”
  &&  emp
).

Definition mergingStones_entail_wit_19_2_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (candidate >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH13 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH16 : (0 <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1 ) best )
.

Definition mergingStones_entail_wit_19_2_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (candidate >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left <= split)) (PreH10 : (split < right)) (PreH11 : (right < n_pre)) (PreH12 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH13 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH15 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH16 : (0 <= candidate)) (PreH17 : (candidate <= 56000)) (PreH18 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (0 <= best)
.

Definition mergingStones_entail_wit_20 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH12 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1 ) best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (left <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= right) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1 ) best ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH12 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1 ) best )) ,
  TT && emp 
|--
  “ ((Zlength (prefix_l_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (2 <= interval_sum) ”
  &&  emp
).

Definition mergingStones_entail_wit_20_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH12 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1 ) best )) ,
  ((Zlength (prefix_l_2)) = (n_pre + 1 ))
.

Definition mergingStones_entail_wit_20_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH12 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1 ) best )) ,
  ((Zlength (stones_l)) = n_pre)
.

Definition mergingStones_entail_wit_20_split_goal_3 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH12 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1 ) best )) ,
  (interval_sum <= 8000)
.

Definition mergingStones_entail_wit_20_split_goal_4 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (interval_sum: Z) (candidate: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) 0))) (PreH12 : (right_value = (Znth right (Znth (split + 1 ) dp_l_2 __default__List_Z) 0))) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (candidate = ((left_value + right_value ) + interval_sum ))) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 56000)) (PreH17 : (0 <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitCandidate stones_l dp_l_2 left right split candidate )) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left (split + 1 ) best )) ,
  (2 <= interval_sum)
.

Definition mergingStones_entail_wit_21 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 56000) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left right best ) ” 
  &&  “ (StoneIntervalMin stones_l left right best ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  TT && emp 
|--
  “ (StoneIntervalMin stones_l left right best ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left right best ) ” 
  &&  “ (best <= 56000) ”
  &&  emp
).

Definition mergingStones_entail_wit_21_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (StoneIntervalMin stones_l left right best )
.

Definition mergingStones_entail_wit_21_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (StoneSplitProgress stones_l dp_l_2 n_pre len left right best )
.

Definition mergingStones_entail_wit_21_split_goal_3 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (best: Z) (interval_sum: Z) (split: Z) (right: Z) (left: Z) (len: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + len ) <= n_pre)) (PreH8 : (right = ((left + len ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < n_pre)) (PreH11 : (left <= split)) (PreH12 : (split <= right)) (PreH13 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH14 : (2 <= interval_sum)) (PreH15 : (interval_sum <= 8000)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000)) (PreH18 : ((Zlength (stones_l)) = n_pre)) (PreH19 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH20 : (StoneMassesBounded stones_l n_pre )) (PreH21 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best )) ,
  (best <= 56000)
.

Definition mergingStones_entail_wit_22 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < n_pre)) (PreH10 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH11 : (2 <= interval_sum)) (PreH12 : (interval_sum <= 8000)) (PreH13 : (0 <= best)) (PreH14 : (best <= 56000)) (PreH15 : (StoneMassesBounded stones_l n_pre )) (PreH16 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH17 : (StoneSplitProgress stones_l dp_l n_pre len left right best )) (PreH18 : (StoneIntervalMin stones_l left right best )) ,
  (((dp_pre + (((left * n_pre ) + right ) * sizeof(INT)))) # Int  |-> best)
  **  (IntArray.missing_i (dp_pre + ((left * n_pre ) * sizeof(INT))) right 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre left 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
|--
  EX (dp_old: (@list (@list Z)))  (dp_new: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 56000) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneUpdatedCell stones_l dp_old dp_new left right best ) ” 
  &&  “ (StoneLeftProgress stones_l dp_new n_pre len (left + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_new )
) \/
(
forall (dp_pre: Z) (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (best <= INT_MAX)) (PreH2 : (best >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (2 <= len)) (PreH6 : (len <= n_pre)) (PreH7 : (0 <= left)) (PreH8 : ((left + len ) <= n_pre)) (PreH9 : (right = ((left + len ) - 1 ))) (PreH10 : (left < right)) (PreH11 : (right < n_pre)) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : (0 <= best)) (PreH16 : (best <= 56000)) (PreH17 : (StoneMassesBounded stones_l n_pre )) (PreH18 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left right best )) (PreH20 : (StoneIntervalMin stones_l left right best )) ,
  (((dp_pre + (((left * n_pre ) + right ) * sizeof(INT)))) # Int  |-> best)
  **  (IntArray.missing_i (dp_pre + ((left * n_pre ) * sizeof(INT))) right 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre left 0 n_pre n_pre dp_l )
|--
  EX (dp_old: (@list (@list Z)))  (dp_new: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 56000) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (StoneUpdatedCell stones_l dp_old dp_new left right best ) ” 
  &&  “ (StoneLeftProgress stones_l dp_new n_pre len (left + 1 ) ) ”
  &&  (IntArray2.full dp_pre n_pre n_pre dp_new )
).

Definition mergingStones_entail_wit_23 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_old: (@list (@list Z))) (dp_new: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (interval_sum: Z) (best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH9 : (2 <= interval_sum)) (PreH10 : (interval_sum <= 8000)) (PreH11 : (0 <= best)) (PreH12 : (best <= 56000)) (PreH13 : (StoneMassesBounded stones_l n_pre )) (PreH14 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH15 : (StoneUpdatedCell stones_l dp_old dp_new left right best )) (PreH16 : (StoneLeftProgress stones_l dp_new n_pre len (left + 1 ) )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_new )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) <= ((n_pre - len ) + 1 )) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneLeftProgress stones_l dp_l n_pre len (left + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_old: (@list (@list Z))) (dp_new: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (interval_sum: Z) (best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH9 : (2 <= interval_sum)) (PreH10 : (interval_sum <= 8000)) (PreH11 : (0 <= best)) (PreH12 : (best <= 56000)) (PreH13 : (StoneMassesBounded stones_l n_pre )) (PreH14 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH15 : (StoneUpdatedCell stones_l dp_old dp_new left right best )) (PreH16 : (StoneLeftProgress stones_l dp_new n_pre len (left + 1 ) )) ,
  TT && emp 
|--
  “ ((Zlength (prefix_l_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ”
  &&  emp
).

Definition mergingStones_entail_wit_23_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_old: (@list (@list Z))) (dp_new: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (interval_sum: Z) (best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH9 : (2 <= interval_sum)) (PreH10 : (interval_sum <= 8000)) (PreH11 : (0 <= best)) (PreH12 : (best <= 56000)) (PreH13 : (StoneMassesBounded stones_l n_pre )) (PreH14 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH15 : (StoneUpdatedCell stones_l dp_old dp_new left right best )) (PreH16 : (StoneLeftProgress stones_l dp_new n_pre len (left + 1 ) )) ,
  ((Zlength (prefix_l_2)) = (n_pre + 1 ))
.

Definition mergingStones_entail_wit_23_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_old: (@list (@list Z))) (dp_new: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (interval_sum: Z) (best: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH9 : (2 <= interval_sum)) (PreH10 : (interval_sum <= 8000)) (PreH11 : (0 <= best)) (PreH12 : (best <= 56000)) (PreH13 : (StoneMassesBounded stones_l n_pre )) (PreH14 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH15 : (StoneUpdatedCell stones_l dp_old dp_new left right best )) (PreH16 : (StoneLeftProgress stones_l dp_new n_pre len (left + 1 ) )) ,
  ((Zlength (stones_l)) = n_pre)
.

Definition mergingStones_entail_wit_24 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre (len + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  TT && emp 
|--
  “ (StoneLenDone stones_l dp_l_2 n_pre (len + 1 ) ) ”
  &&  emp
).

Definition mergingStones_entail_wit_24_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left )) ,
  (StoneLenDone stones_l dp_l_2 n_pre (len + 1 ) )
.

Definition mergingStones_entail_wit_25 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH7 : (StoneLenDone stones_l dp_l_2 n_pre (len + 1 ) )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= (len + 1 )) ” 
  &&  “ ((len + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre (len + 1 ) ) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH7 : (StoneLenDone stones_l dp_l_2 n_pre (len + 1 ) )) ,
  TT && emp 
|--
  “ ((Zlength (prefix_l_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ”
  &&  emp
).

Definition mergingStones_entail_wit_25_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH7 : (StoneLenDone stones_l dp_l_2 n_pre (len + 1 ) )) ,
  ((Zlength (prefix_l_2)) = (n_pre + 1 ))
.

Definition mergingStones_entail_wit_25_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z))) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH7 : (StoneLenDone stones_l dp_l_2 n_pre (len + 1 ) )) ,
  ((Zlength (stones_l)) = n_pre)
.

Definition mergingStones_entail_wit_26 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (len: Z)  __default__List_Z (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1 ))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre (n_pre + 1 ) ) ” 
  &&  “ (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) ) ” 
  &&  “ (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0)) ” 
  &&  “ ((Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) <= 56000) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (len: Z)  __default__List_Z (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1 ))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  TT && emp 
|--
  “ ((Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0) <= 56000) ” 
  &&  “ (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0)) ” 
  &&  “ (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0) ) ” 
  &&  “ (StoneLenDone stones_l dp_l_2 n_pre (n_pre + 1 ) ) ”
  &&  emp
).

Definition mergingStones_entail_wit_26_split_goal_1 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (len: Z)  __default__List_Z (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1 ))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  ((Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0) <= 56000)
.

Definition mergingStones_entail_wit_26_split_goal_2 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (len: Z)  __default__List_Z (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1 ))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0))
.

Definition mergingStones_entail_wit_26_split_goal_3 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (len: Z)  __default__List_Z (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1 ))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0) )
.

Definition mergingStones_entail_wit_26_split_goal_4 := 
forall (n_pre: Z) (stones_l: (@list Z)) (dp_l_2: (@list (@list Z))) (prefix_l_2: (@list Z)) (len: Z) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= (n_pre + 1 ))) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : ((Zlength (prefix_l_2)) = (n_pre + 1 ))) (PreH8 : (StoneMassesBounded stones_l n_pre )) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len )) ,
  (StoneLenDone stones_l dp_l_2 n_pre (n_pre + 1 ) )
.

Definition mergingStones_return_wit_1 := 
(
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre )) (PreH4 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH5 : (StoneLenDone stones_l dp_l_2 n_pre (n_pre + 1 ) )) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0) )) (PreH7 : (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0))) (PreH8 : ((Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0) <= 56000)) ,
  (((dp_pre + (((0 * n_pre ) + (n_pre - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre - 1 )) ((Znth 0 dp_l_2 __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + ((0 * n_pre ) * sizeof(INT))) (n_pre - 1 ) 0 n_pre (Znth 0 dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i dp_pre 0 0 n_pre n_pre dp_l_2 )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l_2 )
|--
  EX (dp_l: (@list (@list Z)))  (prefix_l: (@list Z)) ,
  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre (n_pre + 1 ) ) ” 
  &&  “ (StoneMinimumCost stones_l n_pre (Znth ((n_pre - 1 )) ((Znth 0 dp_l_2 __default__List_Z)) (0)) ) ” 
  &&  “ (0 <= (Znth ((n_pre - 1 )) ((Znth 0 dp_l_2 __default__List_Z)) (0))) ” 
  &&  “ ((Znth ((n_pre - 1 )) ((Znth 0 dp_l_2 __default__List_Z)) (0)) <= 56000) ”
  &&  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
) \/
(
forall (dp_pre: Z) (n_pre: Z) (stones_l: (@list Z)) (prefix_l_2: (@list Z)) (dp_l_2: (@list (@list Z)))  __default__List_Z (PreH1 : ((Znth ((n_pre - 1 )) ((Znth 0 dp_l_2 __default__List_Z)) (0)) <= INT_MAX)) (PreH2 : ((Znth ((n_pre - 1 )) ((Znth 0 dp_l_2 __default__List_Z)) (0)) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (StoneMassesBounded stones_l n_pre )) (PreH6 : (StonePrefixDone stones_l prefix_l_2 n_pre )) (PreH7 : (StoneLenDone stones_l dp_l_2 n_pre (n_pre + 1 ) )) (PreH8 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0) )) (PreH9 : (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0))) (PreH10 : ((Znth (n_pre - 1 ) (Znth 0 dp_l_2 __default__List_Z) 0) <= 56000)) ,
  (((dp_pre + (((0 * n_pre ) + (n_pre - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre - 1 )) ((Znth 0 dp_l_2 __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + ((0 * n_pre ) * sizeof(INT))) (n_pre - 1 ) 0 n_pre (Znth 0 dp_l_2 __default__List_Z) )
  **  (IntArray2.missing_i dp_pre 0 0 n_pre n_pre dp_l_2 )
|--
  EX (dp_l: (@list (@list Z))) ,
  “ (StonePrefixDone stones_l prefix_l_2 n_pre ) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre (n_pre + 1 ) ) ” 
  &&  “ (StoneMinimumCost stones_l n_pre (Znth ((n_pre - 1 )) ((Znth 0 dp_l_2 __default__List_Z)) (0)) ) ” 
  &&  “ (0 <= (Znth ((n_pre - 1 )) ((Znth 0 dp_l_2 __default__List_Z)) (0))) ” 
  &&  “ ((Znth ((n_pre - 1 )) ((Znth 0 dp_l_2 __default__List_Z)) (0)) <= 56000) ”
  &&  (IntArray2.full dp_pre n_pre n_pre dp_l )
).

Definition mergingStones_partial_solve_wit_1 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (StoneMassesBounded stones_l n_pre )) (PreH5 : (StoneTableShape dp_init n_pre )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StoneTableShape dp_init n_pre ) ”
  &&  (((prefix_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg prefix_pre 1 (n_pre + 1 ) )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
.

Definition mergingStones_partial_solve_wit_2 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i )) (PreH9 : (0 <= (Znth i prefix_l 0))) (PreH10 : ((Znth i prefix_l 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StoneTableShape dp_init n_pre ) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l n_pre i ) ” 
  &&  “ (0 <= (Znth i prefix_l 0)) ” 
  &&  “ ((Znth i prefix_l 0) <= 8000) ” 
  &&  “ (1 <= (Znth i stones_l 0)) ” 
  &&  “ ((Znth i stones_l 0) <= 1000) ”
  &&  (((prefix_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) prefix_l 0))
  **  (IntArray.missing_i prefix_pre i 0 (i + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
.

Definition mergingStones_partial_solve_wit_3 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i )) (PreH9 : (0 <= (Znth i prefix_l 0))) (PreH10 : ((Znth i prefix_l 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StoneTableShape dp_init n_pre ) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l n_pre i ) ” 
  &&  “ (0 <= (Znth i prefix_l 0)) ” 
  &&  “ ((Znth i prefix_l 0) <= 8000) ” 
  &&  “ (1 <= (Znth i stones_l 0)) ” 
  &&  “ ((Znth i stones_l 0) <= 1000) ”
  &&  (((stones_pre + (i * sizeof(INT)))) # Int  |-> (Znth i stones_l 0))
  **  (IntArray.missing_i stones_pre i 0 n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
.

Definition mergingStones_partial_solve_wit_4 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (dp_init: (@list (@list Z))) (stones_l: (@list Z)) (prefix_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (StoneMassesBounded stones_l n_pre )) (PreH7 : (StoneTableShape dp_init n_pre )) (PreH8 : (StonePrefixProgress stones_l prefix_l n_pre i )) (PreH9 : (0 <= (Znth i prefix_l 0))) (PreH10 : ((Znth i prefix_l 0) <= 8000)) (PreH11 : (1 <= (Znth i stones_l 0))) (PreH12 : ((Znth i stones_l 0) <= 1000)) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  (IntArray.undef_seg prefix_pre (i + 1 ) (n_pre + 1 ) )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StoneTableShape dp_init n_pre ) ” 
  &&  “ (StonePrefixProgress stones_l prefix_l n_pre i ) ” 
  &&  “ (0 <= (Znth i prefix_l 0)) ” 
  &&  “ ((Znth i prefix_l 0) <= 8000) ” 
  &&  “ (1 <= (Znth i stones_l 0)) ” 
  &&  “ ((Znth i stones_l 0) <= 1000) ”
  &&  (((prefix_pre + ((i + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg prefix_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.seg prefix_pre 0 (i + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_init )
.

Definition mergingStones_partial_solve_wit_5 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (col: Z) (row: Z) (prefix_l: (@list Z))  __default__List_Z (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (stones_l)) = n_pre)) (PreH5 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH6 : (0 <= row)) (PreH7 : (row < n_pre)) (PreH8 : (0 <= col)) (PreH9 : (col <= n_pre)) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneZeroProgress dp_l n_pre row col )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (col < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (0 <= row) ” 
  &&  “ (row < n_pre) ” 
  &&  “ (0 <= col) ” 
  &&  “ (col <= n_pre) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneZeroProgress dp_l n_pre row col ) ”
  &&  (((dp_pre + (((row * n_pre ) + col ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i (dp_pre + ((row * n_pre ) * sizeof(INT))) col 0 n_pre (Znth row dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre row 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
.

Definition mergingStones_partial_solve_wit_6 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((left + len ) <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= ((n_pre - len ) + 1 )) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneLeftProgress stones_l dp_l n_pre len left ) ”
  &&  (((prefix_pre + ((((left + len ) - 1 ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth (((left + len ) - 1 ) + 1 ) prefix_l 0))
  **  (IntArray.missing_i prefix_pre (((left + len ) - 1 ) + 1 ) 0 (n_pre + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
.

Definition mergingStones_partial_solve_wit_7 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (dp_l: (@list (@list Z))) (prefix_l: (@list Z)) (left: Z) (len: Z) (PreH1 : ((left + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (2 <= len)) (PreH5 : (len <= n_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= ((n_pre - len ) + 1 ))) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : ((Zlength (prefix_l)) = (n_pre + 1 ))) (PreH10 : (StoneMassesBounded stones_l n_pre )) (PreH11 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left )) ,
  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ ((left + len ) <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= ((n_pre - len ) + 1 )) ” 
  &&  “ ((Zlength (stones_l)) = n_pre) ” 
  &&  “ ((Zlength (prefix_l)) = (n_pre + 1 )) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneLeftProgress stones_l dp_l n_pre len left ) ”
  &&  (((prefix_pre + (left * sizeof(INT)))) # Int  |-> (Znth left prefix_l 0))
  **  (IntArray.missing_i prefix_pre left 0 (n_pre + 1 ) prefix_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
.

Definition mergingStones_partial_solve_wit_8 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH12 : (2 <= interval_sum)) (PreH13 : (interval_sum <= 8000)) (PreH14 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH15 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH16 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH17 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH18 : (StoneMassesBounded stones_l n_pre )) (PreH19 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= (Znth split (Znth left dp_l __default__List_Z) 0)) ” 
  &&  “ ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000) ” 
  &&  “ (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0)) ” 
  &&  “ ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left split best ) ”
  &&  (((dp_pre + (((left * n_pre ) + split ) * sizeof(INT)))) # Int  |-> (Znth (split) ((Znth left dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + ((left * n_pre ) * sizeof(INT))) split 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre left 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
.

Definition mergingStones_partial_solve_wit_9 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left <= split)) (PreH9 : (split < right)) (PreH10 : (right < n_pre)) (PreH11 : (left_value = (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH12 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH13 : (2 <= interval_sum)) (PreH14 : (interval_sum <= 8000)) (PreH15 : (0 <= (Znth split (Znth left dp_l __default__List_Z) 0))) (PreH16 : ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000)) (PreH17 : (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0))) (PreH18 : ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000)) (PreH19 : (StoneMassesBounded stones_l n_pre )) (PreH20 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH21 : (StoneSplitProgress stones_l dp_l n_pre len left split best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (left_value = (Znth split (Znth left dp_l __default__List_Z) 0)) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= (Znth split (Znth left dp_l __default__List_Z) 0)) ” 
  &&  “ ((Znth split (Znth left dp_l __default__List_Z) 0) <= 56000) ” 
  &&  “ (0 <= (Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0)) ” 
  &&  “ ((Znth right (Znth (split + 1 ) dp_l __default__List_Z) 0) <= 56000) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left split best ) ”
  &&  (((dp_pre + ((((split + 1 ) * n_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (right) ((Znth (split + 1 ) dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + (((split + 1 ) * n_pre ) * sizeof(INT))) right 0 n_pre (Znth (split + 1 ) dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre (split + 1 ) 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
.

Definition mergingStones_partial_solve_wit_10 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z))) (len: Z) (left: Z) (right: Z) (interval_sum: Z) (best: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (2 <= len)) (PreH4 : (len <= n_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + len ) <= n_pre)) (PreH7 : (right = ((left + len ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < n_pre)) (PreH10 : (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l)))))) (PreH11 : (2 <= interval_sum)) (PreH12 : (interval_sum <= 8000)) (PreH13 : (0 <= best)) (PreH14 : (best <= 56000)) (PreH15 : (StoneMassesBounded stones_l n_pre )) (PreH16 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH17 : (StoneSplitProgress stones_l dp_l n_pre len left right best )) (PreH18 : (StoneIntervalMin stones_l left right best )) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + len ) <= n_pre) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (interval_sum = (sum ((sublist (left) ((right + 1 )) (stones_l))))) ” 
  &&  “ (2 <= interval_sum) ” 
  &&  “ (interval_sum <= 8000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 56000) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneSplitProgress stones_l dp_l n_pre len left right best ) ” 
  &&  “ (StoneIntervalMin stones_l left right best ) ”
  &&  (((dp_pre + (((left * n_pre ) + right ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i (dp_pre + ((left * n_pre ) * sizeof(INT))) right 0 n_pre (Znth left dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre left 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
.

Definition mergingStones_partial_solve_wit_11 := 
forall (dp_pre: Z) (prefix_pre: Z) (n_pre: Z) (stones_pre: Z) (stones_l: (@list Z)) (prefix_l: (@list Z)) (dp_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (StoneMassesBounded stones_l n_pre )) (PreH4 : (StonePrefixDone stones_l prefix_l n_pre )) (PreH5 : (StoneLenDone stones_l dp_l n_pre (n_pre + 1 ) )) (PreH6 : (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) )) (PreH7 : (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0))) (PreH8 : ((Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) <= 56000)) ,
  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
  **  (IntArray2.full dp_pre n_pre n_pre dp_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (StoneMassesBounded stones_l n_pre ) ” 
  &&  “ (StonePrefixDone stones_l prefix_l n_pre ) ” 
  &&  “ (StoneLenDone stones_l dp_l n_pre (n_pre + 1 ) ) ” 
  &&  “ (StoneMinimumCost stones_l n_pre (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) ) ” 
  &&  “ (0 <= (Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0)) ” 
  &&  “ ((Znth (n_pre - 1 ) (Znth 0 dp_l __default__List_Z) 0) <= 56000) ”
  &&  (((dp_pre + (((0 * n_pre ) + (n_pre - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre - 1 )) ((Znth 0 dp_l __default__List_Z)) (0)))
  **  (IntArray.missing_i (dp_pre + ((0 * n_pre ) * sizeof(INT))) (n_pre - 1 ) 0 n_pre (Znth 0 dp_l __default__List_Z) )
  **  (IntArray2.missing_i dp_pre 0 0 n_pre n_pre dp_l )
  **  (IntArray.full stones_pre n_pre stones_l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) prefix_l )
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
Axiom proof_of_mergingStones_entail_wit_13 : mergingStones_entail_wit_13.
Axiom proof_of_mergingStones_entail_wit_14 : mergingStones_entail_wit_14.
Axiom proof_of_mergingStones_entail_wit_15 : mergingStones_entail_wit_15.
Axiom proof_of_mergingStones_entail_wit_16 : mergingStones_entail_wit_16.
Axiom proof_of_mergingStones_entail_wit_17 : mergingStones_entail_wit_17.
Axiom proof_of_mergingStones_entail_wit_18 : mergingStones_entail_wit_18.
Axiom proof_of_mergingStones_entail_wit_19_1 : mergingStones_entail_wit_19_1.
Axiom proof_of_mergingStones_entail_wit_19_2 : mergingStones_entail_wit_19_2.
Axiom proof_of_mergingStones_entail_wit_20 : mergingStones_entail_wit_20.
Axiom proof_of_mergingStones_entail_wit_21 : mergingStones_entail_wit_21.
Axiom proof_of_mergingStones_entail_wit_22 : mergingStones_entail_wit_22.
Axiom proof_of_mergingStones_entail_wit_23 : mergingStones_entail_wit_23.
Axiom proof_of_mergingStones_entail_wit_24 : mergingStones_entail_wit_24.
Axiom proof_of_mergingStones_entail_wit_25 : mergingStones_entail_wit_25.
Axiom proof_of_mergingStones_entail_wit_26 : mergingStones_entail_wit_26.
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

End VC_Correct.
