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
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function pqdk_sift_up -----*)

Definition pqdk_sift_up_safety_wit_1 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= child)) (PreH4 : (child < n_pre)) (PreH5 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pqdk_sift_up_safety_wit_2 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (((child - 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition pqdk_sift_up_safety_wit_3 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((child - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (child - 1 )) ”
.

Definition pqdk_sift_up_safety_wit_4 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_sift_up_safety_wit_5 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pqdk_sift_up_entail_wit_1 := 
(
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (PreH1 : (0 <= idx_pre)) (PreH2 : (idx_pre < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) ,
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity M n_pre idx_pre )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= idx_pre) ” 
  &&  “ (idx_pre < n_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre idx_pre ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (PreH1 : (0 <= idx_pre)) (PreH2 : (idx_pre < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) ,
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity M n_pre idx_pre )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= idx_pre) ” 
  &&  “ (idx_pre < n_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre idx_pre ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
).

Definition pqdk_sift_up_entail_wit_2 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values_2 )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values_2 )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= ((child - 1 ) ÷ 2 )) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < child) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < n_pre) ” 
  &&  “ (((child - 1 ) ÷ 2 ) = (heap_parent (child))) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  TT && emp 
|--
  “ (((child - 1 ) ÷ 2 ) = (heap_parent (child))) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < n_pre) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < child) ” 
  &&  “ (0 <= ((child - 1 ) ÷ 2 )) ”
  &&  emp
).

Definition pqdk_sift_up_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (((child - 1 ) ÷ 2 ) = (heap_parent (child)))
.

Definition pqdk_sift_up_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (((child - 1 ) ÷ 2 ) < n_pre)
.

Definition pqdk_sift_up_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (((child - 1 ) ÷ 2 ) < child)
.

Definition pqdk_sift_up_entail_wit_2_split_goal_4 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (0 <= ((child - 1 ) ÷ 2 ))
.

Definition pqdk_sift_up_entail_wit_3 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child )) ,
  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX (pos_values: (@list Z))  (data_values_2: (@list Z))  (key_values_2: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values_2 0) > (Znth child key_values_2 0)) ” 
  &&  “ ((Znth parent key_values 0) = (Znth parent key_values_2 0)) ” 
  &&  “ ((Znth parent data_values 0) = (Znth parent data_values_2 0)) ” 
  &&  “ (0 <= (Znth parent data_values_2 0)) ” 
  &&  “ ((Znth parent data_values_2 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values_2 0)) ” 
  &&  “ ((Znth child data_values_2 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values_2 data_values_2 pos_values data_bound_pre n_pre child ) ”
  &&  (IntArray.full key_pre n_pre key_values_2 )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values_2 )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child )) ,
  TT && emp 
|--
  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ”
  &&  emp
).

Definition pqdk_sift_up_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child )) ,
  ((Znth child data_values 0) < data_bound_pre)
.

Definition pqdk_sift_up_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child )) ,
  (0 <= (Znth child data_values 0))
.

Definition pqdk_sift_up_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child )) ,
  ((Znth parent data_values 0) < data_bound_pre)
.

Definition pqdk_sift_up_entail_wit_3_split_goal_4 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child )) ,
  (0 <= (Znth parent data_values 0))
.

Definition pqdk_sift_up_entail_wit_4 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 0) > (Znth child key_values_2 0))) (PreH10 : (tmp_key = (Znth parent key_values_2 0))) (PreH11 : (tmp_data = (Znth parent data_values_2 0))) (PreH12 : (0 <= (Znth parent data_values_2 0))) (PreH13 : ((Znth parent data_values_2 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values_2 0))) (PreH15 : ((Znth child data_values_2 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (IntArray.full data_pre n_pre (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) )
  **  (IntArray.full key_pre n_pre (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 0)) (key_values_2)))) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values_2 0)) (parent) ((replace_Znth ((Znth parent data_values_2 0)) (child) (pos_values_2)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  EX (pos_values: (@list Z))  (data_values: (@list Z))  (key_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (tmp_key = (Znth child key_values 0)) ” 
  &&  “ (tmp_data = (Znth child data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre parent ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 0) > (Znth child key_values_2 0))) (PreH10 : (tmp_key = (Znth parent key_values_2 0))) (PreH11 : (tmp_data = (Znth parent data_values_2 0))) (PreH12 : (0 <= (Znth parent data_values_2 0))) (PreH13 : ((Znth parent data_values_2 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values_2 0))) (PreH15 : ((Znth child data_values_2 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  TT && emp 
|--
  “ (SiftUpState M (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 0)) (key_values_2)))) (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) (replace_Znth ((Znth child data_values_2 0)) (parent) ((replace_Znth (tmp_data) (child) (pos_values_2)))) data_bound_pre n_pre parent ) ” 
  &&  “ ((Znth child (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) 0)) ” 
  &&  “ ((Znth parent (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth parent (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) 0)) ” 
  &&  “ (tmp_data = (Znth child (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) 0)) ” 
  &&  “ (tmp_key = (Znth child (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 0)) (key_values_2)))) 0)) ”
  &&  emp
).

Definition pqdk_sift_up_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 0) > (Znth child key_values_2 0))) (PreH10 : (tmp_key = (Znth parent key_values_2 0))) (PreH11 : (tmp_data = (Znth parent data_values_2 0))) (PreH12 : (0 <= (Znth parent data_values_2 0))) (PreH13 : ((Znth parent data_values_2 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values_2 0))) (PreH15 : ((Znth child data_values_2 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (SiftUpState M (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 0)) (key_values_2)))) (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) (replace_Znth ((Znth child data_values_2 0)) (parent) ((replace_Znth (tmp_data) (child) (pos_values_2)))) data_bound_pre n_pre parent )
.

Definition pqdk_sift_up_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 0) > (Znth child key_values_2 0))) (PreH10 : (tmp_key = (Znth parent key_values_2 0))) (PreH11 : (tmp_data = (Znth parent data_values_2 0))) (PreH12 : (0 <= (Znth parent data_values_2 0))) (PreH13 : ((Znth parent data_values_2 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values_2 0))) (PreH15 : ((Znth child data_values_2 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  ((Znth child (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) 0) < data_bound_pre)
.

Definition pqdk_sift_up_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 0) > (Znth child key_values_2 0))) (PreH10 : (tmp_key = (Znth parent key_values_2 0))) (PreH11 : (tmp_data = (Znth parent data_values_2 0))) (PreH12 : (0 <= (Znth parent data_values_2 0))) (PreH13 : ((Znth parent data_values_2 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values_2 0))) (PreH15 : ((Znth child data_values_2 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (0 <= (Znth child (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) 0))
.

Definition pqdk_sift_up_entail_wit_4_split_goal_4 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 0) > (Znth child key_values_2 0))) (PreH10 : (tmp_key = (Znth parent key_values_2 0))) (PreH11 : (tmp_data = (Znth parent data_values_2 0))) (PreH12 : (0 <= (Znth parent data_values_2 0))) (PreH13 : ((Znth parent data_values_2 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values_2 0))) (PreH15 : ((Znth child data_values_2 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  ((Znth parent (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) 0) < data_bound_pre)
.

Definition pqdk_sift_up_entail_wit_4_split_goal_5 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 0) > (Znth child key_values_2 0))) (PreH10 : (tmp_key = (Znth parent key_values_2 0))) (PreH11 : (tmp_data = (Znth parent data_values_2 0))) (PreH12 : (0 <= (Znth parent data_values_2 0))) (PreH13 : ((Znth parent data_values_2 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values_2 0))) (PreH15 : ((Znth child data_values_2 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (0 <= (Znth parent (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) 0))
.

Definition pqdk_sift_up_entail_wit_4_split_goal_6 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 0) > (Znth child key_values_2 0))) (PreH10 : (tmp_key = (Znth parent key_values_2 0))) (PreH11 : (tmp_data = (Znth parent data_values_2 0))) (PreH12 : (0 <= (Znth parent data_values_2 0))) (PreH13 : ((Znth parent data_values_2 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values_2 0))) (PreH15 : ((Znth child data_values_2 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (tmp_data = (Znth child (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 0)) (data_values_2)))) 0))
.

Definition pqdk_sift_up_entail_wit_4_split_goal_7 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 0) > (Znth child key_values_2 0))) (PreH10 : (tmp_key = (Znth parent key_values_2 0))) (PreH11 : (tmp_data = (Znth parent data_values_2 0))) (PreH12 : (0 <= (Znth parent data_values_2 0))) (PreH13 : ((Znth parent data_values_2 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values_2 0))) (PreH15 : ((Znth child data_values_2 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child )) ,
  (tmp_key = (Znth child (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 0)) (key_values_2)))) 0))
.

Definition pqdk_sift_up_entail_wit_5 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (tmp_key = (Znth child key_values_2 0))) (PreH10 : (tmp_data = (Znth child data_values_2 0))) (PreH11 : (0 <= (Znth parent data_values_2 0))) (PreH12 : ((Znth parent data_values_2 0) < data_bound_pre)) (PreH13 : (0 <= (Znth child data_values_2 0))) (PreH14 : ((Znth child data_values_2 0) < data_bound_pre)) (PreH15 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre parent )) ,
  (IntArray.full key_pre n_pre key_values_2 )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values_2 )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre parent ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_up_return_wit_1 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (PreH1 : (child <= 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (PreH1 : (child <= 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
).

Definition pqdk_sift_up_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (PreH1 : (child <= 0)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
.

Definition pqdk_sift_up_return_wit_2 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) <= (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) <= (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
).

Definition pqdk_sift_up_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) <= (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
.

Definition pqdk_sift_up_partial_solve_wit_1 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent key_values 0))
  **  (IntArray.missing_i key_pre parent 0 n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_up_partial_solve_wit_2 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |-> (Znth child key_values 0))
  **  (IntArray.missing_i key_pre child 0 n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_up_partial_solve_wit_3 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent key_values 0))
  **  (IntArray.missing_i key_pre parent 0 n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_up_partial_solve_wit_4 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child < n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent data_values 0))
  **  (IntArray.missing_i data_pre parent 0 n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_up_partial_solve_wit_5 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH10 : (tmp_key = (Znth parent key_values 0))) (PreH11 : (tmp_data = (Znth parent data_values 0))) (PreH12 : (0 <= (Znth parent data_values 0))) (PreH13 : ((Znth parent data_values 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values 0))) (PreH15 : ((Znth child data_values 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (tmp_key = (Znth parent key_values 0)) ” 
  &&  “ (tmp_data = (Znth parent data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent data_values 0))
  **  (IntArray.missing_i data_pre parent 0 n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_up_partial_solve_wit_6 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH10 : (tmp_key = (Znth parent key_values 0))) (PreH11 : (tmp_data = (Znth parent data_values 0))) (PreH12 : (0 <= (Znth parent data_values 0))) (PreH13 : ((Znth parent data_values 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values 0))) (PreH15 : ((Znth child data_values 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (tmp_key = (Znth parent key_values 0)) ” 
  &&  “ (tmp_data = (Znth parent data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((pos_pre + ((Znth parent data_values 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i pos_pre (Znth parent data_values 0) 0 data_bound_pre pos_values )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_up_partial_solve_wit_7 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH10 : (tmp_key = (Znth parent key_values 0))) (PreH11 : (tmp_data = (Znth parent data_values 0))) (PreH12 : (0 <= (Znth parent data_values 0))) (PreH13 : ((Znth parent data_values 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values 0))) (PreH15 : ((Znth child data_values 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth parent data_values 0)) (child) (pos_values)) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (tmp_key = (Znth parent key_values 0)) ” 
  &&  “ (tmp_data = (Znth parent data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int  |-> (Znth child data_values 0))
  **  (IntArray.missing_i data_pre child 0 n_pre data_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth parent data_values 0)) (child) (pos_values)) )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_up_partial_solve_wit_8 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH10 : (tmp_key = (Znth parent key_values 0))) (PreH11 : (tmp_data = (Znth parent data_values 0))) (PreH12 : (0 <= (Znth parent data_values 0))) (PreH13 : ((Znth parent data_values 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values 0))) (PreH15 : ((Znth child data_values 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth parent data_values 0)) (child) (pos_values)) )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (tmp_key = (Znth parent key_values 0)) ” 
  &&  “ (tmp_data = (Znth parent data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((pos_pre + ((Znth child data_values 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i pos_pre (Znth child data_values 0) 0 data_bound_pre (replace_Znth ((Znth parent data_values 0)) (child) (pos_values)) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_up_partial_solve_wit_9 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH10 : (tmp_key = (Znth parent key_values 0))) (PreH11 : (tmp_data = (Znth parent data_values 0))) (PreH12 : (0 <= (Znth parent data_values 0))) (PreH13 : ((Znth parent data_values 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values 0))) (PreH15 : ((Znth child data_values 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (tmp_key = (Znth parent key_values 0)) ” 
  &&  “ (tmp_data = (Znth parent data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |-> (Znth child key_values 0))
  **  (IntArray.missing_i key_pre child 0 n_pre key_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_up_partial_solve_wit_10 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH10 : (tmp_key = (Znth parent key_values 0))) (PreH11 : (tmp_data = (Znth parent data_values 0))) (PreH12 : (0 <= (Znth parent data_values 0))) (PreH13 : ((Znth parent data_values 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values 0))) (PreH15 : ((Znth child data_values 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (tmp_key = (Znth parent key_values 0)) ” 
  &&  “ (tmp_data = (Znth parent data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre parent 0 n_pre key_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_up_partial_solve_wit_11 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH10 : (tmp_key = (Znth parent key_values 0))) (PreH11 : (tmp_data = (Znth parent data_values 0))) (PreH12 : (0 <= (Znth parent data_values 0))) (PreH13 : ((Znth parent data_values 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values 0))) (PreH15 : ((Znth child data_values 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre (replace_Znth (parent) ((Znth child key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (tmp_key = (Znth parent key_values 0)) ” 
  &&  “ (tmp_data = (Znth parent data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int  |-> (Znth child data_values 0))
  **  (IntArray.missing_i data_pre child 0 n_pre data_values )
  **  (IntArray.full key_pre n_pre (replace_Znth (parent) ((Znth child key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_up_partial_solve_wit_12 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH10 : (tmp_key = (Znth parent key_values 0))) (PreH11 : (tmp_data = (Znth parent data_values 0))) (PreH12 : (0 <= (Znth parent data_values 0))) (PreH13 : ((Znth parent data_values 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values 0))) (PreH15 : ((Znth child data_values 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre (replace_Znth (parent) ((Znth child key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (tmp_key = (Znth parent key_values 0)) ” 
  &&  “ (tmp_data = (Znth parent data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre parent 0 n_pre data_values )
  **  (IntArray.full key_pre n_pre (replace_Znth (parent) ((Znth child key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_up_partial_solve_wit_13 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH10 : (tmp_key = (Znth parent key_values 0))) (PreH11 : (tmp_data = (Znth parent data_values 0))) (PreH12 : (0 <= (Znth parent data_values 0))) (PreH13 : ((Znth parent data_values 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values 0))) (PreH15 : ((Znth child data_values 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full data_pre n_pre (replace_Znth (parent) ((Znth child data_values 0)) (data_values)) )
  **  (IntArray.full key_pre n_pre (replace_Znth (parent) ((Znth child key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (tmp_key = (Znth parent key_values 0)) ” 
  &&  “ (tmp_data = (Znth parent data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre child 0 n_pre (replace_Znth (parent) ((Znth child key_values 0)) (key_values)) )
  **  (IntArray.full data_pre n_pre (replace_Znth (parent) ((Znth child data_values 0)) (data_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_up_partial_solve_wit_14 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child < n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values 0) > (Znth child key_values 0))) (PreH10 : (tmp_key = (Znth parent key_values 0))) (PreH11 : (tmp_data = (Znth parent data_values 0))) (PreH12 : (0 <= (Znth parent data_values 0))) (PreH13 : ((Znth parent data_values 0) < data_bound_pre)) (PreH14 : (0 <= (Znth child data_values 0))) (PreH15 : ((Znth child data_values 0) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child )) ,
  (IntArray.full key_pre n_pre (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values 0)) (key_values)))) )
  **  (IntArray.full data_pre n_pre (replace_Znth (parent) ((Znth child data_values 0)) (data_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent < n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_values 0) > (Znth child key_values 0)) ” 
  &&  “ (tmp_key = (Znth parent key_values 0)) ” 
  &&  “ (tmp_data = (Znth parent data_values 0)) ” 
  &&  “ (0 <= (Znth parent data_values 0)) ” 
  &&  “ ((Znth parent data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth child data_values 0)) ” 
  &&  “ ((Znth child data_values 0) < data_bound_pre) ” 
  &&  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child ) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre child 0 n_pre (replace_Znth (parent) ((Znth child data_values 0)) (data_values)) )
  **  (IntArray.full key_pre n_pre (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values 0)) (key_values)))) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values 0)) (parent) ((replace_Znth ((Znth parent data_values 0)) (child) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

(*----- Function pqdk_sift_down -----*)

Definition pqdk_sift_down_safety_wit_1 := 
(
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (((current * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((current * 2 ) + 1 )) ”
) \/
(
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (((current * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((current * 2 ) + 1 )) ”
).

Definition pqdk_sift_down_safety_wit_1_split_goal_1 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (((current * 2 ) + 1 ) <= INT_MAX) ”
.

Definition pqdk_sift_down_safety_wit_1_split_goal_2 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((INT_MIN) <= ((current * 2 ) + 1 )) ”
.

Definition pqdk_sift_down_safety_wit_2 := 
(
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((current * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (current * 2 )) ”
) \/
(
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((current * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (current * 2 )) ”
).

Definition pqdk_sift_down_safety_wit_2_split_goal_1 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((current * 2 ) <= INT_MAX) ”
.

Definition pqdk_sift_down_safety_wit_2_split_goal_2 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((INT_MIN) <= (current * 2 )) ”
.

Definition pqdk_sift_down_safety_wit_3 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pqdk_sift_down_safety_wit_4 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_sift_down_safety_wit_5 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (((current * 2 ) + 1 ) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (((current * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((current * 2 ) + 1 )) ”
.

Definition pqdk_sift_down_safety_wit_6 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (((current * 2 ) + 1 ) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((current * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (current * 2 )) ”
.

Definition pqdk_sift_down_safety_wit_7 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (((current * 2 ) + 1 ) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pqdk_sift_down_safety_wit_8 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (((current * 2 ) + 1 ) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_sift_down_safety_wit_9 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (((current * 2 ) + 1 ) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> ((current * 2 ) + 1 ))
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((((current * 2 ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((current * 2 ) + 1 ) + 1 )) ”
.

Definition pqdk_sift_down_safety_wit_10 := 
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (((current * 2 ) + 1 ) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> ((current * 2 ) + 1 ))
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx_pre)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_sift_down_entail_wit_1 := 
(
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (PreH1 : (0 <= idx_pre)) (PreH2 : (idx_pre < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) ,
  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity M n_pre idx_pre )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= idx_pre) ” 
  &&  “ (idx_pre < n_pre) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre idx_pre ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (idx_pre: Z) (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (PreH1 : (0 <= idx_pre)) (PreH2 : (idx_pre < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) ,
  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity M n_pre idx_pre )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= idx_pre) ” 
  &&  “ (idx_pre < n_pre) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre idx_pre ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
).

Definition pqdk_sift_down_entail_wit_2 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (PreH1 : (((current * 2 ) + 1 ) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values_2 )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values_2 )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (((current * 2 ) + 1 ) = ((current * 2 ) + 1 )) ” 
  &&  “ ((((current * 2 ) + 1 ) + 1 ) = (((current * 2 ) + 1 ) + 1 )) ” 
  &&  “ (((current * 2 ) + 1 ) = ((current * 2 ) + 1 )) ” 
  &&  “ (0 <= ((current * 2 ) + 1 )) ” 
  &&  “ (((current * 2 ) + 1 ) < n_pre) ” 
  &&  “ (0 <= (((current * 2 ) + 1 ) + 1 )) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_down_entail_wit_3_1 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth right key_values_2 0) < (Znth left key_values_2 0))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (smallest = left)) (PreH10 : (0 <= left)) (PreH11 : (left < n_pre)) (PreH12 : (0 <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values_2 )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values_2 )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX (data_values: (@list Z))  (pos_values: (@list Z))  (key_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < n_pre) ” 
  &&  “ (SelectedChild key_values n_pre current right ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth right key_values_2 0) < (Znth left key_values_2 0))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (smallest = left)) (PreH10 : (0 <= left)) (PreH11 : (left < n_pre)) (PreH12 : (0 <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  TT && emp 
|--
  “ (SelectedChild key_values_2 n_pre current (left + 1 ) ) ”
  &&  emp
).

Definition pqdk_sift_down_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth right key_values_2 0) < (Znth left key_values_2 0))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (smallest = left)) (PreH10 : (0 <= left)) (PreH11 : (left < n_pre)) (PreH12 : (0 <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (SelectedChild key_values_2 n_pre current (left + 1 ) )
.

Definition pqdk_sift_down_entail_wit_3_2 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (right >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (smallest = left)) (PreH9 : (0 <= left)) (PreH10 : (left < n_pre)) (PreH11 : (0 <= right)) (PreH12 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values_2 )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values_2 )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX (data_values: (@list Z))  (pos_values: (@list Z))  (key_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (right >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (smallest = left)) (PreH9 : (0 <= left)) (PreH10 : (left < n_pre)) (PreH11 : (0 <= right)) (PreH12 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  TT && emp 
|--
  “ (SelectedChild key_values_2 n_pre current left ) ”
  &&  emp
).

Definition pqdk_sift_down_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (right >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (smallest = left)) (PreH9 : (0 <= left)) (PreH10 : (left < n_pre)) (PreH11 : (0 <= right)) (PreH12 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (SelectedChild key_values_2 n_pre current left )
.

Definition pqdk_sift_down_entail_wit_3_3 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth right key_values_2 0) >= (Znth left key_values_2 0))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (smallest = left)) (PreH10 : (0 <= left)) (PreH11 : (left < n_pre)) (PreH12 : (0 <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values_2 )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values_2 )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX (data_values: (@list Z))  (pos_values: (@list Z))  (key_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth right key_values_2 0) >= (Znth left key_values_2 0))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (smallest = left)) (PreH10 : (0 <= left)) (PreH11 : (left < n_pre)) (PreH12 : (0 <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  TT && emp 
|--
  “ (SelectedChild key_values_2 n_pre current left ) ”
  &&  emp
).

Definition pqdk_sift_down_entail_wit_3_3_split_goal_1 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth right key_values_2 0) >= (Znth left key_values_2 0))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (smallest = left)) (PreH10 : (0 <= left)) (PreH11 : (left < n_pre)) (PreH12 : (0 <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (SelectedChild key_values_2 n_pre current left )
.

Definition pqdk_sift_down_entail_wit_4 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX (pos_values: (@list Z))  (data_values_2: (@list Z))  (key_values_2: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values_2 0) > (Znth smallest key_values_2 0)) ” 
  &&  “ ((Znth current key_values 0) = (Znth current key_values_2 0)) ” 
  &&  “ ((Znth current data_values 0) = (Znth current data_values_2 0)) ” 
  &&  “ (0 <= (Znth current data_values_2 0)) ” 
  &&  “ ((Znth current data_values_2 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values_2 0)) ” 
  &&  “ ((Znth smallest data_values_2 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values_2 n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values_2 data_values_2 pos_values data_bound_pre n_pre current ) ”
  &&  (IntArray.full key_pre n_pre key_values_2 )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values_2 )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  TT && emp 
|--
  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ (current < smallest) ” 
  &&  “ (((current * 2 ) + 1 ) < n_pre) ”
  &&  emp
).

Definition pqdk_sift_down_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  ((Znth smallest data_values 0) < data_bound_pre)
.

Definition pqdk_sift_down_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  (0 <= (Znth smallest data_values 0))
.

Definition pqdk_sift_down_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  ((Znth current data_values 0) < data_bound_pre)
.

Definition pqdk_sift_down_entail_wit_4_split_goal_4 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  (0 <= (Znth current data_values 0))
.

Definition pqdk_sift_down_entail_wit_4_split_goal_5 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  (current < smallest)
.

Definition pqdk_sift_down_entail_wit_4_split_goal_6 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current )) ,
  (((current * 2 ) + 1 ) < n_pre)
.

Definition pqdk_sift_down_entail_wit_5 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 0) > (Znth smallest key_values_2 0))) (PreH14 : (tmp_key = (Znth current key_values_2 0))) (PreH15 : (tmp_data = (Znth current data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (IntArray.full data_pre n_pre (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) )
  **  (IntArray.full key_pre n_pre (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 0)) (key_values_2)))) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values_2 0)) (current) ((replace_Znth ((Znth current data_values_2 0)) (smallest) (pos_values_2)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  EX (pos_values: (@list Z))  (data_values: (@list Z))  (key_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ (tmp_key > (Znth current key_values 0)) ” 
  &&  “ (tmp_key = (Znth smallest key_values 0)) ” 
  &&  “ (tmp_data = (Znth smallest data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre smallest ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 0) > (Znth smallest key_values_2 0))) (PreH14 : (tmp_key = (Znth current key_values_2 0))) (PreH15 : (tmp_data = (Znth current data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  TT && emp 
|--
  “ (SiftDownState M (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 0)) (key_values_2)))) (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) (replace_Znth ((Znth smallest data_values_2 0)) (current) ((replace_Znth (tmp_data) (smallest) (pos_values_2)))) data_bound_pre n_pre smallest ) ” 
  &&  “ ((Znth smallest (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) 0)) ” 
  &&  “ ((Znth current (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth current (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) 0)) ” 
  &&  “ (tmp_data = (Znth smallest (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) 0)) ” 
  &&  “ (tmp_key = (Znth smallest (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 0)) (key_values_2)))) 0)) ” 
  &&  “ (tmp_key > (Znth current (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 0)) (key_values_2)))) 0)) ”
  &&  emp
).

Definition pqdk_sift_down_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 0) > (Znth smallest key_values_2 0))) (PreH14 : (tmp_key = (Znth current key_values_2 0))) (PreH15 : (tmp_data = (Znth current data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (SiftDownState M (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 0)) (key_values_2)))) (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) (replace_Znth ((Znth smallest data_values_2 0)) (current) ((replace_Znth (tmp_data) (smallest) (pos_values_2)))) data_bound_pre n_pre smallest )
.

Definition pqdk_sift_down_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 0) > (Znth smallest key_values_2 0))) (PreH14 : (tmp_key = (Znth current key_values_2 0))) (PreH15 : (tmp_data = (Znth current data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  ((Znth smallest (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) 0) < data_bound_pre)
.

Definition pqdk_sift_down_entail_wit_5_split_goal_3 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 0) > (Znth smallest key_values_2 0))) (PreH14 : (tmp_key = (Znth current key_values_2 0))) (PreH15 : (tmp_data = (Znth current data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (0 <= (Znth smallest (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) 0))
.

Definition pqdk_sift_down_entail_wit_5_split_goal_4 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 0) > (Znth smallest key_values_2 0))) (PreH14 : (tmp_key = (Znth current key_values_2 0))) (PreH15 : (tmp_data = (Znth current data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  ((Znth current (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) 0) < data_bound_pre)
.

Definition pqdk_sift_down_entail_wit_5_split_goal_5 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 0) > (Znth smallest key_values_2 0))) (PreH14 : (tmp_key = (Znth current key_values_2 0))) (PreH15 : (tmp_data = (Znth current data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (0 <= (Znth current (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) 0))
.

Definition pqdk_sift_down_entail_wit_5_split_goal_6 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 0) > (Znth smallest key_values_2 0))) (PreH14 : (tmp_key = (Znth current key_values_2 0))) (PreH15 : (tmp_data = (Znth current data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (tmp_data = (Znth smallest (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 0)) (data_values_2)))) 0))
.

Definition pqdk_sift_down_entail_wit_5_split_goal_7 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 0) > (Znth smallest key_values_2 0))) (PreH14 : (tmp_key = (Znth current key_values_2 0))) (PreH15 : (tmp_data = (Znth current data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (tmp_key = (Znth smallest (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 0)) (key_values_2)))) 0))
.

Definition pqdk_sift_down_entail_wit_5_split_goal_8 := 
forall (n_pre: Z) (data_bound_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 0) > (Znth smallest key_values_2 0))) (PreH14 : (tmp_key = (Znth current key_values_2 0))) (PreH15 : (tmp_data = (Znth current data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest )) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current )) ,
  (tmp_key > (Znth current (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 0)) (key_values_2)))) 0))
.

Definition pqdk_sift_down_entail_wit_6 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : (tmp_key > (Znth current key_values_2 0))) (PreH14 : (tmp_key = (Znth smallest key_values_2 0))) (PreH15 : (tmp_data = (Znth smallest data_values_2 0))) (PreH16 : (0 <= (Znth current data_values_2 0))) (PreH17 : ((Znth current data_values_2 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values_2 0))) (PreH19 : ((Znth smallest data_values_2 0) < data_bound_pre)) (PreH20 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre smallest )) ,
  (IntArray.full key_pre n_pre key_values_2 )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values_2 )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre smallest ) ”
  &&  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_down_return_wit_1 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (((current * 2 ) + 1 ) >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (((current * 2 ) + 1 ) >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
).

Definition pqdk_sift_down_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (PreH1 : (((current * 2 ) + 1 ) >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
.

Definition pqdk_sift_down_return_wit_2 := 
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) <= (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
) \/
(
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) <= (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
).

Definition pqdk_sift_down_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) <= (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre )
.

Definition pqdk_sift_down_partial_solve_wit_1 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (right < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (smallest = left)) (PreH9 : (0 <= left)) (PreH10 : (left < n_pre)) (PreH11 : (0 <= right)) (PreH12 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (right < n_pre) ” 
  &&  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (smallest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((key_pre + (right * sizeof(INT)))) # Int  |-> (Znth right key_values 0))
  **  (IntArray.missing_i key_pre right 0 n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_down_partial_solve_wit_2 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (right < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (smallest = left)) (PreH9 : (0 <= left)) (PreH10 : (left < n_pre)) (PreH11 : (0 <= right)) (PreH12 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (right < n_pre) ” 
  &&  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (smallest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((key_pre + (left * sizeof(INT)))) # Int  |-> (Znth left key_values 0))
  **  (IntArray.missing_i key_pre left 0 n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_down_partial_solve_wit_3 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= smallest)) (PreH8 : (smallest < n_pre)) (PreH9 : (SelectedChild key_values n_pre current smallest )) (PreH10 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((key_pre + (current * sizeof(INT)))) # Int  |-> (Znth current key_values 0))
  **  (IntArray.missing_i key_pre current 0 n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_down_partial_solve_wit_4 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= smallest)) (PreH8 : (smallest < n_pre)) (PreH9 : (SelectedChild key_values n_pre current smallest )) (PreH10 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int  |-> (Znth smallest key_values 0))
  **  (IntArray.missing_i key_pre smallest 0 n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_down_partial_solve_wit_5 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((key_pre + (current * sizeof(INT)))) # Int  |-> (Znth current key_values 0))
  **  (IntArray.missing_i key_pre current 0 n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_down_partial_solve_wit_6 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2 ) + 1 ))) (PreH7 : (right = (left + 1 ))) (PreH8 : (0 <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest )) (PreH11 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((data_pre + (current * sizeof(INT)))) # Int  |-> (Znth current data_values 0))
  **  (IntArray.missing_i data_pre current 0 n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_down_partial_solve_wit_7 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH14 : (tmp_key = (Znth current key_values 0))) (PreH15 : (tmp_data = (Znth current data_values 0))) (PreH16 : (0 <= (Znth current data_values 0))) (PreH17 : ((Znth current data_values 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values 0))) (PreH19 : ((Znth smallest data_values 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest )) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (tmp_key = (Znth current key_values 0)) ” 
  &&  “ (tmp_data = (Znth current data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((data_pre + (current * sizeof(INT)))) # Int  |-> (Znth current data_values 0))
  **  (IntArray.missing_i data_pre current 0 n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_sift_down_partial_solve_wit_8 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH14 : (tmp_key = (Znth current key_values 0))) (PreH15 : (tmp_data = (Znth current data_values 0))) (PreH16 : (0 <= (Znth current data_values 0))) (PreH17 : ((Znth current data_values 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values 0))) (PreH19 : ((Znth smallest data_values 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest )) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (tmp_key = (Znth current key_values 0)) ” 
  &&  “ (tmp_data = (Znth current data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((pos_pre + ((Znth current data_values 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i pos_pre (Znth current data_values 0) 0 data_bound_pre pos_values )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_down_partial_solve_wit_9 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH14 : (tmp_key = (Znth current key_values 0))) (PreH15 : (tmp_data = (Znth current data_values 0))) (PreH16 : (0 <= (Znth current data_values 0))) (PreH17 : ((Znth current data_values 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values 0))) (PreH19 : ((Znth smallest data_values 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest )) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (tmp_key = (Znth current key_values 0)) ” 
  &&  “ (tmp_data = (Znth current data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((data_pre + (smallest * sizeof(INT)))) # Int  |-> (Znth smallest data_values 0))
  **  (IntArray.missing_i data_pre smallest 0 n_pre data_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)) )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_down_partial_solve_wit_10 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH14 : (tmp_key = (Znth current key_values 0))) (PreH15 : (tmp_data = (Znth current data_values 0))) (PreH16 : (0 <= (Znth current data_values 0))) (PreH17 : ((Znth current data_values 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values 0))) (PreH19 : ((Znth smallest data_values 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest )) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)) )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (tmp_key = (Znth current key_values 0)) ” 
  &&  “ (tmp_data = (Znth current data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((pos_pre + ((Znth smallest data_values 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i pos_pre (Znth smallest data_values 0) 0 data_bound_pre (replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_down_partial_solve_wit_11 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH14 : (tmp_key = (Znth current key_values 0))) (PreH15 : (tmp_data = (Znth current data_values 0))) (PreH16 : (0 <= (Znth current data_values 0))) (PreH17 : ((Znth current data_values 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values 0))) (PreH19 : ((Znth smallest data_values 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest )) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (tmp_key = (Znth current key_values 0)) ” 
  &&  “ (tmp_data = (Znth current data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int  |-> (Znth smallest key_values 0))
  **  (IntArray.missing_i key_pre smallest 0 n_pre key_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_down_partial_solve_wit_12 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH14 : (tmp_key = (Znth current key_values 0))) (PreH15 : (tmp_data = (Znth current data_values 0))) (PreH16 : (0 <= (Znth current data_values 0))) (PreH17 : ((Znth current data_values 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values 0))) (PreH19 : ((Znth smallest data_values 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest )) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre key_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (tmp_key = (Znth current key_values 0)) ” 
  &&  “ (tmp_data = (Znth current data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((key_pre + (current * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre current 0 n_pre key_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_down_partial_solve_wit_13 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH14 : (tmp_key = (Znth current key_values 0))) (PreH15 : (tmp_data = (Znth current data_values 0))) (PreH16 : (0 <= (Znth current data_values 0))) (PreH17 : ((Znth current data_values 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values 0))) (PreH19 : ((Znth smallest data_values 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest )) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre (replace_Znth (current) ((Znth smallest key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (tmp_key = (Znth current key_values 0)) ” 
  &&  “ (tmp_data = (Znth current data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((data_pre + (smallest * sizeof(INT)))) # Int  |-> (Znth smallest data_values 0))
  **  (IntArray.missing_i data_pre smallest 0 n_pre data_values )
  **  (IntArray.full key_pre n_pre (replace_Znth (current) ((Znth smallest key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_down_partial_solve_wit_14 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH14 : (tmp_key = (Znth current key_values 0))) (PreH15 : (tmp_data = (Znth current data_values 0))) (PreH16 : (0 <= (Znth current data_values 0))) (PreH17 : ((Znth current data_values 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values 0))) (PreH19 : ((Znth smallest data_values 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest )) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full data_pre n_pre data_values )
  **  (IntArray.full key_pre n_pre (replace_Znth (current) ((Znth smallest key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (tmp_key = (Znth current key_values 0)) ” 
  &&  “ (tmp_data = (Znth current data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((data_pre + (current * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre current 0 n_pre data_values )
  **  (IntArray.full key_pre n_pre (replace_Znth (current) ((Znth smallest key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_down_partial_solve_wit_15 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH14 : (tmp_key = (Znth current key_values 0))) (PreH15 : (tmp_data = (Znth current data_values 0))) (PreH16 : (0 <= (Znth current data_values 0))) (PreH17 : ((Znth current data_values 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values 0))) (PreH19 : ((Znth smallest data_values 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest )) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full data_pre n_pre (replace_Znth (current) ((Znth smallest data_values 0)) (data_values)) )
  **  (IntArray.full key_pre n_pre (replace_Znth (current) ((Znth smallest key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (tmp_key = (Znth current key_values 0)) ” 
  &&  “ (tmp_data = (Znth current data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre smallest 0 n_pre (replace_Znth (current) ((Znth smallest key_values 0)) (key_values)) )
  **  (IntArray.full data_pre n_pre (replace_Znth (current) ((Znth smallest data_values 0)) (data_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

Definition pqdk_sift_down_partial_solve_wit_16 := 
forall (n_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (M: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (current: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : (0 <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2 ) + 1 ))) (PreH6 : (right = (left + 1 ))) (PreH7 : (0 <= left)) (PreH8 : (left < n_pre)) (PreH9 : (0 <= right)) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values 0) > (Znth smallest key_values 0))) (PreH14 : (tmp_key = (Znth current key_values 0))) (PreH15 : (tmp_data = (Znth current data_values 0))) (PreH16 : (0 <= (Znth current data_values 0))) (PreH17 : ((Znth current data_values 0) < data_bound_pre)) (PreH18 : (0 <= (Znth smallest data_values 0))) (PreH19 : ((Znth smallest data_values 0) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest )) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current )) ,
  (IntArray.full key_pre n_pre (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values 0)) (key_values)))) )
  **  (IntArray.full data_pre n_pre (replace_Znth (current) ((Znth smallest data_values 0)) (data_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
|--
  “ (n_pre <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= current) ” 
  &&  “ (current < n_pre) ” 
  &&  “ (left = ((current * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < n_pre) ” 
  &&  “ (0 <= right) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < n_pre) ” 
  &&  “ (current < smallest) ” 
  &&  “ ((Znth current key_values 0) > (Znth smallest key_values 0)) ” 
  &&  “ (tmp_key = (Znth current key_values 0)) ” 
  &&  “ (tmp_data = (Znth current data_values 0)) ” 
  &&  “ (0 <= (Znth current data_values 0)) ” 
  &&  “ ((Znth current data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth smallest data_values 0)) ” 
  &&  “ ((Znth smallest data_values 0) < data_bound_pre) ” 
  &&  “ (SelectedChild key_values n_pre current smallest ) ” 
  &&  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current ) ”
  &&  (((data_pre + (smallest * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre smallest 0 n_pre (replace_Znth (current) ((Znth smallest data_values 0)) (data_values)) )
  **  (IntArray.full key_pre n_pre (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values 0)) (key_values)))) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values 0)) (current) ((replace_Znth ((Znth current data_values 0)) (smallest) (pos_values)))) )
  **  (IntArray.undef_seg key_pre n_pre capacity )
  **  (IntArray.undef_seg data_pre n_pre capacity )
.

(*----- Function pqdk_push -----*)

Definition pqdk_push_safety_wit_1 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)) )
  **  (IntArray.full data_pre (n + 1 ) (app (data_values) ((cons (data_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full key_pre (n + 1 ) (app (key_values) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((size_pre) # Int  |-> n)
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)) )
  **  (IntArray.full data_pre (n + 1 ) (app (data_values) ((cons (data_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full key_pre (n + 1 ) (app (key_values) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((size_pre) # Int  |-> n)
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
).

Definition pqdk_push_safety_wit_1_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)) )
  **  (IntArray.full data_pre (n + 1 ) (app (data_values) ((cons (data_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full key_pre (n + 1 ) (app (key_values) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((size_pre) # Int  |-> n)
|--
  “ ((n + 1 ) <= INT_MAX) ”
.

Definition pqdk_push_safety_wit_1_split_goal_2 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)) )
  **  (IntArray.full data_pre (n + 1 ) (app (data_values) ((cons (data_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full key_pre (n + 1 ) (app (key_values) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((size_pre) # Int  |-> n)
|--
  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition pqdk_push_safety_wit_2 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)) )
  **  (IntArray.full data_pre (n + 1 ) (app (data_values) ((cons (data_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full key_pre (n + 1 ) (app (key_values) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((size_pre) # Int  |-> n)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_push_safety_wit_3 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((size_pre) # Int  |-> (n + 1 ))
  **  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) n )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition pqdk_push_safety_wit_4 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((size_pre) # Int  |-> (n + 1 ))
  **  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_push_entail_wit_1 := 
(
forall (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) ,
  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_absent M_before data_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_absent M_before data_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
).

Definition pqdk_push_entail_wit_2 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values_2)) )
  **  (IntArray.full data_pre (n + 1 ) (app (data_values_2) ((cons (data_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full key_pre (n + 1 ) (app (key_values_2) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((size_pre) # Int  |-> (n + 1 ))
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (PushWriteState M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre ) ”
  &&  ((size_pre) # Int  |-> (n + 1 ))
  **  (IntArray.full key_pre (n + 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  (IntArray.full data_pre (n + 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n )) ,
  TT && emp 
|--
  “ (PushWriteState M_before (app (key_values_2) ((cons (key_x_pre) ((@nil Z))))) (app (data_values_2) ((cons (data_x_pre) ((@nil Z))))) (replace_Znth (data_x_pre) (n) (pos_values_2)) data_bound_pre n data_x_pre key_x_pre ) ”
  &&  emp
).

Definition pqdk_push_entail_wit_2_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n )) ,
  (PushWriteState M_before (app (key_values_2) ((cons (key_x_pre) ((@nil Z))))) (app (data_values_2) ((cons (data_x_pre) ((@nil Z))))) (replace_Znth (data_x_pre) (n) (pos_values_2)) data_bound_pre n data_x_pre key_x_pre )
.

Definition pqdk_push_entail_wit_3 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (PushWriteState M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre )) ,
  ((size_pre) # Int  |-> (n + 1 ))
  **  (IntArray.full key_pre (n + 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  (IntArray.full data_pre (n + 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ”
  &&  ((size_pre) # Int  |-> (n + 1 ))
  **  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) n )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (PushWriteState M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n + 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  (IntArray.full data_pre (n + 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) n )
).

Definition pqdk_push_entail_wit_3_split_goal_spatial := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (PushWriteState M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n + 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  (IntArray.full data_pre (n + 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) n )
.

Definition pqdk_push_return_wit_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) )
  **  ((size_pre) # Int  |-> (n + 1 ))
|--
  ((size_pre) # Int  |-> (n + 1 ))
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) )
.

Definition pqdk_push_partial_solve_wit_1 := 
forall (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_absent M_before data_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (((key_pre + (n * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_push_partial_solve_wit_2 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full key_pre (n + 1 ) (app (key_values) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_absent M_before data_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (((data_pre + (n * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full key_pre (n + 1 ) (app (key_values) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_push_partial_solve_wit_3 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full data_pre (n + 1 ) (app (data_values) ((cons (data_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full key_pre (n + 1 ) (app (key_values) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_absent M_before data_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (((pos_pre + (data_x_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i pos_pre data_x_pre 0 data_bound_pre pos_values )
  **  (IntArray.full data_pre (n + 1 ) (app (data_values) ((cons (data_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg data_pre (n + 1 ) capacity )
  **  (IntArray.full key_pre (n + 1 ) (app (key_values) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n + 1 ) capacity )
  **  ((size_pre) # Int  |-> n)
.

Definition pqdk_push_partial_solve_wit_4_pure := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((size_pre) # Int  |-> (n + 1 ))
  **  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) n )
|--
  “ (0 <= n) ” 
  &&  “ (n < (n + 1 )) ” 
  &&  “ ((n + 1 ) <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ”
.

Definition pqdk_push_partial_solve_wit_4_aux := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  ((size_pre) # Int  |-> (n + 1 ))
  **  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) n )
|--
  “ (0 <= n) ” 
  &&  “ (n < (n + 1 )) ” 
  &&  “ ((n + 1 ) <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ”
  &&  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) n )
  **  ((size_pre) # Int  |-> (n + 1 ))
.

Definition pqdk_push_partial_solve_wit_4 := pqdk_push_partial_solve_wit_4_pure -> pqdk_push_partial_solve_wit_4_aux.

(*----- Function pqdk_decrease_key -----*)

Definition pqdk_decrease_key_entail_wit_1 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) ,
  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
).

Definition pqdk_decrease_key_entail_wit_2 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values_2 )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values_2 )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values_2: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= (Znth data_x_pre pos_values 0)) ” 
  &&  “ ((Znth data_x_pre pos_values 0) < n) ” 
  &&  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ” 
  &&  “ (heap_index_of M_before data_values pos_values_2 data_x_pre (Znth data_x_pre pos_values 0) ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values_2 data_bound_pre n ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n )) ,
  TT && emp 
|--
  “ (heap_index_of M_before data_values_2 pos_values data_x_pre (Znth data_x_pre pos_values 0) ) ” 
  &&  “ ((Znth data_x_pre pos_values 0) < n) ” 
  &&  “ (0 <= (Znth data_x_pre pos_values 0)) ”
  &&  emp
).

Definition pqdk_decrease_key_entail_wit_2_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n )) ,
  (heap_index_of M_before data_values_2 pos_values data_x_pre (Znth data_x_pre pos_values 0) )
.

Definition pqdk_decrease_key_entail_wit_2_split_goal_2 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n )) ,
  ((Znth data_x_pre pos_values 0) < n)
.

Definition pqdk_decrease_key_entail_wit_2_split_goal_3 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n )) ,
  (0 <= (Znth data_x_pre pos_values 0))
.

Definition pqdk_decrease_key_entail_wit_3 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_index_of M_before data_values_2 pos_values_2 data_x_pre idx )) (PreH8 : (heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n )) ,
  (IntArray.full key_pre n (replace_Znth (idx) (key_x_pre) (key_values_2)) )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values_2 )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < n) ” 
  &&  “ (DecreaseKeyWriteState M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre idx ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_index_of M_before data_values_2 pos_values_2 data_x_pre idx )) (PreH8 : (heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n )) ,
  TT && emp 
|--
  “ (DecreaseKeyWriteState M_before (replace_Znth (idx) (key_x_pre) (key_values_2)) data_values_2 pos_values_2 data_bound_pre n data_x_pre key_x_pre idx ) ”
  &&  emp
).

Definition pqdk_decrease_key_entail_wit_3_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_index_of M_before data_values_2 pos_values_2 data_x_pre idx )) (PreH8 : (heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n )) ,
  (DecreaseKeyWriteState M_before (replace_Znth (idx) (key_x_pre) (key_values_2)) data_values_2 pos_values_2 data_bound_pre n data_x_pre key_x_pre idx )
.

Definition pqdk_decrease_key_entail_wit_4 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (DecreaseKeyWriteState M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre idx )) ,
  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (0 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < n) ”
  &&  ((size_pre) # Int  |-> n)
  **  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (DecreaseKeyWriteState M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre idx )) ,
  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx )
).

Definition pqdk_decrease_key_entail_wit_4_split_goal_spatial := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (DecreaseKeyWriteState M_before key_values data_values pos_values data_bound_pre n data_x_pre key_x_pre idx )) ,
  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx )
.

Definition pqdk_decrease_key_return_wit_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n )
  **  ((size_pre) # Int  |-> n)
|--
  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n )
.

Definition pqdk_decrease_key_partial_solve_wit_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (0 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (((pos_pre + (data_x_pre * sizeof(INT)))) # Int  |-> (Znth data_x_pre pos_values 0))
  **  (IntArray.missing_i pos_pre data_x_pre 0 data_bound_pre pos_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
.

Definition pqdk_decrease_key_partial_solve_wit_2 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_index_of M_before data_values pos_values data_x_pre idx )) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (0 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < n) ” 
  &&  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ” 
  &&  “ (heap_index_of M_before data_values pos_values data_x_pre idx ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (((key_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre idx 0 n key_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
.

Definition pqdk_decrease_key_partial_solve_wit_3_pure := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((size_pre) # Int  |-> n)
  **  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx )
|--
  “ (0 <= idx) ” 
  &&  “ (idx < n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ”
.

Definition pqdk_decrease_key_partial_solve_wit_3_aux := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) ,
  ((size_pre) # Int  |-> n)
  **  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx )
|--
  “ (0 <= idx) ” 
  &&  “ (idx < n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < n) ”
  &&  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx )
  **  ((size_pre) # Int  |-> n)
.

Definition pqdk_decrease_key_partial_solve_wit_3 := pqdk_decrease_key_partial_solve_wit_3_pure -> pqdk_decrease_key_partial_solve_wit_3_aux.

(*----- Function pqdk_update_or_push -----*)

Definition pqdk_update_or_push_safety_wit_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((( &( "idx" ) )) # Int  |-> (Znth data_x_pre pos_values 0))
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pqdk_update_or_push_entail_wit_1 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) ,
  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_update_or_add_pre M_before data_x_pre key_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_update_or_add_pre M_before data_x_pre key_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
).

Definition pqdk_update_or_push_entail_wit_2 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : ((Znth data_x_pre pos_values 0) < 0)) (PreH2 : (0 <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_absent M_before data_x_pre ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : ((Znth data_x_pre pos_values 0) < 0)) (PreH2 : (0 <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre pos_values )
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  “ (partial_map_absent M_before data_x_pre ) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
).

Definition pqdk_update_or_push_entail_wit_2_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : ((Znth data_x_pre pos_values 0) < 0)) (PreH2 : (0 <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre pos_values )
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  “ (partial_map_absent M_before data_x_pre ) ”
.

Definition pqdk_update_or_push_entail_wit_2_split_goal_spatial := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : ((Znth data_x_pre pos_values 0) < 0)) (PreH2 : (0 <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre pos_values )
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
.

Definition pqdk_update_or_push_entail_wit_3 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : ((Znth data_x_pre pos_values 0) >= 0)) (PreH2 : (0 <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : ((Znth data_x_pre pos_values 0) >= 0)) (PreH2 : (0 <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre pos_values )
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
).

Definition pqdk_update_or_push_entail_wit_3_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : ((Znth data_x_pre pos_values 0) >= 0)) (PreH2 : (0 <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre pos_values )
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ”
.

Definition pqdk_update_or_push_entail_wit_3_split_goal_spatial := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : ((Znth data_x_pre pos_values 0) >= 0)) (PreH2 : (0 <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (0 <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre pos_values )
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
.

Definition pqdk_update_or_push_entail_wit_4_1 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) ,
  ((size_pre) # Int  |-> (n + 1 ))
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) )
|--
  EX (n_after: Z) ,
  “ (partial_map_update_or_add_size M_before n n_after data_x_pre key_x_pre ) ”
  &&  ((size_pre) # Int  |-> n_after)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n_after )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) )
|--
  “ (partial_map_update_or_add_size M_before n (n + 1 ) data_x_pre key_x_pre ) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) )
).

Definition pqdk_update_or_push_entail_wit_4_1_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) )
|--
  “ (partial_map_update_or_add_size M_before n (n + 1 ) data_x_pre key_x_pre ) ”
.

Definition pqdk_update_or_push_entail_wit_4_1_split_goal_spatial := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) (n + 1 ) )
.

Definition pqdk_update_or_push_entail_wit_4_2 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) ,
  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n )
|--
  EX (n_after: Z) ,
  “ (partial_map_update_or_add_size M_before n n_after data_x_pre key_x_pre ) ”
  &&  ((size_pre) # Int  |-> n_after)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n_after )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n )
|--
  “ (partial_map_update_or_add_size M_before n n data_x_pre key_x_pre ) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n )
).

Definition pqdk_update_or_push_entail_wit_4_2_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n )
|--
  “ (partial_map_update_or_add_size M_before n n data_x_pre key_x_pre ) ”
.

Definition pqdk_update_or_push_entail_wit_4_2_split_goal_spatial := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n )
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n )
.

Definition pqdk_update_or_push_return_wit_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (n_after_2: Z) (PreH1 : (partial_map_update_or_add_size M_before n n_after_2 data_x_pre key_x_pre )) ,
  ((size_pre) # Int  |-> n_after_2)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n_after_2 )
|--
  EX (n_after: Z) ,
  “ (partial_map_update_or_add_size M_before n n_after data_x_pre key_x_pre ) ”
  &&  ((size_pre) # Int  |-> n_after)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n_after )
.

Definition pqdk_update_or_push_partial_solve_wit_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre )) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_update_or_add_pre M_before data_x_pre key_x_pre ) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (((pos_pre + (data_x_pre * sizeof(INT)))) # Int  |-> (Znth data_x_pre pos_values 0))
  **  (IntArray.missing_i pos_pre data_x_pre 0 data_bound_pre pos_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
.

Definition pqdk_update_or_push_partial_solve_wit_2_pure := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_absent M_before data_x_pre ) ”
.

Definition pqdk_update_or_push_partial_solve_wit_2_aux := 
forall (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre )) ,
  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_absent M_before data_x_pre ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_absent M_before data_x_pre ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
.

Definition pqdk_update_or_push_partial_solve_wit_2 := pqdk_update_or_push_partial_solve_wit_2_pure -> pqdk_update_or_push_partial_solve_wit_2_aux.

Definition pqdk_update_or_push_partial_solve_wit_3_pure := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (idx: Z) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ”
.

Definition pqdk_update_or_push_partial_solve_wit_3_aux := 
forall (key_x_pre: Z) (data_x_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (0 <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (0 <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre )) ,
  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  “ (0 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= data_x_pre) ” 
  &&  “ (data_x_pre < data_bound_pre) ” 
  &&  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
.

Definition pqdk_update_or_push_partial_solve_wit_3 := pqdk_update_or_push_partial_solve_wit_3_pure -> pqdk_update_or_push_partial_solve_wit_3_aux.

(*----- Function pqdk_pop -----*)

Definition pqdk_pop_safety_wit_1 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  ((( &( "result_key" ) )) # Int  |->_)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pqdk_pop_safety_wit_2 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  ((( &( "result_data" ) )) # Int  |->_)
  **  (IntArray.full key_pre n key_values )
  **  ((( &( "result_key" ) )) # Int  |-> (Znth 0 key_values 0))
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pqdk_pop_safety_wit_3 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (Znth 0 key_values 0))) (PreH2 : (result_data = (Znth 0 data_values 0))) (PreH3 : (1 <= n)) (PreH4 : (n <= capacity)) (PreH5 : (capacity <= heap_capacity)) (PreH6 : (0 <= result_data)) (PreH7 : (result_data < data_bound_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition pqdk_pop_safety_wit_4 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (Znth 0 key_values 0))) (PreH2 : (result_data = (Znth 0 data_values 0))) (PreH3 : (1 <= n)) (PreH4 : (n <= capacity)) (PreH5 : (capacity <= heap_capacity)) (PreH6 : (0 <= result_data)) (PreH7 : (result_data < data_bound_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_pop_safety_wit_5 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (Znth 0 key_values 0))) (PreH2 : (result_data = (Znth 0 data_values 0))) (PreH3 : (1 <= n)) (PreH4 : (n <= capacity)) (PreH5 : (capacity <= heap_capacity)) (PreH6 : (0 <= result_data)) (PreH7 : (result_data < data_bound_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (result_data) ((-1)) (pos_values)) )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_pop_safety_wit_6 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (n = 1)) (PreH2 : (result_key = (Znth 0 key_values 0))) (PreH3 : (result_data = (Znth 0 data_values 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= capacity)) (PreH6 : (capacity <= heap_capacity)) (PreH7 : (0 <= result_data)) (PreH8 : (result_data < data_bound_pre)) (PreH9 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (result_data) ((-1)) (pos_values)) )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pqdk_pop_safety_wit_7 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition pqdk_pop_safety_wit_8 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_pop_safety_wit_9 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full data_pre n data_values )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pqdk_pop_safety_wit_10 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pqdk_pop_safety_wit_11 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition pqdk_pop_safety_wit_12 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_pop_safety_wit_13 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full key_pre n (replace_Znth (0) ((Znth (n - 1 ) key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pqdk_pop_safety_wit_14 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full key_pre n (replace_Znth (0) ((Znth (n - 1 ) key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition pqdk_pop_safety_wit_15 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full key_pre n (replace_Znth (0) ((Znth (n - 1 ) key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_pop_safety_wit_16 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped )) (PreH8 : (0 <= (Znth 0 data_values 0))) (PreH9 : ((Znth 0 data_values 0) < data_bound_pre)) (PreH10 : (SiftDownState (partial_map_remove (M_before) ((item_data (popped)))) key_values data_values pos_values data_bound_pre (n - 1 ) 0 )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre (n - 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n - 1 ) capacity )
  **  (IntArray.full data_pre (n - 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n - 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition pqdk_pop_safety_wit_17 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped )) (PreH8 : (0 <= (Znth 0 data_values 0))) (PreH9 : ((Znth 0 data_values 0) < data_bound_pre)) (PreH10 : (SiftDownState (partial_map_remove (M_before) ((item_data (popped)))) key_values data_values pos_values data_bound_pre (n - 1 ) 0 )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre (n - 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n - 1 ) capacity )
  **  (IntArray.full data_pre (n - 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n - 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_pop_safety_wit_18 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> (n - 1 ))
  **  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) 0 )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition pqdk_pop_safety_wit_19 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> (n - 1 ))
  **  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) 0 )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pqdk_pop_safety_wit_20 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> (n - 1 ))
  **  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) 0 )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pqdk_pop_entail_wit_1 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  ((size_pre) # Int  |-> n)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (pos_values: (@list Z)) ,
  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
).

Definition pqdk_pop_entail_wit_2 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values_2 data_bound_pre n )) ,
  (IntArray.full data_pre n data_values )
  **  (IntArray.full key_pre n key_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
  **  ((data_out_pre) # Int  |-> (Znth 0 data_values 0))
  **  ((key_out_pre) # Int  |-> (Znth 0 key_values 0))
|--
  EX (pos_values: (@list Z))  (data_values_2: (@list Z))  (key_values_2: (@list Z)) ,
  “ ((Znth 0 key_values 0) = (Znth 0 key_values_2 0)) ” 
  &&  “ ((Znth 0 data_values 0) = (Znth 0 data_values_2 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= (Znth 0 data_values 0)) ” 
  &&  “ ((Znth 0 data_values 0) < data_bound_pre) ” 
  &&  “ (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values_2 )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values_2 )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> (Znth 0 data_values 0))
  **  ((key_out_pre) # Int  |-> (Znth 0 key_values 0))
) \/
(
forall (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values_2 data_bound_pre n )) ,
  TT && emp 
|--
  “ ((Znth 0 data_values 0) < data_bound_pre) ” 
  &&  “ (0 <= (Znth 0 data_values 0)) ”
  &&  emp
).

Definition pqdk_pop_entail_wit_2_split_goal_1 := 
forall (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values_2 data_bound_pre n )) ,
  ((Znth 0 data_values 0) < data_bound_pre)
.

Definition pqdk_pop_entail_wit_2_split_goal_2 := 
forall (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values_2: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values_2 data_bound_pre n )) ,
  (0 <= (Znth 0 data_values 0))
.

Definition pqdk_pop_entail_wit_3 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (n = 1)) (PreH2 : (result_key = (Znth 0 key_values 0))) (PreH3 : (result_data = (Znth 0 data_values 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= capacity)) (PreH6 : (capacity <= heap_capacity)) (PreH7 : (0 <= result_data)) (PreH8 : (result_data < data_bound_pre)) (PreH9 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (result_data) ((-1)) (pos_values)) )
  **  ((size_pre) # Int  |-> 0)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  EX (popped: (Z * Z)) ,
  “ (n = 1) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ”
  &&  ((size_pre) # Int  |-> 0)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) 0 )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
) \/
(
forall (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (n = 1)) (PreH2 : (result_key = (Znth 0 key_values 0))) (PreH3 : (result_data = (Znth 0 data_values 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= capacity)) (PreH6 : (capacity <= heap_capacity)) (PreH7 : (0 <= result_data)) (PreH8 : (result_data < data_bound_pre)) (PreH9 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (result_data) ((-1)) (pos_values)) )
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  EX (popped: (Z * Z)) ,
  “ (n = 1) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) 0 )
).

Definition pqdk_pop_entail_wit_4 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (n <> 1)) (PreH2 : (result_key = (Znth 0 key_values_2 0))) (PreH3 : (result_data = (Znth 0 data_values_2 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= capacity)) (PreH6 : (capacity <= heap_capacity)) (PreH7 : (0 <= result_data)) (PreH8 : (result_data < data_bound_pre)) (PreH9 : (heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth (result_data) ((-1)) (pos_values_2)) )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values_2 )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values_2 )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  EX (key_values: (@list Z))  (pos_values: (@list Z))  (data_values: (@list Z))  (popped: (Z * Z)) ,
  “ (1 < n) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (0 <= (Znth (n - 1 ) data_values 0)) ” 
  &&  “ ((Znth (n - 1 ) data_values 0) < data_bound_pre) ” 
  &&  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
) \/
(
forall (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (n <> 1)) (PreH2 : (result_key = (Znth 0 key_values_2 0))) (PreH3 : (result_data = (Znth 0 data_values_2 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= capacity)) (PreH6 : (capacity <= heap_capacity)) (PreH7 : (0 <= result_data)) (PreH8 : (result_data < data_bound_pre)) (PreH9 : (heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n )) ,
  TT && emp 
|--
  EX (popped: (Z * Z)) ,
  “ (1 < n) ” 
  &&  “ ((Znth 0 key_values_2 0) = (item_key (popped))) ” 
  &&  “ ((Znth 0 data_values_2 0) = (item_data (popped))) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (0 <= (Znth (n - 1 ) data_values_2 0)) ” 
  &&  “ ((Znth (n - 1 ) data_values_2 0) < data_bound_pre) ” 
  &&  “ (PopMarkedState M_before key_values_2 data_values_2 (replace_Znth ((Znth 0 data_values_2 0)) ((-1)) (pos_values_2)) data_bound_pre n popped ) ”
  &&  emp
).

Definition pqdk_pop_entail_wit_5 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped_2: (Z * Z)) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped_2)))) (PreH6 : (result_data = (item_data (popped_2)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values_2 0))) (PreH10 : ((Znth (n - 1 ) data_values_2 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n popped_2 )) ,
  (IntArray.full data_pre n (replace_Znth (0) ((Znth (n - 1 ) data_values_2 0)) (data_values_2)) )
  **  (IntArray.full key_pre n (replace_Znth (0) ((Znth (n - 1 ) key_values_2 0)) (key_values_2)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values_2 0)) (0) (pos_values_2)) )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  EX (key_values: (@list Z))  (pos_values: (@list Z))  (data_values: (@list Z))  (popped: (Z * Z)) ,
  “ (1 < n) ” 
  &&  “ (0 < (n - 1 )) ” 
  &&  “ ((n - 1 ) <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ” 
  &&  “ (0 <= (Znth 0 data_values 0)) ” 
  &&  “ ((Znth 0 data_values 0) < data_bound_pre) ” 
  &&  “ (SiftDownState (partial_map_remove (M_before) ((item_data (popped)))) key_values data_values pos_values data_bound_pre (n - 1 ) 0 ) ”
  &&  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre (n - 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n - 1 ) capacity )
  **  (IntArray.full data_pre (n - 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n - 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
) \/
(
forall (data_bound_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped_2: (Z * Z)) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped_2)))) (PreH6 : (result_data = (item_data (popped_2)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values_2 0))) (PreH10 : ((Znth (n - 1 ) data_values_2 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n popped_2 )) ,
  (IntArray.full data_pre n (replace_Znth (0) ((Znth (n - 1 ) data_values_2 0)) (data_values_2)) )
  **  (IntArray.full key_pre n (replace_Znth (0) ((Znth (n - 1 ) key_values_2 0)) (key_values_2)) )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
|--
  EX (key_values: (@list Z))  (data_values: (@list Z))  (popped: (Z * Z)) ,
  “ (1 < n) ” 
  &&  “ (0 < (n - 1 )) ” 
  &&  “ ((n - 1 ) <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ” 
  &&  “ (0 <= (Znth 0 data_values 0)) ” 
  &&  “ ((Znth 0 data_values 0) < data_bound_pre) ” 
  &&  “ (SiftDownState (partial_map_remove (M_before) ((item_data (popped)))) key_values data_values (replace_Znth ((Znth (n - 1 ) data_values_2 0)) (0) (pos_values_2)) data_bound_pre (n - 1 ) 0 ) ”
  &&  (IntArray.full key_pre (n - 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n - 1 ) capacity )
  **  (IntArray.full data_pre (n - 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n - 1 ) capacity )
).

Definition pqdk_pop_entail_wit_6 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped_2: (Z * Z)) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped_2)))) (PreH6 : (result_data = (item_data (popped_2)))) (PreH7 : (partial_map_minimum M_before popped_2 )) (PreH8 : (0 <= (Znth 0 data_values_2 0))) (PreH9 : ((Znth 0 data_values_2 0) < data_bound_pre)) (PreH10 : (SiftDownState (partial_map_remove (M_before) ((item_data (popped_2)))) key_values_2 data_values_2 pos_values_2 data_bound_pre (n - 1 ) 0 )) ,
  ((size_pre) # Int  |-> (n - 1 ))
  **  (IntArray.full key_pre (n - 1 ) key_values_2 )
  **  (IntArray.undef_seg key_pre (n - 1 ) capacity )
  **  (IntArray.full data_pre (n - 1 ) data_values_2 )
  **  (IntArray.undef_seg data_pre (n - 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values_2 )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  EX (key_values: (@list Z))  (pos_values: (@list Z))  (data_values: (@list Z))  (popped: (Z * Z)) ,
  “ (1 < n) ” 
  &&  “ (0 < (n - 1 )) ” 
  &&  “ ((n - 1 ) <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ” 
  &&  “ (0 <= (Znth 0 data_values 0)) ” 
  &&  “ ((Znth 0 data_values 0) < data_bound_pre) ” 
  &&  “ (SiftDownState (partial_map_remove (M_before) ((item_data (popped)))) key_values data_values pos_values data_bound_pre (n - 1 ) 0 ) ”
  &&  ((size_pre) # Int  |-> (n - 1 ))
  **  (IntArray.full key_pre (n - 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n - 1 ) capacity )
  **  (IntArray.full data_pre (n - 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n - 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
) \/
(
forall (data_bound_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped_2: (Z * Z)) (key_values_2: (@list Z)) (data_values_2: (@list Z)) (pos_values_2: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped_2)))) (PreH6 : (result_data = (item_data (popped_2)))) (PreH7 : (partial_map_minimum M_before popped_2 )) (PreH8 : (0 <= (Znth 0 data_values_2 0))) (PreH9 : ((Znth 0 data_values_2 0) < data_bound_pre)) (PreH10 : (SiftDownState (partial_map_remove (M_before) ((item_data (popped_2)))) key_values_2 data_values_2 pos_values_2 data_bound_pre (n - 1 ) 0 )) ,
  TT && emp 
|--
  EX (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ” 
  &&  “ (SiftDownState (partial_map_remove (M_before) ((item_data (popped)))) key_values_2 data_values_2 pos_values_2 data_bound_pre (n - 1 ) 0 ) ”
  &&  emp
).

Definition pqdk_pop_entail_wit_7 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped_2: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped_2)))) (PreH6 : (result_data = (item_data (popped_2)))) (PreH7 : (partial_map_minimum M_before popped_2 )) (PreH8 : (0 <= (Znth 0 data_values 0))) (PreH9 : ((Znth 0 data_values 0) < data_bound_pre)) (PreH10 : (SiftDownState (partial_map_remove (M_before) ((item_data (popped_2)))) key_values data_values pos_values data_bound_pre (n - 1 ) 0 )) ,
  ((size_pre) # Int  |-> (n - 1 ))
  **  (IntArray.full key_pre (n - 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n - 1 ) capacity )
  **  (IntArray.full data_pre (n - 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n - 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  EX (popped: (Z * Z)) ,
  “ (1 < n) ” 
  &&  “ (0 < (n - 1 )) ” 
  &&  “ ((n - 1 ) <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ”
  &&  ((size_pre) # Int  |-> (n - 1 ))
  **  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) 0 )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
) \/
(
forall (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped_2: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped_2)))) (PreH6 : (result_data = (item_data (popped_2)))) (PreH7 : (partial_map_minimum M_before popped_2 )) (PreH8 : (0 <= (Znth 0 data_values 0))) (PreH9 : ((Znth 0 data_values 0) < data_bound_pre)) (PreH10 : (SiftDownState (partial_map_remove (M_before) ((item_data (popped_2)))) key_values data_values pos_values data_bound_pre (n - 1 ) 0 )) ,
  (IntArray.full key_pre (n - 1 ) key_values )
  **  (IntArray.undef_seg key_pre (n - 1 ) capacity )
  **  (IntArray.full data_pre (n - 1 ) data_values )
  **  (IntArray.undef_seg data_pre (n - 1 ) capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
|--
  EX (popped: (Z * Z)) ,
  “ (1 < n) ” 
  &&  “ (0 < (n - 1 )) ” 
  &&  “ ((n - 1 ) <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ”
  &&  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) 0 )
).

Definition pqdk_pop_return_wit_1 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (n = 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (partial_map_minimum M_before popped_2 )) ,
  ((size_pre) # Int  |-> 0)
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped_2)))) 0 )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  EX (data_out_pre_v: Z)  (popped: (Z * Z))  (key_out_pre_v: Z) ,
  “ (key_out_pre_v = (item_key (popped))) ” 
  &&  “ (data_out_pre_v = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ”
  &&  ((key_out_pre) # Int  |-> key_out_pre_v)
  **  ((data_out_pre) # Int  |-> data_out_pre_v)
  **  ((size_pre) # Int  |-> (n - 1 ))
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) )
) \/
(
forall (data_bound_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (n = 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (partial_map_minimum M_before popped_2 )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped_2)))) 0 )
|--
  EX (popped: (Z * Z)) ,
  “ (result_data = (item_data (popped))) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (0 = (n - 1 )) ” 
  &&  “ (partial_map_minimum M_before popped ) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) )
).

Definition pqdk_pop_return_wit_2 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped_2)))) (PreH6 : (result_data = (item_data (popped_2)))) (PreH7 : (partial_map_minimum M_before popped_2 )) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped_2)))) (n - 1 ) )
  **  ((size_pre) # Int  |-> (n - 1 ))
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  EX (data_out_pre_v: Z)  (popped: (Z * Z))  (key_out_pre_v: Z) ,
  “ (key_out_pre_v = (item_key (popped))) ” 
  &&  “ (data_out_pre_v = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ”
  &&  ((key_out_pre) # Int  |-> key_out_pre_v)
  **  ((data_out_pre) # Int  |-> data_out_pre_v)
  **  ((size_pre) # Int  |-> (n - 1 ))
  **  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) )
.

Definition pqdk_pop_partial_solve_wit_1 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (((key_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 key_values 0))
  **  (IntArray.missing_i key_pre 0 0 n key_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pqdk_pop_partial_solve_wit_2 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  (IntArray.full key_pre n key_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (((data_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 data_values 0))
  **  (IntArray.missing_i data_pre 0 0 n data_values )
  **  (IntArray.full key_pre n key_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pqdk_pop_partial_solve_wit_3 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (Znth 0 key_values 0))) (PreH2 : (result_data = (Znth 0 data_values 0))) (PreH3 : (1 <= n)) (PreH4 : (n <= capacity)) (PreH5 : (capacity <= heap_capacity)) (PreH6 : (0 <= result_data)) (PreH7 : (result_data < data_bound_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n )) ,
  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (result_key = (Znth 0 key_values 0)) ” 
  &&  “ (result_data = (Znth 0 data_values 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (0 <= result_data) ” 
  &&  “ (result_data < data_bound_pre) ” 
  &&  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n ) ”
  &&  (((pos_pre + (result_data * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i pos_pre result_data 0 data_bound_pre pos_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
.

Definition pqdk_pop_partial_solve_wit_4 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.full data_pre n data_values )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 < n) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (0 <= (Znth (n - 1 ) data_values 0)) ” 
  &&  “ ((Znth (n - 1 ) data_values 0) < data_bound_pre) ” 
  &&  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped ) ”
  &&  (((data_pre + ((n - 1 ) * sizeof(INT)))) # Int  |-> (Znth (n - 1 ) data_values 0))
  **  (IntArray.missing_i data_pre (n - 1 ) 0 n data_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
.

Definition pqdk_pop_partial_solve_wit_5 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full data_pre n data_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  (IntArray.full pos_pre data_bound_pre pos_values )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 < n) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (0 <= (Znth (n - 1 ) data_values 0)) ” 
  &&  “ ((Znth (n - 1 ) data_values 0) < data_bound_pre) ” 
  &&  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped ) ”
  &&  (((pos_pre + ((Znth (n - 1 ) data_values 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i pos_pre (Znth (n - 1 ) data_values 0) 0 data_bound_pre pos_values )
  **  (IntArray.full data_pre n data_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
.

Definition pqdk_pop_partial_solve_wit_6 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.full key_pre n key_values )
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 < n) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (0 <= (Znth (n - 1 ) data_values 0)) ” 
  &&  “ ((Znth (n - 1 ) data_values 0) < data_bound_pre) ” 
  &&  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped ) ”
  &&  (((key_pre + ((n - 1 ) * sizeof(INT)))) # Int  |-> (Znth (n - 1 ) key_values 0))
  **  (IntArray.missing_i key_pre (n - 1 ) 0 n key_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
.

Definition pqdk_pop_partial_solve_wit_7 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full key_pre n key_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 < n) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (0 <= (Znth (n - 1 ) data_values 0)) ” 
  &&  “ ((Znth (n - 1 ) data_values 0) < data_bound_pre) ” 
  &&  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped ) ”
  &&  (((key_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre 0 0 n key_values )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
.

Definition pqdk_pop_partial_solve_wit_8 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full key_pre n (replace_Znth (0) ((Znth (n - 1 ) key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  (IntArray.full data_pre n data_values )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 < n) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (0 <= (Znth (n - 1 ) data_values 0)) ” 
  &&  “ ((Znth (n - 1 ) data_values 0) < data_bound_pre) ” 
  &&  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped ) ”
  &&  (((data_pre + ((n - 1 ) * sizeof(INT)))) # Int  |-> (Znth (n - 1 ) data_values 0))
  **  (IntArray.missing_i data_pre (n - 1 ) 0 n data_values )
  **  (IntArray.full key_pre n (replace_Znth (0) ((Znth (n - 1 ) key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
.

Definition pqdk_pop_partial_solve_wit_9 := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (key_values: (@list Z)) (data_values: (@list Z)) (pos_values: (@list Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (0 <= (n - 1 ))) (PreH8 : ((n - 1 ) < n)) (PreH9 : (0 <= (Znth (n - 1 ) data_values 0))) (PreH10 : ((Znth (n - 1 ) data_values 0) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped )) ,
  (IntArray.full data_pre n data_values )
  **  (IntArray.full key_pre n (replace_Znth (0) ((Znth (n - 1 ) key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (1 < n) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (0 <= (Znth (n - 1 ) data_values 0)) ” 
  &&  “ ((Znth (n - 1 ) data_values 0) < data_bound_pre) ” 
  &&  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped ) ”
  &&  (((data_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre 0 0 n data_values )
  **  (IntArray.full key_pre n (replace_Znth (0) ((Znth (n - 1 ) key_values 0)) (key_values)) )
  **  (IntArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1 ) data_values 0)) (0) (pos_values)) )
  **  ((size_pre) # Int  |-> n)
  **  (IntArray.undef_seg key_pre n capacity )
  **  (IntArray.undef_seg data_pre n capacity )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
.

Definition pqdk_pop_partial_solve_wit_10_pure := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "pos" ) )) # Ptr  |-> pos_pre)
  **  ((( &( "size" ) )) # Ptr  |-> size_pre)
  **  ((( &( "data_bound" ) )) # Int  |-> data_bound_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((size_pre) # Int  |-> (n - 1 ))
  **  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) 0 )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (0 <= 0) ” 
  &&  “ (0 < (n - 1 )) ” 
  &&  “ ((n - 1 ) <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ”
.

Definition pqdk_pop_partial_solve_wit_10_aux := 
forall (key_out_pre: Z) (data_out_pre: Z) (data_bound_pre: Z) (size_pre: Z) (pos_pre: Z) (data_pre: Z) (key_pre: Z) (capacity: Z) (n: Z) (M_before: partial_map) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (1 < n)) (PreH2 : (0 < (n - 1 ))) (PreH3 : ((n - 1 ) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped )) ,
  ((size_pre) # Int  |-> (n - 1 ))
  **  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) 0 )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  “ (0 <= 0) ” 
  &&  “ (0 < (n - 1 )) ” 
  &&  “ ((n - 1 ) <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (1 < n) ” 
  &&  “ (0 < (n - 1 )) ” 
  &&  “ ((n - 1 ) <= capacity) ” 
  &&  “ (capacity <= heap_capacity) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (partial_map_minimum M_before popped ) ”
  &&  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1 ) 0 )
  **  ((size_pre) # Int  |-> (n - 1 ))
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
.

Definition pqdk_pop_partial_solve_wit_10 := pqdk_pop_partial_solve_wit_10_pure -> pqdk_pop_partial_solve_wit_10_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_pqdk_sift_up_safety_wit_1 : pqdk_sift_up_safety_wit_1.
Axiom proof_of_pqdk_sift_up_safety_wit_2 : pqdk_sift_up_safety_wit_2.
Axiom proof_of_pqdk_sift_up_safety_wit_3 : pqdk_sift_up_safety_wit_3.
Axiom proof_of_pqdk_sift_up_safety_wit_4 : pqdk_sift_up_safety_wit_4.
Axiom proof_of_pqdk_sift_up_safety_wit_5 : pqdk_sift_up_safety_wit_5.
Axiom proof_of_pqdk_sift_up_entail_wit_1 : pqdk_sift_up_entail_wit_1.
Axiom proof_of_pqdk_sift_up_entail_wit_2 : pqdk_sift_up_entail_wit_2.
Axiom proof_of_pqdk_sift_up_entail_wit_3 : pqdk_sift_up_entail_wit_3.
Axiom proof_of_pqdk_sift_up_entail_wit_4 : pqdk_sift_up_entail_wit_4.
Axiom proof_of_pqdk_sift_up_entail_wit_5 : pqdk_sift_up_entail_wit_5.
Axiom proof_of_pqdk_sift_up_return_wit_1 : pqdk_sift_up_return_wit_1.
Axiom proof_of_pqdk_sift_up_return_wit_2 : pqdk_sift_up_return_wit_2.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_1 : pqdk_sift_up_partial_solve_wit_1.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_2 : pqdk_sift_up_partial_solve_wit_2.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_3 : pqdk_sift_up_partial_solve_wit_3.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_4 : pqdk_sift_up_partial_solve_wit_4.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_5 : pqdk_sift_up_partial_solve_wit_5.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_6 : pqdk_sift_up_partial_solve_wit_6.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_7 : pqdk_sift_up_partial_solve_wit_7.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_8 : pqdk_sift_up_partial_solve_wit_8.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_9 : pqdk_sift_up_partial_solve_wit_9.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_10 : pqdk_sift_up_partial_solve_wit_10.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_11 : pqdk_sift_up_partial_solve_wit_11.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_12 : pqdk_sift_up_partial_solve_wit_12.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_13 : pqdk_sift_up_partial_solve_wit_13.
Axiom proof_of_pqdk_sift_up_partial_solve_wit_14 : pqdk_sift_up_partial_solve_wit_14.
Axiom proof_of_pqdk_sift_down_safety_wit_1 : pqdk_sift_down_safety_wit_1.
Axiom proof_of_pqdk_sift_down_safety_wit_2 : pqdk_sift_down_safety_wit_2.
Axiom proof_of_pqdk_sift_down_safety_wit_3 : pqdk_sift_down_safety_wit_3.
Axiom proof_of_pqdk_sift_down_safety_wit_4 : pqdk_sift_down_safety_wit_4.
Axiom proof_of_pqdk_sift_down_safety_wit_5 : pqdk_sift_down_safety_wit_5.
Axiom proof_of_pqdk_sift_down_safety_wit_6 : pqdk_sift_down_safety_wit_6.
Axiom proof_of_pqdk_sift_down_safety_wit_7 : pqdk_sift_down_safety_wit_7.
Axiom proof_of_pqdk_sift_down_safety_wit_8 : pqdk_sift_down_safety_wit_8.
Axiom proof_of_pqdk_sift_down_safety_wit_9 : pqdk_sift_down_safety_wit_9.
Axiom proof_of_pqdk_sift_down_safety_wit_10 : pqdk_sift_down_safety_wit_10.
Axiom proof_of_pqdk_sift_down_entail_wit_1 : pqdk_sift_down_entail_wit_1.
Axiom proof_of_pqdk_sift_down_entail_wit_2 : pqdk_sift_down_entail_wit_2.
Axiom proof_of_pqdk_sift_down_entail_wit_3_1 : pqdk_sift_down_entail_wit_3_1.
Axiom proof_of_pqdk_sift_down_entail_wit_3_2 : pqdk_sift_down_entail_wit_3_2.
Axiom proof_of_pqdk_sift_down_entail_wit_3_3 : pqdk_sift_down_entail_wit_3_3.
Axiom proof_of_pqdk_sift_down_entail_wit_4 : pqdk_sift_down_entail_wit_4.
Axiom proof_of_pqdk_sift_down_entail_wit_5 : pqdk_sift_down_entail_wit_5.
Axiom proof_of_pqdk_sift_down_entail_wit_6 : pqdk_sift_down_entail_wit_6.
Axiom proof_of_pqdk_sift_down_return_wit_1 : pqdk_sift_down_return_wit_1.
Axiom proof_of_pqdk_sift_down_return_wit_2 : pqdk_sift_down_return_wit_2.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_1 : pqdk_sift_down_partial_solve_wit_1.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_2 : pqdk_sift_down_partial_solve_wit_2.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_3 : pqdk_sift_down_partial_solve_wit_3.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_4 : pqdk_sift_down_partial_solve_wit_4.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_5 : pqdk_sift_down_partial_solve_wit_5.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_6 : pqdk_sift_down_partial_solve_wit_6.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_7 : pqdk_sift_down_partial_solve_wit_7.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_8 : pqdk_sift_down_partial_solve_wit_8.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_9 : pqdk_sift_down_partial_solve_wit_9.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_10 : pqdk_sift_down_partial_solve_wit_10.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_11 : pqdk_sift_down_partial_solve_wit_11.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_12 : pqdk_sift_down_partial_solve_wit_12.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_13 : pqdk_sift_down_partial_solve_wit_13.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_14 : pqdk_sift_down_partial_solve_wit_14.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_15 : pqdk_sift_down_partial_solve_wit_15.
Axiom proof_of_pqdk_sift_down_partial_solve_wit_16 : pqdk_sift_down_partial_solve_wit_16.
Axiom proof_of_pqdk_push_safety_wit_1 : pqdk_push_safety_wit_1.
Axiom proof_of_pqdk_push_safety_wit_2 : pqdk_push_safety_wit_2.
Axiom proof_of_pqdk_push_safety_wit_3 : pqdk_push_safety_wit_3.
Axiom proof_of_pqdk_push_safety_wit_4 : pqdk_push_safety_wit_4.
Axiom proof_of_pqdk_push_entail_wit_1 : pqdk_push_entail_wit_1.
Axiom proof_of_pqdk_push_entail_wit_2 : pqdk_push_entail_wit_2.
Axiom proof_of_pqdk_push_entail_wit_3 : pqdk_push_entail_wit_3.
Axiom proof_of_pqdk_push_return_wit_1 : pqdk_push_return_wit_1.
Axiom proof_of_pqdk_push_partial_solve_wit_1 : pqdk_push_partial_solve_wit_1.
Axiom proof_of_pqdk_push_partial_solve_wit_2 : pqdk_push_partial_solve_wit_2.
Axiom proof_of_pqdk_push_partial_solve_wit_3 : pqdk_push_partial_solve_wit_3.
Axiom proof_of_pqdk_push_partial_solve_wit_4_pure : pqdk_push_partial_solve_wit_4_pure.
Axiom proof_of_pqdk_push_partial_solve_wit_4 : pqdk_push_partial_solve_wit_4.
Axiom proof_of_pqdk_decrease_key_entail_wit_1 : pqdk_decrease_key_entail_wit_1.
Axiom proof_of_pqdk_decrease_key_entail_wit_2 : pqdk_decrease_key_entail_wit_2.
Axiom proof_of_pqdk_decrease_key_entail_wit_3 : pqdk_decrease_key_entail_wit_3.
Axiom proof_of_pqdk_decrease_key_entail_wit_4 : pqdk_decrease_key_entail_wit_4.
Axiom proof_of_pqdk_decrease_key_return_wit_1 : pqdk_decrease_key_return_wit_1.
Axiom proof_of_pqdk_decrease_key_partial_solve_wit_1 : pqdk_decrease_key_partial_solve_wit_1.
Axiom proof_of_pqdk_decrease_key_partial_solve_wit_2 : pqdk_decrease_key_partial_solve_wit_2.
Axiom proof_of_pqdk_decrease_key_partial_solve_wit_3_pure : pqdk_decrease_key_partial_solve_wit_3_pure.
Axiom proof_of_pqdk_decrease_key_partial_solve_wit_3 : pqdk_decrease_key_partial_solve_wit_3.
Axiom proof_of_pqdk_update_or_push_safety_wit_1 : pqdk_update_or_push_safety_wit_1.
Axiom proof_of_pqdk_update_or_push_entail_wit_1 : pqdk_update_or_push_entail_wit_1.
Axiom proof_of_pqdk_update_or_push_entail_wit_2 : pqdk_update_or_push_entail_wit_2.
Axiom proof_of_pqdk_update_or_push_entail_wit_3 : pqdk_update_or_push_entail_wit_3.
Axiom proof_of_pqdk_update_or_push_entail_wit_4_1 : pqdk_update_or_push_entail_wit_4_1.
Axiom proof_of_pqdk_update_or_push_entail_wit_4_2 : pqdk_update_or_push_entail_wit_4_2.
Axiom proof_of_pqdk_update_or_push_return_wit_1 : pqdk_update_or_push_return_wit_1.
Axiom proof_of_pqdk_update_or_push_partial_solve_wit_1 : pqdk_update_or_push_partial_solve_wit_1.
Axiom proof_of_pqdk_update_or_push_partial_solve_wit_2_pure : pqdk_update_or_push_partial_solve_wit_2_pure.
Axiom proof_of_pqdk_update_or_push_partial_solve_wit_2 : pqdk_update_or_push_partial_solve_wit_2.
Axiom proof_of_pqdk_update_or_push_partial_solve_wit_3_pure : pqdk_update_or_push_partial_solve_wit_3_pure.
Axiom proof_of_pqdk_update_or_push_partial_solve_wit_3 : pqdk_update_or_push_partial_solve_wit_3.
Axiom proof_of_pqdk_pop_safety_wit_1 : pqdk_pop_safety_wit_1.
Axiom proof_of_pqdk_pop_safety_wit_2 : pqdk_pop_safety_wit_2.
Axiom proof_of_pqdk_pop_safety_wit_3 : pqdk_pop_safety_wit_3.
Axiom proof_of_pqdk_pop_safety_wit_4 : pqdk_pop_safety_wit_4.
Axiom proof_of_pqdk_pop_safety_wit_5 : pqdk_pop_safety_wit_5.
Axiom proof_of_pqdk_pop_safety_wit_6 : pqdk_pop_safety_wit_6.
Axiom proof_of_pqdk_pop_safety_wit_7 : pqdk_pop_safety_wit_7.
Axiom proof_of_pqdk_pop_safety_wit_8 : pqdk_pop_safety_wit_8.
Axiom proof_of_pqdk_pop_safety_wit_9 : pqdk_pop_safety_wit_9.
Axiom proof_of_pqdk_pop_safety_wit_10 : pqdk_pop_safety_wit_10.
Axiom proof_of_pqdk_pop_safety_wit_11 : pqdk_pop_safety_wit_11.
Axiom proof_of_pqdk_pop_safety_wit_12 : pqdk_pop_safety_wit_12.
Axiom proof_of_pqdk_pop_safety_wit_13 : pqdk_pop_safety_wit_13.
Axiom proof_of_pqdk_pop_safety_wit_14 : pqdk_pop_safety_wit_14.
Axiom proof_of_pqdk_pop_safety_wit_15 : pqdk_pop_safety_wit_15.
Axiom proof_of_pqdk_pop_safety_wit_16 : pqdk_pop_safety_wit_16.
Axiom proof_of_pqdk_pop_safety_wit_17 : pqdk_pop_safety_wit_17.
Axiom proof_of_pqdk_pop_safety_wit_18 : pqdk_pop_safety_wit_18.
Axiom proof_of_pqdk_pop_safety_wit_19 : pqdk_pop_safety_wit_19.
Axiom proof_of_pqdk_pop_safety_wit_20 : pqdk_pop_safety_wit_20.
Axiom proof_of_pqdk_pop_entail_wit_1 : pqdk_pop_entail_wit_1.
Axiom proof_of_pqdk_pop_entail_wit_2 : pqdk_pop_entail_wit_2.
Axiom proof_of_pqdk_pop_entail_wit_3 : pqdk_pop_entail_wit_3.
Axiom proof_of_pqdk_pop_entail_wit_4 : pqdk_pop_entail_wit_4.
Axiom proof_of_pqdk_pop_entail_wit_5 : pqdk_pop_entail_wit_5.
Axiom proof_of_pqdk_pop_entail_wit_6 : pqdk_pop_entail_wit_6.
Axiom proof_of_pqdk_pop_entail_wit_7 : pqdk_pop_entail_wit_7.
Axiom proof_of_pqdk_pop_return_wit_1 : pqdk_pop_return_wit_1.
Axiom proof_of_pqdk_pop_return_wit_2 : pqdk_pop_return_wit_2.
Axiom proof_of_pqdk_pop_partial_solve_wit_1 : pqdk_pop_partial_solve_wit_1.
Axiom proof_of_pqdk_pop_partial_solve_wit_2 : pqdk_pop_partial_solve_wit_2.
Axiom proof_of_pqdk_pop_partial_solve_wit_3 : pqdk_pop_partial_solve_wit_3.
Axiom proof_of_pqdk_pop_partial_solve_wit_4 : pqdk_pop_partial_solve_wit_4.
Axiom proof_of_pqdk_pop_partial_solve_wit_5 : pqdk_pop_partial_solve_wit_5.
Axiom proof_of_pqdk_pop_partial_solve_wit_6 : pqdk_pop_partial_solve_wit_6.
Axiom proof_of_pqdk_pop_partial_solve_wit_7 : pqdk_pop_partial_solve_wit_7.
Axiom proof_of_pqdk_pop_partial_solve_wit_8 : pqdk_pop_partial_solve_wit_8.
Axiom proof_of_pqdk_pop_partial_solve_wit_9 : pqdk_pop_partial_solve_wit_9.
Axiom proof_of_pqdk_pop_partial_solve_wit_10_pure : pqdk_pop_partial_solve_wit_10_pure.
Axiom proof_of_pqdk_pop_partial_solve_wit_10 : pqdk_pop_partial_solve_wit_10.

End VC_Correct.
