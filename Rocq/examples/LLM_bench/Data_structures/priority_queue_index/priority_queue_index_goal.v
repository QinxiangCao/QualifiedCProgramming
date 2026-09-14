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
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function push -----*)

Definition push_safety_wit_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_current: (@list Z)) (data_current: (@list Z)) (key_written: (@list Z)) (data_written: (@list Z)) (child: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 <= child)) (PreH4 : (child <= n_pre)) (PreH5 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH6 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition push_safety_wit_2 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_current: (@list Z)) (data_current: (@list Z)) (key_written: (@list Z)) (data_written: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ (((child - 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition push_safety_wit_3 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_current: (@list Z)) (data_current: (@list Z)) (key_written: (@list Z)) (data_written: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ ((child - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (child - 1 )) ”
.

Definition push_safety_wit_4 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_current: (@list Z)) (data_current: (@list Z)) (key_written: (@list Z)) (data_written: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition push_safety_wit_5 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_current: (@list Z)) (data_current: (@list Z)) (key_written: (@list Z)) (data_written: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x_pre)
  **  ((( &( "key_x" ) )) # Int  |-> key_x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition push_entail_wit_1 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) ,
  (store_heap key_pre data_pre S_before n_pre )
|--
  EX (key_base: (@list Z))  (data_base: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (heap_representation S_before key_base data_base n_pre ) ”
  &&  (IntArray.full key_pre n_pre key_base )
  **  (IntArray.undef_seg key_pre n_pre (n_pre + 1 ) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre n_pre data_base )
  **  (IntArray.undef_seg data_pre n_pre (n_pre + 1 ) )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
) \/
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) ,
  (store_heap key_pre data_pre S_before n_pre )
|--
  EX (key_base: (@list Z))  (data_base: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (heap_representation S_before key_base data_base n_pre ) ”
  &&  (IntArray.full key_pre n_pre key_base )
  **  (IntArray.undef_seg key_pre n_pre (n_pre + 1 ) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre n_pre data_base )
  **  (IntArray.undef_seg data_pre n_pre (n_pre + 1 ) )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
).

Definition push_entail_wit_2 := 
(
forall (key_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_base_2: (@list Z)) (data_base_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before key_base_2 data_base_2 n_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) (app (key_base_2) ((cons (key_x_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre n_pre data_base_2 )
  **  (IntArray.undef_seg data_pre n_pre (n_pre + 1 ) )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  EX (key_base: (@list Z))  (data_base: (@list Z))  (key_written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (KeyWriteState S_before key_base data_base key_written n_pre key_x_pre ) ”
  &&  (IntArray.full key_pre (n_pre + 1 ) key_written )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre n_pre data_base )
  **  (IntArray.undef_seg data_pre n_pre (n_pre + 1 ) )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
) \/
(
forall (key_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_base_2: (@list Z)) (data_base_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before key_base_2 data_base_2 n_pre )) ,
  TT && emp 
|--
  EX (key_base: (@list Z)) ,
  “ (KeyWriteState S_before key_base data_base_2 (app (key_base_2) ((cons (key_x_pre) ((@nil Z))))) n_pre key_x_pre ) ”
  &&  emp
).

Definition push_entail_wit_3 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_base: (@list Z)) (data_base: (@list Z)) (key_written_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (KeyWriteState S_before key_base data_base key_written_2 n_pre key_x_pre )) ,
  (IntArray.full data_pre (n_pre + 1 ) (app (data_base) ((cons (data_x_pre) ((@nil Z))))) )
  **  (IntArray.full key_pre (n_pre + 1 ) key_written_2 )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  EX (key_written: (@list Z))  (data_written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_written data_written n_pre n_pre data_x_pre key_x_pre ) ”
  &&  (IntArray.full key_pre (n_pre + 1 ) key_written )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_written )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_base: (@list Z)) (data_base: (@list Z)) (key_written_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (KeyWriteState S_before key_base data_base key_written_2 n_pre key_x_pre )) ,
  TT && emp 
|--
  “ (PushLoopState key_written_2 (app (data_base) ((cons (data_x_pre) ((@nil Z))))) key_written_2 (app (data_base) ((cons (data_x_pre) ((@nil Z))))) n_pre n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushSource key_written_2 (app (data_base) ((cons (data_x_pre) ((@nil Z))))) S_before n_pre data_x_pre key_x_pre ) ”
  &&  emp
).

Definition push_entail_wit_3_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_base: (@list Z)) (data_base: (@list Z)) (key_written_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (KeyWriteState S_before key_base data_base key_written_2 n_pre key_x_pre )) ,
  (PushLoopState key_written_2 (app (data_base) ((cons (data_x_pre) ((@nil Z))))) key_written_2 (app (data_base) ((cons (data_x_pre) ((@nil Z))))) n_pre n_pre data_x_pre key_x_pre )
.

Definition push_entail_wit_3_split_goal_2 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_base: (@list Z)) (data_base: (@list Z)) (key_written_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (KeyWriteState S_before key_base data_base key_written_2 n_pre key_x_pre )) ,
  (PushSource key_written_2 (app (data_base) ((cons (data_x_pre) ((@nil Z))))) S_before n_pre data_x_pre key_x_pre )
.

Definition push_entail_wit_4 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH4 : (PushLoopState key_written_2 data_written_2 key_written_2 data_written_2 n_pre n_pre data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_written_2 )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_written_2 )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  EX (key_current: (@list Z))  (data_current: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre n_pre data_x_pre key_x_pre ) ”
  &&  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH4 : (PushLoopState key_written_2 data_written_2 key_written_2 data_written_2 n_pre n_pre data_x_pre key_x_pre )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z)) ,
  “ (n_pre <= n_pre) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_written_2 data_written_2 n_pre n_pre data_x_pre key_x_pre ) ”
  &&  emp
).

Definition push_entail_wit_5 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH7 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_current_2 )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current_2 )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  EX (key_current: (@list Z))  (data_current: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= ((child - 1 ) ÷ 2 )) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < child) ” 
  &&  “ (((child - 1 ) ÷ 2 ) <= n_pre) ” 
  &&  “ (((child - 1 ) ÷ 2 ) = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH7 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z)) ,
  “ (0 < child) ” 
  &&  “ (0 <= ((child - 1 ) ÷ 2 )) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < child) ” 
  &&  “ (((child - 1 ) ÷ 2 ) <= n_pre) ” 
  &&  “ (((child - 1 ) ÷ 2 ) = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current_2 data_current_2 n_pre child data_x_pre key_x_pre ) ”
  &&  emp
).

Definition push_entail_wit_6 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current_2 0) <= (Znth child key_current_2 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_current_2 )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current_2 )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  EX (data_current: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z))  (key_current: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_current 0) <= (Znth child key_current 0)) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushResult S_before key_current data_current n_pre data_x_pre key_x_pre ) ”
  &&  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current_2 0) <= (Znth child key_current_2 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre )) ,
  TT && emp 
|--
  “ (PushResult S_before key_current_2 data_current_2 n_pre data_x_pre key_x_pre ) ”
  &&  emp
).

Definition push_entail_wit_6_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current_2 0) <= (Znth child key_current_2 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre )) ,
  (PushResult S_before key_current_2 data_current_2 n_pre data_x_pre key_x_pre )
.

Definition push_entail_wit_7 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written_2 data_written_2 key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full data_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent data_current 0)) ((replace_Znth (parent) ((Znth child data_current 0)) (data_current)))) )
  **  (IntArray.full key_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (data_current_2: (@list Z))  (key_current_2: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_current 0) = (Znth child key_current_2 0)) ” 
  &&  “ ((Znth parent data_current 0) = (Znth child data_current_2 0)) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current_2 data_current_2 n_pre parent data_x_pre key_x_pre ) ”
  &&  (IntArray.full key_pre (n_pre + 1 ) key_current_2 )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current_2 )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written_2 data_written_2 key_current data_current n_pre child data_x_pre key_x_pre )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z)) ,
  “ ((Znth (heap_parent (child)) key_current 0) = (Znth child (replace_Znth (child) ((Znth (heap_parent (child)) key_current 0)) ((replace_Znth ((heap_parent (child))) ((Znth child key_current 0)) (key_current)))) 0)) ” 
  &&  “ ((Znth (heap_parent (child)) data_current 0) = (Znth child (replace_Znth (child) ((Znth (heap_parent (child)) data_current 0)) ((replace_Znth ((heap_parent (child))) ((Znth child data_current 0)) (data_current)))) 0)) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written (replace_Znth (child) ((Znth (heap_parent (child)) key_current 0)) ((replace_Znth ((heap_parent (child))) ((Znth child key_current 0)) (key_current)))) (replace_Znth (child) ((Znth (heap_parent (child)) data_current 0)) ((replace_Znth ((heap_parent (child))) ((Znth child data_current 0)) (data_current)))) n_pre (heap_parent (child)) data_x_pre key_x_pre ) ”
  &&  emp
).

Definition push_entail_wit_8 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child <= n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (tmp_key = (Znth child key_current_2 0))) (PreH10 : (tmp_data = (Znth child data_current_2 0))) (PreH11 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH12 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre parent data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_current_2 )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current_2 )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  EX (key_current: (@list Z))  (data_current: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre parent data_x_pre key_x_pre ) ”
  &&  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child <= n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (tmp_key = (Znth child key_current_2 0))) (PreH10 : (tmp_data = (Znth child data_current_2 0))) (PreH11 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH12 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre parent data_x_pre key_x_pre )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z)) ,
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current_2 data_current_2 n_pre (heap_parent (child)) data_x_pre key_x_pre ) ”
  &&  emp
).

Definition push_entail_wit_9_1 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_current: (@list Z)) (data_current: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (child: Z) (PreH1 : (child <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH7 : (PushLoopState key_written_2 data_written_2 key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  EX (key_result: (@list Z))  (data_result: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushResult S_before key_result data_result n_pre data_x_pre key_x_pre ) ”
  &&  (IntArray.full key_pre (n_pre + 1 ) key_result )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_result )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_current: (@list Z)) (data_current: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (child: Z) (PreH1 : (child <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH7 : (PushLoopState key_written_2 data_written_2 key_current data_current n_pre child data_x_pre key_x_pre )) ,
  TT && emp 
|--
  “ (PushResult S_before key_current data_current n_pre data_x_pre key_x_pre ) ”
  &&  emp
).

Definition push_entail_wit_9_1_split_goal_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (S_before: (@multiset (Z * Z))) (key_current: (@list Z)) (data_current: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (child: Z) (PreH1 : (child <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH7 : (PushLoopState key_written_2 data_written_2 key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (PushResult S_before key_current data_current n_pre data_x_pre key_x_pre )
.

Definition push_entail_wit_9_2 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child <= n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_current 0) <= (Znth child key_current 0))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushResult S_before key_current data_current n_pre data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  EX (key_result: (@list Z))  (data_result: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushResult S_before key_result data_result n_pre data_x_pre key_x_pre ) ”
  &&  (IntArray.full key_pre (n_pre + 1 ) key_result )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_result )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_entail_wit_10 := 
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_result: (@list Z)) (data_result: (@list Z)) (child: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 <= child)) (PreH4 : (child <= n_pre)) (PreH5 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH6 : (PushResult S_before key_result data_result n_pre data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_result )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_result )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ (0 <= child) ” 
  &&  “ (child <= n_pre) ”
  &&  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1 ) )
) \/
(
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_result: (@list Z)) (data_result: (@list Z)) (child: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 <= child)) (PreH4 : (child <= n_pre)) (PreH5 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH6 : (PushResult S_before key_result data_result n_pre data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_result )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_result )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1 ) )
).

Definition push_entail_wit_10_split_goal_spatial := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_result: (@list Z)) (data_result: (@list Z)) (child: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 <= child)) (PreH4 : (child <= n_pre)) (PreH5 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH6 : (PushResult S_before key_result data_result n_pre data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_result )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_result )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1 ) )
.

Definition push_return_wit_1 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (child: Z) (PreH1 : (0 <= child)) (PreH2 : (child <= n_pre)) ,
  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1 ) )
|--
  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1 ) )
.

Definition push_partial_solve_wit_1 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_base: (@list Z)) (data_base: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before key_base data_base n_pre )) ,
  (IntArray.full key_pre n_pre key_base )
  **  (IntArray.undef_seg key_pre n_pre (n_pre + 1 ) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre n_pre data_base )
  **  (IntArray.undef_seg data_pre n_pre (n_pre + 1 ) )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (heap_representation S_before key_base data_base n_pre ) ”
  &&  (((key_pre + (n_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.full key_pre n_pre key_base )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre n_pre data_base )
  **  (IntArray.undef_seg data_pre n_pre (n_pre + 1 ) )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_2 := 
forall (key_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_base: (@list Z)) (data_base: (@list Z)) (key_written: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (KeyWriteState S_before key_base data_base key_written n_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_written )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre n_pre data_base )
  **  (IntArray.undef_seg data_pre n_pre (n_pre + 1 ) )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (KeyWriteState S_before key_base data_base key_written n_pre key_x_pre ) ”
  &&  (((data_pre + (n_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.full key_pre (n_pre + 1 ) key_written )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre n_pre data_base )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_3 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child <= n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH10 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent key_current 0))
  **  (IntArray.missing_i key_pre parent 0 (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_4 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child <= n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH10 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |-> (Znth child key_current 0))
  **  (IntArray.missing_i key_pre child 0 (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_5 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent key_current 0))
  **  (IntArray.missing_i key_pre parent 0 (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_6 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |-> (Znth child key_current 0))
  **  (IntArray.missing_i key_pre child 0 (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_7 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre parent 0 (n_pre + 1 ) key_current )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_8 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) (replace_Znth (parent) ((Znth child key_current 0)) (key_current)) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre child 0 (n_pre + 1 ) (replace_Znth (parent) ((Znth child key_current 0)) (key_current)) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_9 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full key_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent data_current 0))
  **  (IntArray.missing_i data_pre parent 0 (n_pre + 1 ) data_current )
  **  (IntArray.full key_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_10 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.full key_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int  |-> (Znth child data_current 0))
  **  (IntArray.missing_i data_pre child 0 (n_pre + 1 ) data_current )
  **  (IntArray.full key_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_11 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full data_pre (n_pre + 1 ) data_current )
  **  (IntArray.full key_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre parent 0 (n_pre + 1 ) data_current )
  **  (IntArray.full key_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

Definition push_partial_solve_wit_12 := 
forall (key_x_pre: Z) (data_x_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre )) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre )) ,
  (IntArray.full data_pre (n_pre + 1 ) (replace_Znth (parent) ((Znth child data_current 0)) (data_current)) )
  **  (IntArray.full key_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre ) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre child 0 (n_pre + 1 ) (replace_Znth (parent) ((Znth child data_current 0)) (data_current)) )
  **  (IntArray.full key_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.undef_seg key_pre (n_pre + 1 ) heap_capacity )
  **  (IntArray.undef_seg data_pre (n_pre + 1 ) heap_capacity )
.

(*----- Function build -----*)

Definition build_safety_wit_1 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (key_input)) = n_pre)) (PreH4 : ((Zlength (data_input)) = n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full key_pre n_pre key_input )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre data_input )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_2 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)) (PreH4 : ((Zlength (key_input)) = n_pre)) (PreH5 : ((Zlength (data_input)) = n_pre)) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full key_pre n_pre key_input )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre data_input )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ False ”
.

Definition build_safety_wit_3 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (key_written: (@list Z)) (data_written: (@list Z)) (S_prefix: (@multiset (Z * Z))) (child: Z) (key_x: Z) (i: Z) (data_x: Z) (PreH1 : (data_x = (Znth i data_input 0))) (PreH2 : (key_x = (Znth i key_input 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= child)) (PreH8 : (child <= i)) (PreH9 : ((Zlength (key_input)) = n_pre)) (PreH10 : ((Zlength (data_input)) = n_pre)) (PreH11 : (BuildPrefixState S_prefix key_input data_input i )) (PreH12 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH13 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "key_x" ) )) # Int  |-> key_x)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_4 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (key_written: (@list Z)) (data_written: (@list Z)) (S_prefix: (@multiset (Z * Z))) (child: Z) (key_x: Z) (i: Z) (data_x: Z) (PreH1 : (child > 0)) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix key_input data_input i )) (PreH13 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "key_x" ) )) # Int  |-> key_x)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ (((child - 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition build_safety_wit_5 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (key_written: (@list Z)) (data_written: (@list Z)) (S_prefix: (@multiset (Z * Z))) (child: Z) (key_x: Z) (i: Z) (data_x: Z) (PreH1 : (child > 0)) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix key_input data_input i )) (PreH13 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "key_x" ) )) # Int  |-> key_x)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ ((child - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (child - 1 )) ”
.

Definition build_safety_wit_6 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (key_written: (@list Z)) (data_written: (@list Z)) (S_prefix: (@multiset (Z * Z))) (child: Z) (key_x: Z) (i: Z) (data_x: Z) (PreH1 : (child > 0)) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix key_input data_input i )) (PreH13 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "key_x" ) )) # Int  |-> key_x)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_7 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (key_written: (@list Z)) (data_written: (@list Z)) (S_prefix: (@multiset (Z * Z))) (child: Z) (key_x: Z) (i: Z) (data_x: Z) (PreH1 : (child > 0)) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix key_input data_input i )) (PreH13 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "data_x" ) )) # Int  |-> data_x)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "key_x" ) )) # Int  |-> key_x)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition build_safety_wit_8 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_result: (@list Z)) (data_result: (@list Z)) (i: Z) (data_x: Z) (key_x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (data_x = (Znth i data_input 0))) (PreH6 : (key_x = (Znth i key_input 0))) (PreH7 : ((Zlength (key_input)) = n_pre)) (PreH8 : ((Zlength (data_input)) = n_pre)) (PreH9 : (BuildPrefixState (multiset_insert (S_prefix) ((heap_item (key_x) (data_x)))) key_input data_input (i + 1 ) )) (PreH10 : (heap_representation (multiset_insert (S_prefix) ((heap_item (key_x) (data_x)))) key_result data_result (i + 1 ) )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full key_pre (i + 1 ) key_result )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_result )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_entail_wit_1 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (key_input)) = n_pre)) (PreH4 : ((Zlength (data_input)) = n_pre)) ,
  (IntArray.full key_pre n_pre key_input )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre data_input )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  (“ (n_pre = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ”
  &&  (IntArray.full key_pre n_pre key_input )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre data_input )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity ))
  ||
  (EX (key_prefix: (@list Z))  (data_prefix: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input 1 ) ” 
  &&  “ (heap_representation S_prefix key_prefix data_prefix 1 ) ”
  &&  (IntArray.full key_pre 1 key_prefix )
  **  (IntArray.seg key_pre 1 n_pre (sublist (1) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre 1 data_prefix )
  **  (IntArray.seg data_pre 1 n_pre (sublist (1) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity ))
.

Definition build_entail_wit_2 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_prefix: (@list Z)) (data_prefix: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH9 : (heap_representation S_prefix_2 key_prefix data_prefix i )) ,
  (IntArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)) )
  **  (IntArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)) )
  **  (IntArray.full key_pre i key_prefix )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre i data_prefix )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (key_base: (@list Z))  (data_base: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Znth (i - i ) (sublist (i) (n_pre) (data_input)) 0) = (Znth i data_input 0)) ” 
  &&  “ ((Znth (i - i ) (sublist (i) (n_pre) (key_input)) 0) = (Znth i key_input 0)) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (heap_representation S_prefix key_base data_base i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i (Znth (i - i ) (sublist (i) (n_pre) (data_input)) 0) (Znth (i - i ) (sublist (i) (n_pre) (key_input)) 0) ) ” 
  &&  “ (PushLoopState key_written data_written key_written data_written i i (Znth (i - i ) (sublist (i) (n_pre) (data_input)) 0) (Znth (i - i ) (sublist (i) (n_pre) (key_input)) 0) ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_written )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_written )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
) \/
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_prefix: (@list Z)) (data_prefix: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH9 : (heap_representation S_prefix_2 key_prefix data_prefix i )) ,
  (IntArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)) )
  **  (IntArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)) )
  **  (IntArray.full key_pre i key_prefix )
  **  (IntArray.full data_pre i data_prefix )
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (key_base: (@list Z))  (data_base: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Znth (i - i ) (sublist (i) (n_pre) (data_input)) 0) = (Znth i data_input 0)) ” 
  &&  “ ((Znth (i - i ) (sublist (i) (n_pre) (key_input)) 0) = (Znth i key_input 0)) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (heap_representation S_prefix key_base data_base i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i (Znth (i - i ) (sublist (i) (n_pre) (data_input)) 0) (Znth (i - i ) (sublist (i) (n_pre) (key_input)) 0) ) ” 
  &&  “ (PushLoopState key_written data_written key_written data_written i i (Znth (i - i ) (sublist (i) (n_pre) (data_input)) 0) (Znth (i - i ) (sublist (i) (n_pre) (key_input)) 0) ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_written )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.full data_pre (i + 1 ) data_written )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
).

Definition build_entail_wit_3 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_base: (@list Z)) (data_base: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (i: Z) (data_x: Z) (key_x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (data_x = (Znth i data_input 0))) (PreH6 : (key_x = (Znth i key_input 0))) (PreH7 : ((Zlength (key_input)) = n_pre)) (PreH8 : ((Zlength (data_input)) = n_pre)) (PreH9 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH10 : (heap_representation S_prefix_2 key_base data_base i )) (PreH11 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH12 : (PushLoopState key_written_2 data_written_2 key_written_2 data_written_2 i i data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_written_2 )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_written_2 )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (key_current: (@list Z))  (data_current: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= i) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i i data_x key_x ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
) \/
(
forall (n_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_base: (@list Z)) (data_base: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (i: Z) (data_x: Z) (key_x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (data_x = (Znth i data_input 0))) (PreH6 : (key_x = (Znth i key_input 0))) (PreH7 : ((Zlength (key_input)) = n_pre)) (PreH8 : ((Zlength (data_input)) = n_pre)) (PreH9 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH10 : (heap_representation S_prefix_2 key_base data_base i )) (PreH11 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH12 : (PushLoopState key_written_2 data_written_2 key_written_2 data_written_2 i i data_x key_x )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (0 <= i) ” 
  &&  “ (i <= i) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i (Znth i data_input 0) (Znth i key_input 0) ) ” 
  &&  “ (PushLoopState key_written data_written key_written_2 data_written_2 i i (Znth i data_input 0) (Znth i key_input 0) ) ”
  &&  emp
).

Definition build_entail_wit_4 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (child: Z) (key_x: Z) (i: Z) (data_x: Z) (PreH1 : (child > 0)) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH13 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH14 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i child data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_current_2 )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current_2 )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (key_current: (@list Z))  (data_current: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= ((child - 1 ) ÷ 2 )) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < child) ” 
  &&  “ (((child - 1 ) ÷ 2 ) <= i) ” 
  &&  “ (((child - 1 ) ÷ 2 ) = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
) \/
(
forall (n_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (child: Z) (key_x: Z) (i: Z) (data_x: Z) (PreH1 : (child > 0)) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH13 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH14 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i child data_x key_x )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (0 < child) ” 
  &&  “ (0 <= ((child - 1 ) ÷ 2 )) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < child) ” 
  &&  “ (((child - 1 ) ÷ 2 ) <= i) ” 
  &&  “ (((child - 1 ) ÷ 2 ) = (heap_parent (child))) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i (Znth i data_input 0) (Znth i key_input 0) ) ” 
  &&  “ (PushLoopState key_written data_written key_current_2 data_current_2 i child (Znth i data_input 0) (Znth i key_input 0) ) ”
  &&  emp
).

Definition build_entail_wit_5 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current_2 0) <= (Znth child key_current_2 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH17 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH18 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i child data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_current_2 )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current_2 )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (data_current: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z)))  (key_current: (@list Z)) ,
  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_current 0) <= (Znth child key_current 0)) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushResult S_prefix key_current data_current i data_x key_x ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
) \/
(
forall (n_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current_2 0) <= (Znth child key_current_2 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH17 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH18 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i child data_x key_x )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i (Znth i data_input 0) (Znth i key_input 0) ) ” 
  &&  “ (PushResult S_prefix key_current_2 data_current_2 i (Znth i data_input 0) (Znth i key_input 0) ) ”
  &&  emp
).

Definition build_entail_wit_6 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH17 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH18 : (PushLoopState key_written_2 data_written_2 key_current data_current i child data_x key_x )) ,
  (IntArray.full data_pre (i + 1 ) (replace_Znth (child) ((Znth parent data_current 0)) ((replace_Znth (parent) ((Znth child data_current 0)) (data_current)))) )
  **  (IntArray.full key_pre (i + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z)))  (data_current_2: (@list Z))  (key_current_2: (@list Z)) ,
  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Znth parent key_current 0) = (Znth child key_current_2 0)) ” 
  &&  “ ((Znth parent data_current 0) = (Znth child data_current_2 0)) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current_2 data_current_2 i parent data_x key_x ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_current_2 )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current_2 )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
) \/
(
forall (n_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH17 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH18 : (PushLoopState key_written_2 data_written_2 key_current data_current i child data_x key_x )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ ((Znth (heap_parent (child)) key_current 0) = (Znth child (replace_Znth (child) ((Znth (heap_parent (child)) key_current 0)) ((replace_Znth ((heap_parent (child))) ((Znth child key_current 0)) (key_current)))) 0)) ” 
  &&  “ ((Znth (heap_parent (child)) data_current 0) = (Znth child (replace_Znth (child) ((Znth (heap_parent (child)) data_current 0)) ((replace_Znth ((heap_parent (child))) ((Znth child data_current 0)) (data_current)))) 0)) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i (Znth i data_input 0) (Znth i key_input 0) ) ” 
  &&  “ (PushLoopState key_written data_written (replace_Znth (child) ((Znth (heap_parent (child)) key_current 0)) ((replace_Znth ((heap_parent (child))) ((Znth child key_current 0)) (key_current)))) (replace_Znth (child) ((Znth (heap_parent (child)) data_current 0)) ((replace_Znth ((heap_parent (child))) ((Znth child data_current 0)) (data_current)))) i (heap_parent (child)) (Znth i data_input 0) (Znth i key_input 0) ) ”
  &&  emp
).

Definition build_entail_wit_7 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (data_x = (Znth i data_input 0))) (PreH2 : (key_x = (Znth i key_input 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 < child)) (PreH8 : (child <= i)) (PreH9 : (0 <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : (tmp_key = (Znth child key_current_2 0))) (PreH14 : (tmp_data = (Znth child data_current_2 0))) (PreH15 : ((Zlength (key_input)) = n_pre)) (PreH16 : ((Zlength (data_input)) = n_pre)) (PreH17 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH18 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH19 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i parent data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_current_2 )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current_2 )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (key_current: (@list Z))  (data_current: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent <= i) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i parent data_x key_x ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
) \/
(
forall (n_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current_2: (@list Z)) (data_current_2: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (data_x = (Znth i data_input 0))) (PreH2 : (key_x = (Znth i key_input 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 < child)) (PreH8 : (child <= i)) (PreH9 : (0 <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : (tmp_key = (Znth child key_current_2 0))) (PreH14 : (tmp_data = (Znth child data_current_2 0))) (PreH15 : ((Zlength (key_input)) = n_pre)) (PreH16 : ((Zlength (data_input)) = n_pre)) (PreH17 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH18 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH19 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i parent data_x key_x )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i (Znth i data_input 0) (Znth i key_input 0) ) ” 
  &&  “ (PushLoopState key_written data_written key_current_2 data_current_2 i (heap_parent (child)) (Znth i data_input 0) (Znth i key_input 0) ) ”
  &&  emp
).

Definition build_entail_wit_8_1 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (child: Z) (key_x: Z) (i: Z) (data_x: Z) (PreH1 : (child <= 0)) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH13 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH14 : (PushLoopState key_written_2 data_written_2 key_current data_current i child data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (key_result: (@list Z))  (data_result: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushResult S_prefix key_result data_result i data_x key_x ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_result )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_result )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
) \/
(
forall (n_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (child: Z) (key_x: Z) (i: Z) (data_x: Z) (PreH1 : (child <= 0)) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH13 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH14 : (PushLoopState key_written_2 data_written_2 key_current data_current i child data_x key_x )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i (Znth i data_input 0) (Znth i key_input 0) ) ” 
  &&  “ (PushResult S_prefix key_current data_current i (Znth i data_input 0) (Znth i key_input 0) ) ”
  &&  emp
).

Definition build_entail_wit_8_2 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : (data_x = (Znth i data_input 0))) (PreH2 : (key_x = (Znth i key_input 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 < child)) (PreH8 : (child <= i)) (PreH9 : (0 <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : ((Znth parent key_current 0) <= (Znth child key_current 0))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH17 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH18 : (PushResult S_prefix_2 key_current data_current i data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (key_result: (@list Z))  (data_result: (@list Z))  (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushResult S_prefix key_result data_result i data_x key_x ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_result )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_result )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
) \/
(
forall (n_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_written_2: (@list Z)) (data_written_2: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : (data_x = (Znth i data_input 0))) (PreH2 : (key_x = (Znth i key_input 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 < child)) (PreH8 : (child <= i)) (PreH9 : (0 <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : ((Znth parent key_current 0) <= (Znth child key_current 0))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH17 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x )) (PreH18 : (PushResult S_prefix_2 key_current data_current i data_x key_x )) ,
  TT && emp 
|--
  EX (key_written: (@list Z))  (data_written: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i (Znth i data_input 0) (Znth i key_input 0) ) ” 
  &&  “ (PushResult S_prefix key_current data_current i (Znth i data_input 0) (Znth i key_input 0) ) ”
  &&  emp
).

Definition build_entail_wit_9 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_result_2: (@list Z)) (data_result_2: (@list Z)) (i: Z) (data_x: Z) (key_x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (data_x = (Znth i data_input 0))) (PreH6 : (key_x = (Znth i key_input 0))) (PreH7 : ((Zlength (key_input)) = n_pre)) (PreH8 : ((Zlength (data_input)) = n_pre)) (PreH9 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH10 : (PushSource key_written data_written S_prefix_2 i data_x key_x )) (PreH11 : (PushResult S_prefix_2 key_result_2 data_result_2 i data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_result_2 )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_result_2 )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (key_result: (@list Z))  (data_result: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState (multiset_insert (S_prefix) ((heap_item (key_x) (data_x)))) key_input data_input (i + 1 ) ) ” 
  &&  “ (heap_representation (multiset_insert (S_prefix) ((heap_item (key_x) (data_x)))) key_result data_result (i + 1 ) ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_result )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_result )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
) \/
(
forall (n_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_result_2: (@list Z)) (data_result_2: (@list Z)) (i: Z) (data_x: Z) (key_x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (data_x = (Znth i data_input 0))) (PreH6 : (key_x = (Znth i key_input 0))) (PreH7 : ((Zlength (key_input)) = n_pre)) (PreH8 : ((Zlength (data_input)) = n_pre)) (PreH9 : (BuildPrefixState S_prefix_2 key_input data_input i )) (PreH10 : (PushSource key_written data_written S_prefix_2 i data_x key_x )) (PreH11 : (PushResult S_prefix_2 key_result_2 data_result_2 i data_x key_x )) ,
  TT && emp 
|--
  EX (S_prefix: (@multiset (Z * Z))) ,
  “ (BuildPrefixState (multiset_insert (S_prefix) ((heap_item ((Znth i key_input 0)) ((Znth i data_input 0))))) key_input data_input (i + 1 ) ) ” 
  &&  “ (heap_representation (multiset_insert (S_prefix) ((heap_item ((Znth i key_input 0)) ((Znth i data_input 0))))) key_result_2 data_result_2 (i + 1 ) ) ”
  &&  emp
).

Definition build_entail_wit_10 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_result: (@list Z)) (data_result: (@list Z)) (i: Z) (data_x: Z) (key_x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (data_x = (Znth i data_input 0))) (PreH6 : (key_x = (Znth i key_input 0))) (PreH7 : ((Zlength (key_input)) = n_pre)) (PreH8 : ((Zlength (data_input)) = n_pre)) (PreH9 : (BuildPrefixState (multiset_insert (S_prefix_2) ((heap_item (key_x) (data_x)))) key_input data_input (i + 1 ) )) (PreH10 : (heap_representation (multiset_insert (S_prefix_2) ((heap_item (key_x) (data_x)))) key_result data_result (i + 1 ) )) ,
  (IntArray.full key_pre (i + 1 ) key_result )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_result )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (key_prefix: (@list Z))  (data_prefix: (@list Z))  (S_prefix: (@multiset (Z * Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input (i + 1 ) ) ” 
  &&  “ (heap_representation S_prefix key_prefix data_prefix (i + 1 ) ) ”
  &&  (IntArray.full key_pre (i + 1 ) key_prefix )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_prefix )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
) \/
(
forall (n_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix_2: (@multiset (Z * Z))) (key_result: (@list Z)) (data_result: (@list Z)) (i: Z) (data_x: Z) (key_x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (data_x = (Znth i data_input 0))) (PreH6 : (key_x = (Znth i key_input 0))) (PreH7 : ((Zlength (key_input)) = n_pre)) (PreH8 : ((Zlength (data_input)) = n_pre)) (PreH9 : (BuildPrefixState (multiset_insert (S_prefix_2) ((heap_item (key_x) (data_x)))) key_input data_input (i + 1 ) )) (PreH10 : (heap_representation (multiset_insert (S_prefix_2) ((heap_item (key_x) (data_x)))) key_result data_result (i + 1 ) )) ,
  TT && emp 
|--
  EX (S_prefix: (@multiset (Z * Z))) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (key_input))) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input (i + 1 ) ) ” 
  &&  “ (heap_representation S_prefix key_result data_result (i + 1 ) ) ”
  &&  emp
).

Definition build_entail_wit_11_1 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)) (PreH4 : ((Zlength (key_input)) = n_pre)) (PreH5 : ((Zlength (data_input)) = n_pre)) ,
  (IntArray.full key_pre n_pre key_input )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre data_input )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre )
) \/
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)) (PreH4 : ((Zlength (key_input)) = n_pre)) (PreH5 : ((Zlength (data_input)) = n_pre)) ,
  (IntArray.full key_pre n_pre key_input )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre data_input )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre )
).

Definition build_entail_wit_11_1_split_goal_spatial := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)) (PreH4 : ((Zlength (key_input)) = n_pre)) (PreH5 : ((Zlength (data_input)) = n_pre)) ,
  (IntArray.full key_pre n_pre key_input )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre data_input )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre )
.

Definition build_entail_wit_11_2 := 
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_prefix: (@list Z)) (data_prefix: (@list Z)) (S_prefix: (@multiset (Z * Z))) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix key_input data_input i )) (PreH9 : (heap_representation S_prefix key_prefix data_prefix i )) ,
  (IntArray.full key_pre i key_prefix )
  **  (IntArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre i data_prefix )
  **  (IntArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre )
) \/
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_prefix: (@list Z)) (data_prefix: (@list Z)) (S_prefix: (@multiset (Z * Z))) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix key_input data_input i )) (PreH9 : (heap_representation S_prefix key_prefix data_prefix i )) ,
  (IntArray.full key_pre i key_prefix )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre i data_prefix )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre )
).

Definition build_entail_wit_11_2_split_goal_spatial := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_prefix: (@list Z)) (data_prefix: (@list Z)) (S_prefix: (@multiset (Z * Z))) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix key_input data_input i )) (PreH9 : (heap_representation S_prefix key_prefix data_prefix i )) ,
  (IntArray.full key_pre i key_prefix )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre i data_prefix )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre )
.

Definition build_return_wit_1 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) ,
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre )
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre )
.

Definition build_partial_solve_wit_1 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_prefix: (@list Z)) (data_prefix: (@list Z)) (S_prefix: (@multiset (Z * Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix key_input data_input i )) (PreH9 : (heap_representation S_prefix key_prefix data_prefix i )) ,
  (IntArray.full key_pre i key_prefix )
  **  (IntArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre i data_prefix )
  **  (IntArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (heap_representation S_prefix key_prefix data_prefix i ) ”
  &&  (((data_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - i ) (sublist (i) (n_pre) (data_input)) 0))
  **  (IntArray.missing_i data_pre i i n_pre (sublist (i) (n_pre) (data_input)) )
  **  (IntArray.full key_pre i key_prefix )
  **  (IntArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre i data_prefix )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_2 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (key_prefix: (@list Z)) (data_prefix: (@list Z)) (S_prefix: (@multiset (Z * Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix key_input data_input i )) (PreH9 : (heap_representation S_prefix key_prefix data_prefix i )) ,
  (IntArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)) )
  **  (IntArray.full key_pre i key_prefix )
  **  (IntArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre i data_prefix )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (heap_representation S_prefix key_prefix data_prefix i ) ”
  &&  (((key_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - i ) (sublist (i) (n_pre) (key_input)) 0))
  **  (IntArray.missing_i key_pre i i n_pre (sublist (i) (n_pre) (key_input)) )
  **  (IntArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)) )
  **  (IntArray.full key_pre i key_prefix )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre i data_prefix )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_3 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : (data_x = (Znth i data_input 0))) (PreH2 : (key_x = (Znth i key_input 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 < child)) (PreH8 : (child <= i)) (PreH9 : (0 <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : ((Zlength (key_input)) = n_pre)) (PreH14 : ((Zlength (data_input)) = n_pre)) (PreH15 : (BuildPrefixState S_prefix key_input data_input i )) (PreH16 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH17 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent key_current 0))
  **  (IntArray.missing_i key_pre parent 0 (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_4 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : (data_x = (Znth i data_input 0))) (PreH2 : (key_x = (Znth i key_input 0))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 < child)) (PreH8 : (child <= i)) (PreH9 : (0 <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : ((Zlength (key_input)) = n_pre)) (PreH14 : ((Zlength (data_input)) = n_pre)) (PreH15 : (BuildPrefixState S_prefix key_input data_input i )) (PreH16 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH17 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |-> (Znth child key_current 0))
  **  (IntArray.missing_i key_pre child 0 (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_5 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i )) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent key_current 0))
  **  (IntArray.missing_i key_pre parent 0 (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_6 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i )) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |-> (Znth child key_current 0))
  **  (IntArray.missing_i key_pre child 0 (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_7 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i )) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre parent 0 (i + 1 ) key_current )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_8 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i )) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) (replace_Znth (parent) ((Znth child key_current 0)) (key_current)) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre child 0 (i + 1 ) (replace_Znth (parent) ((Znth child key_current 0)) (key_current)) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_9 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i )) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  (IntArray.full key_pre (i + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent data_current 0))
  **  (IntArray.missing_i data_pre parent 0 (i + 1 ) data_current )
  **  (IntArray.full key_pre (i + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_10 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i )) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.full key_pre (i + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int  |-> (Znth child data_current 0))
  **  (IntArray.missing_i data_pre child 0 (i + 1 ) data_current )
  **  (IntArray.full key_pre (i + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_11 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i )) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  (IntArray.full data_pre (i + 1 ) data_current )
  **  (IntArray.full key_pre (i + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre parent 0 (i + 1 ) data_current )
  **  (IntArray.full key_pre (i + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

Definition build_partial_solve_wit_12 := 
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (data_input: (@list Z)) (key_input: (@list Z)) (S_prefix: (@multiset (Z * Z))) (key_written: (@list Z)) (data_written: (@list Z)) (key_current: (@list Z)) (data_current: (@list Z)) (data_x: Z) (i: Z) (key_x: Z) (child: Z) (parent: Z) (PreH1 : ((Znth parent key_current 0) > (Znth child key_current 0))) (PreH2 : (data_x = (Znth i data_input 0))) (PreH3 : (key_x = (Znth i key_input 0))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 < child)) (PreH9 : (child <= i)) (PreH10 : (0 <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i )) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x )) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x )) ,
  (IntArray.full data_pre (i + 1 ) (replace_Znth (parent) ((Znth child data_current 0)) (data_current)) )
  **  (IntArray.full key_pre (i + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  “ ((Znth parent key_current 0) > (Znth child key_current 0)) ” 
  &&  “ (data_x = (Znth i data_input 0)) ” 
  &&  “ (key_x = (Znth i key_input 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= i) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= i) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ ((Zlength (key_input)) = n_pre) ” 
  &&  “ ((Zlength (data_input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix key_input data_input i ) ” 
  &&  “ (PushSource key_written data_written S_prefix i data_x key_x ) ” 
  &&  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x ) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre child 0 (i + 1 ) (replace_Znth (parent) ((Znth child data_current 0)) (data_current)) )
  **  (IntArray.full key_pre (i + 1 ) (replace_Znth (child) ((Znth parent key_current 0)) ((replace_Znth (parent) ((Znth child key_current 0)) (key_current)))) )
  **  (IntArray.seg key_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (key_input)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.seg data_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (data_input)) )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
.

(*----- Function pop -----*)

Definition pop_safety_wit_1 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre )) (PreH4 : (PrefixMinimum before_key before_data n_pre popped )) (PreH5 : (multiset_minimum S_before popped )) ,
  ((( &( "result_key" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_2 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre )) (PreH4 : (PrefixMinimum before_key before_data n_pre popped )) (PreH5 : (multiset_minimum S_before popped )) ,
  ((( &( "result_data" ) )) # Int  |->_)
  **  (IntArray.full key_pre n_pre before_key )
  **  ((( &( "result_key" ) )) # Int  |-> (Znth 0 before_key 0))
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_3 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (heap_representation S_before before_key before_data n_pre )) (PreH6 : (PrefixMinimum before_key before_data n_pre popped )) (PreH7 : (multiset_minimum S_before popped )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_4 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre )) (PreH9 : (PrefixMinimum before_key before_data n_pre popped )) (PreH10 : (multiset_minimum S_before popped )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_5 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre )) (PreH9 : (PrefixMinimum before_key before_data n_pre popped )) (PreH10 : (multiset_minimum S_before popped )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_6 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre )) (PreH9 : (PrefixMinimum before_key before_data n_pre popped )) (PreH10 : (multiset_minimum S_before popped )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_7 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre )) (PreH9 : (PrefixMinimum before_key before_data n_pre popped )) (PreH10 : (multiset_minimum S_before popped )) ,
  (IntArray.full key_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before_key 0)) (before_key)) )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_8 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre )) (PreH9 : (PrefixMinimum before_key before_data n_pre popped )) (PreH10 : (multiset_minimum S_before popped )) ,
  (IntArray.full key_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before_key 0)) (before_key)) )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_9 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre )) (PreH9 : (PrefixMinimum before_key before_data n_pre popped )) (PreH10 : (multiset_minimum S_before popped )) ,
  (IntArray.full key_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before_key 0)) (before_key)) )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_10 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (heap_representation S_before before_key before_data n_pre )) (PreH6 : (PrefixMinimum before_key before_data n_pre popped )) (PreH7 : (multiset_minimum S_before popped )) (PreH8 : (PopLoopState before_key before_data current_key current_data n_pre 0 )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_11 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (0 <= ((idx * 2 ) + 1 ))) (PreH8 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre )) (PreH10 : (PrefixMinimum before_key before_data n_pre popped )) (PreH11 : (multiset_minimum S_before popped )) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_12 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (0 <= ((idx * 2 ) + 1 ))) (PreH8 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre )) (PreH10 : (PrefixMinimum before_key before_data n_pre popped )) (PreH11 : (multiset_minimum S_before popped )) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((idx * 2 ) + 1 )) ”
.

Definition pop_safety_wit_13 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (0 <= ((idx * 2 ) + 1 ))) (PreH8 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre )) (PreH10 : (PrefixMinimum before_key before_data n_pre popped )) (PreH11 : (multiset_minimum S_before popped )) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((idx * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx * 2 )) ”
.

Definition pop_safety_wit_14 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (0 <= ((idx * 2 ) + 1 ))) (PreH8 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre )) (PreH10 : (PrefixMinimum before_key before_data n_pre popped )) (PreH11 : (multiset_minimum S_before popped )) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pop_safety_wit_15 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (0 <= ((idx * 2 ) + 1 ))) (PreH8 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre )) (PreH10 : (PrefixMinimum before_key before_data n_pre popped )) (PreH11 : (multiset_minimum S_before popped )) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_16 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (0 <= ((idx * 2 ) + 1 ))) (PreH8 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre )) (PreH10 : (PrefixMinimum before_key before_data n_pre popped )) (PreH11 : (multiset_minimum S_before popped )) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_17 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (0 <= ((idx * 2 ) + 1 ))) (PreH9 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre )) (PreH11 : (PrefixMinimum before_key before_data n_pre popped )) (PreH12 : (multiset_minimum S_before popped )) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((idx * 2 ) + 1 )) ”
.

Definition pop_safety_wit_18 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (0 <= ((idx * 2 ) + 1 ))) (PreH9 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre )) (PreH11 : (PrefixMinimum before_key before_data n_pre popped )) (PreH12 : (multiset_minimum S_before popped )) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((idx * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx * 2 )) ”
.

Definition pop_safety_wit_19 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (0 <= ((idx * 2 ) + 1 ))) (PreH9 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre )) (PreH11 : (PrefixMinimum before_key before_data n_pre popped )) (PreH12 : (multiset_minimum S_before popped )) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pop_safety_wit_20 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (0 <= ((idx * 2 ) + 1 ))) (PreH9 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre )) (PreH11 : (PrefixMinimum before_key before_data n_pre popped )) (PreH12 : (multiset_minimum S_before popped )) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_21 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (0 <= ((idx * 2 ) + 1 ))) (PreH9 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre )) (PreH11 : (PrefixMinimum before_key before_data n_pre popped )) (PreH12 : (multiset_minimum S_before popped )) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> ((idx * 2 ) + 1 ))
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((((idx * 2 ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((idx * 2 ) + 1 ) + 1 )) ”
.

Definition pop_safety_wit_22 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key: (@list Z)) (current_data: (@list Z)) (before_key: (@list Z)) (before_data: (@list Z)) (idx: Z) (result_data: Z) (popped: (Z * Z)) (result_key: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (0 <= ((idx * 2 ) + 1 ))) (PreH9 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre )) (PreH11 : (PrefixMinimum before_key before_data n_pre popped )) (PreH12 : (multiset_minimum S_before popped )) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> ((idx * 2 ) + 1 ))
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_23 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (left = ((idx * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (smallest = left)) (PreH10 : (0 <= left)) (PreH11 : (left < (n_pre - 1 ))) (PreH12 : (0 <= right)) (PreH13 : (right <= (n_pre - 1 ))) (PreH14 : (heap_representation S_before before_key before_data n_pre )) (PreH15 : (PrefixMinimum before_key before_data n_pre popped )) (PreH16 : (multiset_minimum S_before popped )) (PreH17 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "smallest" ) )) # Int  |-> smallest)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_24 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (left = ((idx * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (smallest = left)) (PreH10 : (0 <= left)) (PreH11 : (left < (n_pre - 1 ))) (PreH12 : (0 <= right)) (PreH13 : (right <= (n_pre - 1 ))) (PreH14 : (heap_representation S_before before_key before_data n_pre )) (PreH15 : (PrefixMinimum before_key before_data n_pre popped )) (PreH16 : (multiset_minimum S_before popped )) (PreH17 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_out" ) )) # Ptr  |-> data_out_pre)
  **  ((( &( "key_out" ) )) # Ptr  |-> key_out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "result_key" ) )) # Int  |-> result_key)
  **  ((( &( "result_data" ) )) # Int  |-> result_data)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "smallest" ) )) # Int  |-> smallest)
  **  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_entail_wit_1 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (PreH1 : (1 <= n_pre)) ,
  (store_heap key_pre data_pre S_before n_pre )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (popped: (Z * Z))  (before_key: (@list Z))  (before_data: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (PreH1 : (1 <= n_pre)) ,
  (store_heap key_pre data_pre S_before n_pre )
|--
  EX (popped: (Z * Z))  (before_key: (@list Z))  (before_data: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
).

Definition pop_entail_wit_2 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped_2: (Z * Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre )) (PreH4 : (PrefixMinimum before_key before_data n_pre popped_2 )) (PreH5 : (multiset_minimum S_before popped_2 )) ,
  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (before_key_2: (@list Z))  (before_data_2: (@list Z))  (popped: (Z * Z)) ,
  “ ((Znth 0 before_key 0) = (item_key (popped))) ” 
  &&  “ ((Znth 0 before_data 0) = (item_data (popped))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before_key_2 before_data_2 n_pre ) ” 
  &&  “ (PrefixMinimum before_key_2 before_data_2 n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (IntArray.full key_pre n_pre before_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped_2: (Z * Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre )) (PreH4 : (PrefixMinimum before_key before_data n_pre popped_2 )) (PreH5 : (multiset_minimum S_before popped_2 )) ,
  TT && emp 
|--
  EX (popped: (Z * Z)) ,
  “ ((Znth 0 before_key 0) = (item_key (popped))) ” 
  &&  “ ((Znth 0 before_data 0) = (item_data (popped))) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  emp
).

Definition pop_entail_wit_3 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (n_pre = 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (heap_representation S_before before_key before_data n_pre )) (PreH7 : (PrefixMinimum before_key before_data n_pre popped_2 )) (PreH8 : (multiset_minimum S_before popped_2 )) ,
  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (popped: (Z * Z)) ,
  “ (n_pre = 1) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) 0 )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (n_pre = 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (heap_representation S_before before_key before_data n_pre )) (PreH7 : (PrefixMinimum before_key before_data n_pre popped_2 )) (PreH8 : (multiset_minimum S_before popped_2 )) ,
  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (popped: (Z * Z)) ,
  “ (n_pre = 1) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) 0 )
).

Definition pop_entail_wit_4 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH7 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH8 : (multiset_minimum S_before popped_2 )) ,
  (IntArray.full key_pre n_pre before_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH7 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH8 : (multiset_minimum S_before popped_2 )) ,
  TT && emp 
|--
  EX (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ (PrefixMinimum before_key_2 before_data_2 n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  emp
).

Definition pop_entail_wit_5 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH9 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH10 : (multiset_minimum S_before popped_2 )) ,
  (IntArray.full data_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before_data_2 0)) (before_data_2)) )
  **  (IntArray.full key_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before_key_2 0)) (before_key_2)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (current_key: (@list Z))  (current_data: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre 0 ) ”
  &&  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH9 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH10 : (multiset_minimum S_before popped_2 )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data (replace_Znth (0) ((Znth (n_pre - 1 ) before_key_2 0)) (before_key_2)) (replace_Znth (0) ((Znth (n_pre - 1 ) before_data_2 0)) (before_data_2)) n_pre 0 ) ”
  &&  emp
).

Definition pop_entail_wit_6 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH6 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH7 : (multiset_minimum S_before popped_2 )) (PreH8 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre 0 )) ,
  (IntArray.full key_pre n_pre current_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (current_key: (@list Z))  (current_data: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (n_pre - 1 )) ” 
  &&  “ (0 <= ((0 * 2 ) + 1 )) ” 
  &&  “ (((0 * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre 0 ) ”
  &&  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH6 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH7 : (multiset_minimum S_before popped_2 )) (PreH8 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre 0 )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (n_pre - 1 )) ” 
  &&  “ (0 <= ((0 * 2 ) + 1 )) ” 
  &&  “ (((0 * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre 0 ) ”
  &&  emp
).

Definition pop_entail_wit_7 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (idx: Z) (result_data: Z) (popped_2: (Z * Z)) (result_key: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (0 <= ((idx * 2 ) + 1 ))) (PreH9 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH11 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH12 : (multiset_minimum S_before popped_2 )) (PreH13 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (current_key: (@list Z))  (current_data: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) = ((idx * 2 ) + 1 )) ” 
  &&  “ ((((idx * 2 ) + 1 ) + 1 ) = (((idx * 2 ) + 1 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) = ((idx * 2 ) + 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (0 <= (((idx * 2 ) + 1 ) + 1 )) ” 
  &&  “ ((((idx * 2 ) + 1 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (idx: Z) (result_data: Z) (popped_2: (Z * Z)) (result_key: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (0 <= ((idx * 2 ) + 1 ))) (PreH9 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH11 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH12 : (multiset_minimum S_before popped_2 )) (PreH13 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (0 <= (((idx * 2 ) + 1 ) + 1 )) ” 
  &&  “ ((((idx * 2 ) + 1 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre idx ) ”
  &&  emp
).

Definition pop_entail_wit_8_1 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth right current_key_2 0) < (Znth left current_key_2 0))) (PreH2 : (right < (n_pre - 1 ))) (PreH3 : (result_key = (item_key (popped_2)))) (PreH4 : (result_data = (item_data (popped_2)))) (PreH5 : (1 < n_pre)) (PreH6 : (n_pre <= heap_capacity)) (PreH7 : (0 <= idx)) (PreH8 : (idx < (n_pre - 1 ))) (PreH9 : (left = ((idx * 2 ) + 1 ))) (PreH10 : (right = (left + 1 ))) (PreH11 : (smallest = left)) (PreH12 : (0 <= left)) (PreH13 : (left < (n_pre - 1 ))) (PreH14 : (0 <= right)) (PreH15 : (right <= (n_pre - 1 ))) (PreH16 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH17 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH18 : (multiset_minimum S_before popped_2 )) (PreH19 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (current_data: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (current_key: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx right ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth right current_key_2 0) < (Znth left current_key_2 0))) (PreH2 : (right < (n_pre - 1 ))) (PreH3 : (result_key = (item_key (popped_2)))) (PreH4 : (result_data = (item_data (popped_2)))) (PreH5 : (1 < n_pre)) (PreH6 : (n_pre <= heap_capacity)) (PreH7 : (0 <= idx)) (PreH8 : (idx < (n_pre - 1 ))) (PreH9 : (left = ((idx * 2 ) + 1 ))) (PreH10 : (right = (left + 1 ))) (PreH11 : (smallest = left)) (PreH12 : (0 <= left)) (PreH13 : (left < (n_pre - 1 ))) (PreH14 : (0 <= right)) (PreH15 : (right <= (n_pre - 1 ))) (PreH16 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH17 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH18 : (multiset_minimum S_before popped_2 )) (PreH19 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (PopSelectedChild current_key_2 (n_pre - 1 ) idx (left + 1 ) ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre idx ) ”
  &&  emp
).

Definition pop_entail_wit_8_2 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (right >= (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (smallest = left)) (PreH11 : (0 <= left)) (PreH12 : (left < (n_pre - 1 ))) (PreH13 : (0 <= right)) (PreH14 : (right <= (n_pre - 1 ))) (PreH15 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH16 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH17 : (multiset_minimum S_before popped_2 )) (PreH18 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (current_data: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (current_key: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (right >= (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (smallest = left)) (PreH11 : (0 <= left)) (PreH12 : (left < (n_pre - 1 ))) (PreH13 : (0 <= right)) (PreH14 : (right <= (n_pre - 1 ))) (PreH15 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH16 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH17 : (multiset_minimum S_before popped_2 )) (PreH18 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (PopSelectedChild current_key_2 (n_pre - 1 ) idx left ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre idx ) ”
  &&  emp
).

Definition pop_entail_wit_8_3 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth right current_key_2 0) >= (Znth left current_key_2 0))) (PreH2 : (right < (n_pre - 1 ))) (PreH3 : (result_key = (item_key (popped_2)))) (PreH4 : (result_data = (item_data (popped_2)))) (PreH5 : (1 < n_pre)) (PreH6 : (n_pre <= heap_capacity)) (PreH7 : (0 <= idx)) (PreH8 : (idx < (n_pre - 1 ))) (PreH9 : (left = ((idx * 2 ) + 1 ))) (PreH10 : (right = (left + 1 ))) (PreH11 : (smallest = left)) (PreH12 : (0 <= left)) (PreH13 : (left < (n_pre - 1 ))) (PreH14 : (0 <= right)) (PreH15 : (right <= (n_pre - 1 ))) (PreH16 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH17 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH18 : (multiset_minimum S_before popped_2 )) (PreH19 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (current_data: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (current_key: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth right current_key_2 0) >= (Znth left current_key_2 0))) (PreH2 : (right < (n_pre - 1 ))) (PreH3 : (result_key = (item_key (popped_2)))) (PreH4 : (result_data = (item_data (popped_2)))) (PreH5 : (1 < n_pre)) (PreH6 : (n_pre <= heap_capacity)) (PreH7 : (0 <= idx)) (PreH8 : (idx < (n_pre - 1 ))) (PreH9 : (left = ((idx * 2 ) + 1 ))) (PreH10 : (right = (left + 1 ))) (PreH11 : (smallest = left)) (PreH12 : (0 <= left)) (PreH13 : (left < (n_pre - 1 ))) (PreH14 : (0 <= right)) (PreH15 : (right <= (n_pre - 1 ))) (PreH16 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH17 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH18 : (multiset_minimum S_before popped_2 )) (PreH19 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (PopSelectedChild current_key_2 (n_pre - 1 ) idx left ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre idx ) ”
  &&  emp
).

Definition pop_entail_wit_9 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key_2 0) <= (Znth smallest current_key_2 0))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key_2 (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH14 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH15 : (multiset_minimum S_before popped_2 )) (PreH16 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (current_data: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (current_key: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ ((Znth idx current_key 0) <= (Znth smallest current_key 0)) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopReadyState before_key before_data current_key current_data n_pre popped ) ”
  &&  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key_2 0) <= (Znth smallest current_key_2 0))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key_2 (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH14 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH15 : (multiset_minimum S_before popped_2 )) (PreH16 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopReadyState before_key before_data current_key_2 current_data_2 n_pre popped ) ”
  &&  emp
).

Definition pop_entail_wit_10 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key 0) > (Znth smallest current_key 0))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH14 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH15 : (multiset_minimum S_before popped_2 )) (PreH16 : (PopLoopState before_key_2 before_data_2 current_key current_data n_pre idx )) ,
  (IntArray.full data_pre n_pre (replace_Znth (smallest) ((Znth idx current_data 0)) ((replace_Znth (idx) ((Znth smallest current_data 0)) (current_data)))) )
  **  (IntArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (current_data_2: (@list Z))  (current_key_2: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (idx < smallest) ” 
  &&  “ ((Znth idx current_key 0) = (Znth smallest current_key_2 0)) ” 
  &&  “ ((Znth idx current_data 0) = (Znth smallest current_data_2 0)) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre smallest ) ”
  &&  (IntArray.full key_pre n_pre current_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key 0) > (Znth smallest current_key 0))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH14 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH15 : (multiset_minimum S_before popped_2 )) (PreH16 : (PopLoopState before_key_2 before_data_2 current_key current_data n_pre idx )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (idx < smallest) ” 
  &&  “ ((Znth idx current_key 0) = (Znth smallest (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) 0)) ” 
  &&  “ ((Znth idx current_data 0) = (Znth smallest (replace_Znth (smallest) ((Znth idx current_data 0)) ((replace_Znth (idx) ((Znth smallest current_data 0)) (current_data)))) 0)) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) (replace_Znth (smallest) ((Znth idx current_data 0)) ((replace_Znth (idx) ((Znth smallest current_data 0)) (current_data)))) n_pre smallest ) ”
  &&  emp
).

Definition pop_entail_wit_11 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (left = ((idx * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (0 <= left)) (PreH10 : (left < (n_pre - 1 ))) (PreH11 : (0 <= right)) (PreH12 : (right <= (n_pre - 1 ))) (PreH13 : (0 <= smallest)) (PreH14 : (smallest < (n_pre - 1 ))) (PreH15 : (idx < smallest)) (PreH16 : (tmp_key = (Znth smallest current_key_2 0))) (PreH17 : (tmp_data = (Znth smallest current_data_2 0))) (PreH18 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH19 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH20 : (multiset_minimum S_before popped_2 )) (PreH21 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre smallest )) ,
  (IntArray.full key_pre n_pre current_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (current_key: (@list Z))  (current_data: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (0 <= ((smallest * 2 ) + 1 )) ” 
  &&  “ (((smallest * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre smallest ) ”
  &&  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (tmp_key: Z) (tmp_data: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (left = ((idx * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (0 <= left)) (PreH10 : (left < (n_pre - 1 ))) (PreH11 : (0 <= right)) (PreH12 : (right <= (n_pre - 1 ))) (PreH13 : (0 <= smallest)) (PreH14 : (smallest < (n_pre - 1 ))) (PreH15 : (idx < smallest)) (PreH16 : (tmp_key = (Znth smallest current_key_2 0))) (PreH17 : (tmp_data = (Znth smallest current_data_2 0))) (PreH18 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH19 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH20 : (multiset_minimum S_before popped_2 )) (PreH21 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre smallest )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (0 <= ((smallest * 2 ) + 1 )) ” 
  &&  “ (((smallest * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre smallest ) ”
  &&  emp
).

Definition pop_entail_wit_12_1 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (idx: Z) (result_data: Z) (popped_2: (Z * Z)) (result_key: Z) (PreH1 : (((idx * 2 ) + 1 ) >= (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (0 <= ((idx * 2 ) + 1 ))) (PreH9 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH11 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH12 : (multiset_minimum S_before popped_2 )) (PreH13 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (current_key: (@list Z))  (current_data: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopReadyState before_key before_data current_key current_data n_pre popped ) ”
  &&  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (idx: Z) (result_data: Z) (popped_2: (Z * Z)) (result_key: Z) (PreH1 : (((idx * 2 ) + 1 ) >= (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (0 <= ((idx * 2 ) + 1 ))) (PreH9 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH11 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH12 : (multiset_minimum S_before popped_2 )) (PreH13 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopReadyState before_key before_data current_key_2 current_data_2 n_pre popped ) ”
  &&  emp
).

Definition pop_entail_wit_12_2 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (left = ((idx * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (0 <= left)) (PreH10 : (left < (n_pre - 1 ))) (PreH11 : (0 <= right)) (PreH12 : (right <= (n_pre - 1 ))) (PreH13 : (0 <= smallest)) (PreH14 : (smallest < (n_pre - 1 ))) (PreH15 : ((Znth idx current_key_2 0) <= (Znth smallest current_key_2 0))) (PreH16 : (PopSelectedChild current_key_2 (n_pre - 1 ) idx smallest )) (PreH17 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH18 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH19 : (multiset_minimum S_before popped_2 )) (PreH20 : (PopReadyState before_key_2 before_data_2 current_key_2 current_data_2 n_pre popped_2 )) ,
  (IntArray.full key_pre n_pre current_key_2 )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data_2 )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (current_key: (@list Z))  (current_data: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopReadyState before_key before_data current_key current_data n_pre popped ) ”
  &&  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key_2: (@list Z)) (current_data_2: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (left = ((idx * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (0 <= left)) (PreH10 : (left < (n_pre - 1 ))) (PreH11 : (0 <= right)) (PreH12 : (right <= (n_pre - 1 ))) (PreH13 : (0 <= smallest)) (PreH14 : (smallest < (n_pre - 1 ))) (PreH15 : ((Znth idx current_key_2 0) <= (Znth smallest current_key_2 0))) (PreH16 : (PopSelectedChild current_key_2 (n_pre - 1 ) idx smallest )) (PreH17 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH18 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH19 : (multiset_minimum S_before popped_2 )) (PreH20 : (PopReadyState before_key_2 before_data_2 current_key_2 current_data_2 n_pre popped_2 )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopReadyState before_key before_data current_key_2 current_data_2 n_pre popped ) ”
  &&  emp
).

Definition pop_entail_wit_13 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH8 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH9 : (multiset_minimum S_before popped_2 )) (PreH10 : (PopReadyState before_key_2 before_data_2 current_key current_data n_pre popped_2 )) ,
  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (result_key_values: (@list Z))  (result_data_values: (@list Z))  (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopResult S_before before_key before_data result_key_values result_data_values n_pre popped ) ”
  &&  (IntArray.full key_pre n_pre result_key_values )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre result_data_values )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (S_before: (@multiset (Z * Z))) (before_key_2: (@list Z)) (before_data_2: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (heap_representation S_before before_key_2 before_data_2 n_pre )) (PreH8 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2 )) (PreH9 : (multiset_minimum S_before popped_2 )) (PreH10 : (PopReadyState before_key_2 before_data_2 current_key current_data n_pre popped_2 )) ,
  TT && emp 
|--
  EX (before_key: (@list Z))  (before_data: (@list Z))  (popped: (Z * Z)) ,
  “ ((item_key (popped_2)) = (item_key (popped))) ” 
  &&  “ ((item_data (popped_2)) = (item_data (popped))) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopResult S_before before_key before_data current_key current_data n_pre popped ) ”
  &&  emp
).

Definition pop_entail_wit_14 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (result_key_values: (@list Z)) (result_data_values: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (heap_representation S_before before_key before_data n_pre )) (PreH8 : (PrefixMinimum before_key before_data n_pre popped_2 )) (PreH9 : (multiset_minimum S_before popped_2 )) (PreH10 : (PopResult S_before before_key before_data result_key_values result_data_values n_pre popped_2 )) ,
  (IntArray.full key_pre n_pre result_key_values )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre result_data_values )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  EX (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1 ) )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
) \/
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (result_key_values: (@list Z)) (result_data_values: (@list Z)) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (heap_representation S_before before_key before_data n_pre )) (PreH8 : (PrefixMinimum before_key before_data n_pre popped_2 )) (PreH9 : (multiset_minimum S_before popped_2 )) (PreH10 : (PopResult S_before before_key before_data result_key_values result_data_values n_pre popped_2 )) ,
  (IntArray.full key_pre n_pre result_key_values )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre result_data_values )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
|--
  EX (popped: (Z * Z)) ,
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1 ) )
).

Definition pop_return_wit_1 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (0 <= idx)) (PreH4 : (idx < (n_pre - 1 ))) (PreH5 : (multiset_minimum S_before popped_2 )) ,
  (store_heap key_pre data_pre (multiset_remove (S_before) (popped_2)) (n_pre - 1 ) )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  EX (data_out_pre_v: Z)  (popped: (Z * Z))  (key_out_pre_v: Z) ,
  “ (key_out_pre_v = (item_key (popped))) ” 
  &&  “ (data_out_pre_v = (item_data (popped))) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  ((key_out_pre) # Int  |-> key_out_pre_v)
  **  ((data_out_pre) # Int  |-> data_out_pre_v)
  **  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1 ) )
.

Definition pop_return_wit_2 := 
(
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (n_pre = 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (multiset_minimum S_before popped_2 )) ,
  (store_heap key_pre data_pre (multiset_remove (S_before) (popped_2)) 0 )
  **  ((data_out_pre) # Int  |-> result_data)
  **  ((key_out_pre) # Int  |-> result_key)
|--
  EX (data_out_pre_v: Z)  (popped: (Z * Z))  (key_out_pre_v: Z) ,
  “ (key_out_pre_v = (item_key (popped))) ” 
  &&  “ (data_out_pre_v = (item_data (popped))) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  ((key_out_pre) # Int  |-> key_out_pre_v)
  **  ((data_out_pre) # Int  |-> data_out_pre_v)
  **  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1 ) )
) \/
(
forall (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (popped_2: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (n_pre = 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (multiset_minimum S_before popped_2 )) ,
  (store_heap key_pre data_pre (multiset_remove (S_before) (popped_2)) 0 )
|--
  EX (popped: (Z * Z)) ,
  “ (result_data = (item_data (popped))) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1 ) )
).

Definition pop_partial_solve_wit_1 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre )) (PreH4 : (PrefixMinimum before_key before_data n_pre popped )) (PreH5 : (multiset_minimum S_before popped )) ,
  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (((key_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 before_key 0))
  **  (IntArray.missing_i key_pre 0 0 n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_2 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre )) (PreH4 : (PrefixMinimum before_key before_data n_pre popped )) (PreH5 : (multiset_minimum S_before popped )) ,
  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (((data_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 before_data 0))
  **  (IntArray.missing_i data_pre 0 0 n_pre before_data )
  **  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_3 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre )) (PreH9 : (PrefixMinimum before_key before_data n_pre popped )) (PreH10 : (multiset_minimum S_before popped )) ,
  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (((key_pre + ((n_pre - 1 ) * sizeof(INT)))) # Int  |-> (Znth (n_pre - 1 ) before_key 0))
  **  (IntArray.missing_i key_pre (n_pre - 1 ) 0 n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_4 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre )) (PreH9 : (PrefixMinimum before_key before_data n_pre popped )) (PreH10 : (multiset_minimum S_before popped )) ,
  (IntArray.full key_pre n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (((key_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre 0 0 n_pre before_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_5 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre )) (PreH9 : (PrefixMinimum before_key before_data n_pre popped )) (PreH10 : (multiset_minimum S_before popped )) ,
  (IntArray.full key_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before_key 0)) (before_key)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (((data_pre + ((n_pre - 1 ) * sizeof(INT)))) # Int  |-> (Znth (n_pre - 1 ) before_data 0))
  **  (IntArray.missing_i data_pre (n_pre - 1 ) 0 n_pre before_data )
  **  (IntArray.full key_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before_key 0)) (before_key)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_6 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= (n_pre - 1 ))) (PreH6 : ((n_pre - 1 ) < n_pre)) (PreH7 : ((n_pre - 1 ) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre )) (PreH9 : (PrefixMinimum before_key before_data n_pre popped )) (PreH10 : (multiset_minimum S_before popped )) ,
  (IntArray.full data_pre n_pre before_data )
  **  (IntArray.full key_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before_key 0)) (before_key)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ”
  &&  (((data_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre 0 0 n_pre before_data )
  **  (IntArray.full key_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before_key 0)) (before_key)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_7 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (right < (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (smallest = left)) (PreH11 : (0 <= left)) (PreH12 : (left < (n_pre - 1 ))) (PreH13 : (0 <= right)) (PreH14 : (right <= (n_pre - 1 ))) (PreH15 : (heap_representation S_before before_key before_data n_pre )) (PreH16 : (PrefixMinimum before_key before_data n_pre popped )) (PreH17 : (multiset_minimum S_before popped )) (PreH18 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (right < (n_pre - 1 )) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (smallest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((key_pre + (right * sizeof(INT)))) # Int  |-> (Znth right current_key 0))
  **  (IntArray.missing_i key_pre right 0 n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_8 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (right < (n_pre - 1 ))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (smallest = left)) (PreH11 : (0 <= left)) (PreH12 : (left < (n_pre - 1 ))) (PreH13 : (0 <= right)) (PreH14 : (right <= (n_pre - 1 ))) (PreH15 : (heap_representation S_before before_key before_data n_pre )) (PreH16 : (PrefixMinimum before_key before_data n_pre popped )) (PreH17 : (multiset_minimum S_before popped )) (PreH18 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (right < (n_pre - 1 )) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (smallest = left) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (n_pre - 1 )) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= (n_pre - 1 )) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((key_pre + (left * sizeof(INT)))) # Int  |-> (Znth left current_key 0))
  **  (IntArray.missing_i key_pre left 0 n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_9 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (left = ((idx * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (0 <= smallest)) (PreH10 : (smallest < (n_pre - 1 ))) (PreH11 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH12 : (heap_representation S_before before_key before_data n_pre )) (PreH13 : (PrefixMinimum before_key before_data n_pre popped )) (PreH14 : (multiset_minimum S_before popped )) (PreH15 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((key_pre + (idx * sizeof(INT)))) # Int  |-> (Znth idx current_key 0))
  **  (IntArray.missing_i key_pre idx 0 n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_10 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (0 <= idx)) (PreH6 : (idx < (n_pre - 1 ))) (PreH7 : (left = ((idx * 2 ) + 1 ))) (PreH8 : (right = (left + 1 ))) (PreH9 : (0 <= smallest)) (PreH10 : (smallest < (n_pre - 1 ))) (PreH11 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH12 : (heap_representation S_before before_key before_data n_pre )) (PreH13 : (PrefixMinimum before_key before_data n_pre popped )) (PreH14 : (multiset_minimum S_before popped )) (PreH15 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int  |-> (Znth smallest current_key 0))
  **  (IntArray.missing_i key_pre smallest 0 n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_11 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key 0) > (Znth smallest current_key 0))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key before_data n_pre )) (PreH14 : (PrefixMinimum before_key before_data n_pre popped )) (PreH15 : (multiset_minimum S_before popped )) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((Znth idx current_key 0) > (Znth smallest current_key 0)) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((key_pre + (idx * sizeof(INT)))) # Int  |-> (Znth idx current_key 0))
  **  (IntArray.missing_i key_pre idx 0 n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_12 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key 0) > (Znth smallest current_key 0))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key before_data n_pre )) (PreH14 : (PrefixMinimum before_key before_data n_pre popped )) (PreH15 : (multiset_minimum S_before popped )) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((Znth idx current_key 0) > (Znth smallest current_key 0)) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int  |-> (Znth smallest current_key 0))
  **  (IntArray.missing_i key_pre smallest 0 n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_13 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key 0) > (Znth smallest current_key 0))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key before_data n_pre )) (PreH14 : (PrefixMinimum before_key before_data n_pre popped )) (PreH15 : (multiset_minimum S_before popped )) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full key_pre n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((Znth idx current_key 0) > (Znth smallest current_key 0)) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((key_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre idx 0 n_pre current_key )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_14 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key 0) > (Znth smallest current_key 0))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key before_data n_pre )) (PreH14 : (PrefixMinimum before_key before_data n_pre popped )) (PreH15 : (multiset_minimum S_before popped )) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full key_pre n_pre (replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((Znth idx current_key 0) > (Znth smallest current_key 0)) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre smallest 0 n_pre (replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_15 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key 0) > (Znth smallest current_key 0))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key before_data n_pre )) (PreH14 : (PrefixMinimum before_key before_data n_pre popped )) (PreH15 : (multiset_minimum S_before popped )) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((Znth idx current_key 0) > (Znth smallest current_key 0)) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((data_pre + (idx * sizeof(INT)))) # Int  |-> (Znth idx current_data 0))
  **  (IntArray.missing_i data_pre idx 0 n_pre current_data )
  **  (IntArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_16 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key 0) > (Znth smallest current_key 0))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key before_data n_pre )) (PreH14 : (PrefixMinimum before_key before_data n_pre popped )) (PreH15 : (multiset_minimum S_before popped )) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((Znth idx current_key 0) > (Znth smallest current_key 0)) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((data_pre + (smallest * sizeof(INT)))) # Int  |-> (Znth smallest current_data 0))
  **  (IntArray.missing_i data_pre smallest 0 n_pre current_data )
  **  (IntArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_17 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key 0) > (Znth smallest current_key 0))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key before_data n_pre )) (PreH14 : (PrefixMinimum before_key before_data n_pre popped )) (PreH15 : (multiset_minimum S_before popped )) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full data_pre n_pre current_data )
  **  (IntArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((Znth idx current_key 0) > (Znth smallest current_key 0)) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((data_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre idx 0 n_pre current_data )
  **  (IntArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Definition pop_partial_solve_wit_18 := 
forall (key_out_pre: Z) (data_out_pre: Z) (n_pre: Z) (data_pre: Z) (key_pre: Z) (S_before: (@multiset (Z * Z))) (before_key: (@list Z)) (before_data: (@list Z)) (current_key: (@list Z)) (current_data: (@list Z)) (popped: (Z * Z)) (result_key: Z) (result_data: Z) (idx: Z) (left: Z) (right: Z) (smallest: Z) (PreH1 : ((Znth idx current_key 0) > (Znth smallest current_key 0))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (0 <= idx)) (PreH7 : (idx < (n_pre - 1 ))) (PreH8 : (left = ((idx * 2 ) + 1 ))) (PreH9 : (right = (left + 1 ))) (PreH10 : (0 <= smallest)) (PreH11 : (smallest < (n_pre - 1 ))) (PreH12 : (PopSelectedChild current_key (n_pre - 1 ) idx smallest )) (PreH13 : (heap_representation S_before before_key before_data n_pre )) (PreH14 : (PrefixMinimum before_key before_data n_pre popped )) (PreH15 : (multiset_minimum S_before popped )) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx )) ,
  (IntArray.full data_pre n_pre (replace_Znth (idx) ((Znth smallest current_data 0)) (current_data)) )
  **  (IntArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
|--
  “ ((Znth idx current_key 0) > (Znth smallest current_key 0)) ” 
  &&  “ (result_key = (item_key (popped))) ” 
  &&  “ (result_data = (item_data (popped))) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= smallest) ” 
  &&  “ (smallest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current_key (n_pre - 1 ) idx smallest ) ” 
  &&  “ (heap_representation S_before before_key before_data n_pre ) ” 
  &&  “ (PrefixMinimum before_key before_data n_pre popped ) ” 
  &&  “ (multiset_minimum S_before popped ) ” 
  &&  “ (PopLoopState before_key before_data current_key current_data n_pre idx ) ”
  &&  (((data_pre + (smallest * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i data_pre smallest 0 n_pre (replace_Znth (idx) ((Znth smallest current_data 0)) (current_data)) )
  **  (IntArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key 0)) ((replace_Znth (idx) ((Znth smallest current_key 0)) (current_key)))) )
  **  (IntArray.undef_seg key_pre n_pre heap_capacity )
  **  (IntArray.undef_seg data_pre n_pre heap_capacity )
  **  ((data_out_pre) # Int  |->_)
  **  ((key_out_pre) # Int  |->_)
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_push_safety_wit_1 : push_safety_wit_1.
Axiom proof_of_push_safety_wit_2 : push_safety_wit_2.
Axiom proof_of_push_safety_wit_3 : push_safety_wit_3.
Axiom proof_of_push_safety_wit_4 : push_safety_wit_4.
Axiom proof_of_push_safety_wit_5 : push_safety_wit_5.
Axiom proof_of_push_entail_wit_1 : push_entail_wit_1.
Axiom proof_of_push_entail_wit_2 : push_entail_wit_2.
Axiom proof_of_push_entail_wit_3 : push_entail_wit_3.
Axiom proof_of_push_entail_wit_4 : push_entail_wit_4.
Axiom proof_of_push_entail_wit_5 : push_entail_wit_5.
Axiom proof_of_push_entail_wit_6 : push_entail_wit_6.
Axiom proof_of_push_entail_wit_7 : push_entail_wit_7.
Axiom proof_of_push_entail_wit_8 : push_entail_wit_8.
Axiom proof_of_push_entail_wit_9_1 : push_entail_wit_9_1.
Axiom proof_of_push_entail_wit_9_2 : push_entail_wit_9_2.
Axiom proof_of_push_entail_wit_10 : push_entail_wit_10.
Axiom proof_of_push_return_wit_1 : push_return_wit_1.
Axiom proof_of_push_partial_solve_wit_1 : push_partial_solve_wit_1.
Axiom proof_of_push_partial_solve_wit_2 : push_partial_solve_wit_2.
Axiom proof_of_push_partial_solve_wit_3 : push_partial_solve_wit_3.
Axiom proof_of_push_partial_solve_wit_4 : push_partial_solve_wit_4.
Axiom proof_of_push_partial_solve_wit_5 : push_partial_solve_wit_5.
Axiom proof_of_push_partial_solve_wit_6 : push_partial_solve_wit_6.
Axiom proof_of_push_partial_solve_wit_7 : push_partial_solve_wit_7.
Axiom proof_of_push_partial_solve_wit_8 : push_partial_solve_wit_8.
Axiom proof_of_push_partial_solve_wit_9 : push_partial_solve_wit_9.
Axiom proof_of_push_partial_solve_wit_10 : push_partial_solve_wit_10.
Axiom proof_of_push_partial_solve_wit_11 : push_partial_solve_wit_11.
Axiom proof_of_push_partial_solve_wit_12 : push_partial_solve_wit_12.
Axiom proof_of_build_safety_wit_1 : build_safety_wit_1.
Axiom proof_of_build_safety_wit_2 : build_safety_wit_2.
Axiom proof_of_build_safety_wit_3 : build_safety_wit_3.
Axiom proof_of_build_safety_wit_4 : build_safety_wit_4.
Axiom proof_of_build_safety_wit_5 : build_safety_wit_5.
Axiom proof_of_build_safety_wit_6 : build_safety_wit_6.
Axiom proof_of_build_safety_wit_7 : build_safety_wit_7.
Axiom proof_of_build_safety_wit_8 : build_safety_wit_8.
Axiom proof_of_build_entail_wit_1 : build_entail_wit_1.
Axiom proof_of_build_entail_wit_2 : build_entail_wit_2.
Axiom proof_of_build_entail_wit_3 : build_entail_wit_3.
Axiom proof_of_build_entail_wit_4 : build_entail_wit_4.
Axiom proof_of_build_entail_wit_5 : build_entail_wit_5.
Axiom proof_of_build_entail_wit_6 : build_entail_wit_6.
Axiom proof_of_build_entail_wit_7 : build_entail_wit_7.
Axiom proof_of_build_entail_wit_8_1 : build_entail_wit_8_1.
Axiom proof_of_build_entail_wit_8_2 : build_entail_wit_8_2.
Axiom proof_of_build_entail_wit_9 : build_entail_wit_9.
Axiom proof_of_build_entail_wit_10 : build_entail_wit_10.
Axiom proof_of_build_entail_wit_11_1 : build_entail_wit_11_1.
Axiom proof_of_build_entail_wit_11_2 : build_entail_wit_11_2.
Axiom proof_of_build_return_wit_1 : build_return_wit_1.
Axiom proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1.
Axiom proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2.
Axiom proof_of_build_partial_solve_wit_3 : build_partial_solve_wit_3.
Axiom proof_of_build_partial_solve_wit_4 : build_partial_solve_wit_4.
Axiom proof_of_build_partial_solve_wit_5 : build_partial_solve_wit_5.
Axiom proof_of_build_partial_solve_wit_6 : build_partial_solve_wit_6.
Axiom proof_of_build_partial_solve_wit_7 : build_partial_solve_wit_7.
Axiom proof_of_build_partial_solve_wit_8 : build_partial_solve_wit_8.
Axiom proof_of_build_partial_solve_wit_9 : build_partial_solve_wit_9.
Axiom proof_of_build_partial_solve_wit_10 : build_partial_solve_wit_10.
Axiom proof_of_build_partial_solve_wit_11 : build_partial_solve_wit_11.
Axiom proof_of_build_partial_solve_wit_12 : build_partial_solve_wit_12.
Axiom proof_of_pop_safety_wit_1 : pop_safety_wit_1.
Axiom proof_of_pop_safety_wit_2 : pop_safety_wit_2.
Axiom proof_of_pop_safety_wit_3 : pop_safety_wit_3.
Axiom proof_of_pop_safety_wit_4 : pop_safety_wit_4.
Axiom proof_of_pop_safety_wit_5 : pop_safety_wit_5.
Axiom proof_of_pop_safety_wit_6 : pop_safety_wit_6.
Axiom proof_of_pop_safety_wit_7 : pop_safety_wit_7.
Axiom proof_of_pop_safety_wit_8 : pop_safety_wit_8.
Axiom proof_of_pop_safety_wit_9 : pop_safety_wit_9.
Axiom proof_of_pop_safety_wit_10 : pop_safety_wit_10.
Axiom proof_of_pop_safety_wit_11 : pop_safety_wit_11.
Axiom proof_of_pop_safety_wit_12 : pop_safety_wit_12.
Axiom proof_of_pop_safety_wit_13 : pop_safety_wit_13.
Axiom proof_of_pop_safety_wit_14 : pop_safety_wit_14.
Axiom proof_of_pop_safety_wit_15 : pop_safety_wit_15.
Axiom proof_of_pop_safety_wit_16 : pop_safety_wit_16.
Axiom proof_of_pop_safety_wit_17 : pop_safety_wit_17.
Axiom proof_of_pop_safety_wit_18 : pop_safety_wit_18.
Axiom proof_of_pop_safety_wit_19 : pop_safety_wit_19.
Axiom proof_of_pop_safety_wit_20 : pop_safety_wit_20.
Axiom proof_of_pop_safety_wit_21 : pop_safety_wit_21.
Axiom proof_of_pop_safety_wit_22 : pop_safety_wit_22.
Axiom proof_of_pop_safety_wit_23 : pop_safety_wit_23.
Axiom proof_of_pop_safety_wit_24 : pop_safety_wit_24.
Axiom proof_of_pop_entail_wit_1 : pop_entail_wit_1.
Axiom proof_of_pop_entail_wit_2 : pop_entail_wit_2.
Axiom proof_of_pop_entail_wit_3 : pop_entail_wit_3.
Axiom proof_of_pop_entail_wit_4 : pop_entail_wit_4.
Axiom proof_of_pop_entail_wit_5 : pop_entail_wit_5.
Axiom proof_of_pop_entail_wit_6 : pop_entail_wit_6.
Axiom proof_of_pop_entail_wit_7 : pop_entail_wit_7.
Axiom proof_of_pop_entail_wit_8_1 : pop_entail_wit_8_1.
Axiom proof_of_pop_entail_wit_8_2 : pop_entail_wit_8_2.
Axiom proof_of_pop_entail_wit_8_3 : pop_entail_wit_8_3.
Axiom proof_of_pop_entail_wit_9 : pop_entail_wit_9.
Axiom proof_of_pop_entail_wit_10 : pop_entail_wit_10.
Axiom proof_of_pop_entail_wit_11 : pop_entail_wit_11.
Axiom proof_of_pop_entail_wit_12_1 : pop_entail_wit_12_1.
Axiom proof_of_pop_entail_wit_12_2 : pop_entail_wit_12_2.
Axiom proof_of_pop_entail_wit_13 : pop_entail_wit_13.
Axiom proof_of_pop_entail_wit_14 : pop_entail_wit_14.
Axiom proof_of_pop_return_wit_1 : pop_return_wit_1.
Axiom proof_of_pop_return_wit_2 : pop_return_wit_2.
Axiom proof_of_pop_partial_solve_wit_1 : pop_partial_solve_wit_1.
Axiom proof_of_pop_partial_solve_wit_2 : pop_partial_solve_wit_2.
Axiom proof_of_pop_partial_solve_wit_3 : pop_partial_solve_wit_3.
Axiom proof_of_pop_partial_solve_wit_4 : pop_partial_solve_wit_4.
Axiom proof_of_pop_partial_solve_wit_5 : pop_partial_solve_wit_5.
Axiom proof_of_pop_partial_solve_wit_6 : pop_partial_solve_wit_6.
Axiom proof_of_pop_partial_solve_wit_7 : pop_partial_solve_wit_7.
Axiom proof_of_pop_partial_solve_wit_8 : pop_partial_solve_wit_8.
Axiom proof_of_pop_partial_solve_wit_9 : pop_partial_solve_wit_9.
Axiom proof_of_pop_partial_solve_wit_10 : pop_partial_solve_wit_10.
Axiom proof_of_pop_partial_solve_wit_11 : pop_partial_solve_wit_11.
Axiom proof_of_pop_partial_solve_wit_12 : pop_partial_solve_wit_12.
Axiom proof_of_pop_partial_solve_wit_13 : pop_partial_solve_wit_13.
Axiom proof_of_pop_partial_solve_wit_14 : pop_partial_solve_wit_14.
Axiom proof_of_pop_partial_solve_wit_15 : pop_partial_solve_wit_15.
Axiom proof_of_pop_partial_solve_wit_16 : pop_partial_solve_wit_16.
Axiom proof_of_pop_partial_solve_wit_17 : pop_partial_solve_wit_17.
Axiom proof_of_pop_partial_solve_wit_18 : pop_partial_solve_wit_18.

End VC_Correct.
