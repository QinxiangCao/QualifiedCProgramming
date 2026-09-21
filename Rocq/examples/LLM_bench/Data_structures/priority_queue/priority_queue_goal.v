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
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib.
Local Open Scope sac.

(*----- Function push -----*)

Definition push_safety_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (written: (@list Z)) (child: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 <= child)) (PreH4 : (child <= n_pre)) (PreH5 : (PushSource written S_before n_pre x_pre )) (PreH6 : (PushLoopState written current n_pre child x_pre )) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition push_safety_wit_2 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (written: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre )) (PreH7 : (PushLoopState written current n_pre child x_pre )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  “ (((child - 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition push_safety_wit_3 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (written: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre )) (PreH7 : (PushLoopState written current n_pre child x_pre )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  “ ((child - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (child - 1 )) ”
.

Definition push_safety_wit_4 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (written: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre )) (PreH7 : (PushLoopState written current n_pre child x_pre )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition push_safety_wit_5 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (written: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre )) (PreH7 : (PushLoopState written current n_pre child x_pre )) ,
  ((( &( "parent" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "child" ) )) # Int  |-> child)
  **  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition push_entail_wit_1 := 
(
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) ,
  (((heap_pre + (n_pre * sizeof(INT)))) # Int  |-> x_pre)
  **  (store_heap heap_pre S_before n_pre )
|--
  EX (current: (@list Z))  (written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current n_pre n_pre x_pre ) ”
  &&  (IntArray.full heap_pre (n_pre + 1 ) current )
) \/
(
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (x_pre >= INT_MIN)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < heap_capacity)) ,
  (((heap_pre + (n_pre * sizeof(INT)))) # Int  |-> x_pre)
  **  (store_heap heap_pre S_before n_pre )
|--
  EX (current: (@list Z))  (written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current n_pre n_pre x_pre ) ”
  &&  (IntArray.full heap_pre (n_pre + 1 ) current )
).

Definition push_entail_wit_2 := 
(
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current_2: (@list Z)) (written_2: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written_2 S_before n_pre x_pre )) (PreH7 : (PushLoopState written_2 current_2 n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current_2 )
|--
  EX (current: (@list Z))  (written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= ((child - 1 ) ÷ 2 )) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < child) ” 
  &&  “ (((child - 1 ) ÷ 2 ) <= n_pre) ” 
  &&  “ (((child - 1 ) ÷ 2 ) = (heap_parent (child))) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current n_pre child x_pre ) ”
  &&  (IntArray.full heap_pre (n_pre + 1 ) current )
) \/
(
forall (x_pre: Z) (n_pre: Z) (S_before: (@multiset Z)) (current_2: (@list Z)) (written_2: (@list Z)) (child: Z) (PreH1 : (child > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written_2 S_before n_pre x_pre )) (PreH7 : (PushLoopState written_2 current_2 n_pre child x_pre )) ,
  TT && emp 
|--
  EX (written: (@list Z)) ,
  “ (0 < child) ” 
  &&  “ (0 <= ((child - 1 ) ÷ 2 )) ” 
  &&  “ (((child - 1 ) ÷ 2 ) < child) ” 
  &&  “ (((child - 1 ) ÷ 2 ) <= n_pre) ” 
  &&  “ (((child - 1 ) ÷ 2 ) = (heap_parent (child))) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current_2 n_pre child x_pre ) ”
  &&  emp
).

Definition push_entail_wit_3 := 
(
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (written_2: (@list Z)) (current_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent current_2 0) < (Znth child current_2 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written_2 S_before n_pre x_pre )) (PreH11 : (PushLoopState written_2 current_2 n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) (replace_Znth (child) ((Znth parent current_2 0)) ((replace_Znth (parent) ((Znth child current_2 0)) (current_2)))) )
|--
  EX (current: (@list Z))  (written: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current n_pre parent x_pre ) ”
  &&  (IntArray.full heap_pre (n_pre + 1 ) current )
) \/
(
forall (x_pre: Z) (n_pre: Z) (S_before: (@multiset Z)) (written_2: (@list Z)) (current_2: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent current_2 0) < (Znth child current_2 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written_2 S_before n_pre x_pre )) (PreH11 : (PushLoopState written_2 current_2 n_pre child x_pre )) ,
  TT && emp 
|--
  EX (written: (@list Z)) ,
  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written (replace_Znth (child) ((Znth (heap_parent (child)) current_2 0)) ((replace_Znth ((heap_parent (child))) ((Znth child current_2 0)) (current_2)))) n_pre (heap_parent (child)) x_pre ) ”
  &&  emp
).

Definition push_return_wit_1 := 
(
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (written: (@list Z)) (child: Z) (PreH1 : (child <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre )) (PreH7 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1 ) )
) \/
(
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (written: (@list Z)) (child: Z) (PreH1 : (child <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre )) (PreH7 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1 ) )
).

Definition push_return_wit_1_split_goal_spatial := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (written: (@list Z)) (child: Z) (PreH1 : (child <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource written S_before n_pre x_pre )) (PreH7 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1 ) )
.

Definition push_return_wit_2 := 
(
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (written: (@list Z)) (current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent current 0) >= (Znth child current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre )) (PreH11 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1 ) )
) \/
(
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (written: (@list Z)) (current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent current 0) >= (Znth child current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre )) (PreH11 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1 ) )
).

Definition push_return_wit_2_split_goal_spatial := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (written: (@list Z)) (current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent current 0) >= (Znth child current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre )) (PreH11 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  (store_heap heap_pre (multiset_insert (S_before) (x_pre)) (n_pre + 1 ) )
.

Definition push_partial_solve_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) ,
  (store_heap heap_pre S_before n_pre )
  **  (IntArray.undef_seg heap_pre n_pre (n_pre + 1 ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ”
  &&  (((heap_pre + (n_pre * sizeof(INT)))) # Int  |->_)
  **  (store_heap heap_pre S_before n_pre )
.

Definition push_partial_solve_wit_2 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (written: (@list Z)) (current: (@list Z)) (child: Z) (parent: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child <= n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (PushSource written S_before n_pre x_pre )) (PreH10 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current n_pre child x_pre ) ”
  &&  (((heap_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent current 0))
  **  (IntArray.missing_i heap_pre parent 0 (n_pre + 1 ) current )
.

Definition push_partial_solve_wit_3 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (written: (@list Z)) (current: (@list Z)) (child: Z) (parent: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (0 < child)) (PreH4 : (child <= n_pre)) (PreH5 : (0 <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (PushSource written S_before n_pre x_pre )) (PreH10 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current n_pre child x_pre ) ”
  &&  (((heap_pre + (child * sizeof(INT)))) # Int  |-> (Znth child current 0))
  **  (IntArray.missing_i heap_pre child 0 (n_pre + 1 ) current )
.

Definition push_partial_solve_wit_4 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (written: (@list Z)) (current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent current 0) < (Znth child current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre )) (PreH11 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  “ ((Znth parent current 0) < (Znth child current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current n_pre child x_pre ) ”
  &&  (((heap_pre + (parent * sizeof(INT)))) # Int  |-> (Znth parent current 0))
  **  (IntArray.missing_i heap_pre parent 0 (n_pre + 1 ) current )
.

Definition push_partial_solve_wit_5 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (written: (@list Z)) (current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent current 0) < (Znth child current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre )) (PreH11 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  “ ((Znth parent current 0) < (Znth child current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current n_pre child x_pre ) ”
  &&  (((heap_pre + (child * sizeof(INT)))) # Int  |-> (Znth child current 0))
  **  (IntArray.missing_i heap_pre child 0 (n_pre + 1 ) current )
.

Definition push_partial_solve_wit_6 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (written: (@list Z)) (current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent current 0) < (Znth child current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre )) (PreH11 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) current )
|--
  “ ((Znth parent current 0) < (Znth child current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current n_pre child x_pre ) ”
  &&  (((heap_pre + (parent * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i heap_pre parent 0 (n_pre + 1 ) current )
.

Definition push_partial_solve_wit_7 := 
forall (x_pre: Z) (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (written: (@list Z)) (current: (@list Z)) (child: Z) (parent: Z) (PreH1 : ((Znth parent current 0) < (Znth child current 0))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : (0 < child)) (PreH5 : (child <= n_pre)) (PreH6 : (0 <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource written S_before n_pre x_pre )) (PreH11 : (PushLoopState written current n_pre child x_pre )) ,
  (IntArray.full heap_pre (n_pre + 1 ) (replace_Znth (parent) ((Znth child current 0)) (current)) )
|--
  “ ((Znth parent current 0) < (Znth child current 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < heap_capacity) ” 
  &&  “ (0 < child) ” 
  &&  “ (child <= n_pre) ” 
  &&  “ (0 <= parent) ” 
  &&  “ (parent < child) ” 
  &&  “ (parent <= n_pre) ” 
  &&  “ (parent = (heap_parent (child))) ” 
  &&  “ (PushSource written S_before n_pre x_pre ) ” 
  &&  “ (PushLoopState written current n_pre child x_pre ) ”
  &&  (((heap_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i heap_pre child 0 (n_pre + 1 ) (replace_Znth (parent) ((Znth child current 0)) (current)) )
.

(*----- Function build -----*)

Definition build_safety_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full heap_pre n_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_2 := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full heap_pre n_pre input )
|--
  “ False ”
.

Definition build_safety_wit_3 := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (S_prefix: (@multiset Z)) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i )) ,
  (store_heap heap_pre (multiset_insert (S_prefix) (x)) (i + 1 ) )
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_entail_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (IntArray.full heap_pre n_pre input )
|--
  (“ (n_pre = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((Zlength (input)) = n_pre) ”
  &&  (IntArray.full heap_pre n_pre input ))
  ||
  (EX (S_prefix: (@multiset Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix input 1 ) ”
  &&  (store_heap heap_pre S_prefix 1 )
  **  (IntArray.seg heap_pre 1 n_pre (sublist (1) (n_pre) (input)) ))
.

Definition build_entail_wit_2 := 
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (S_prefix_2: (@multiset Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i )) ,
  (IntArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)) )
  **  (store_heap heap_pre S_prefix_2 i )
|--
  EX (S_prefix: (@multiset Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Znth (i - i ) (sublist (i) (n_pre) (input)) 0) = (Znth i input 0)) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix input i ) ”
  &&  (store_heap heap_pre S_prefix i )
  **  (IntArray.undef_seg heap_pre i (i + 1 ) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
) \/
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (S_prefix_2: (@multiset Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i )) ,
  (IntArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)) )
  **  (store_heap heap_pre S_prefix_2 i )
|--
  EX (S_prefix: (@multiset Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Znth (i - i ) (sublist (i) (n_pre) (input)) 0) = (Znth i input 0)) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix input i ) ”
  &&  (store_heap heap_pre S_prefix i )
  **  (IntArray.undef_seg heap_pre i (i + 1 ) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
).

Definition build_entail_wit_3 := 
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (S_prefix_2: (@multiset Z)) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i )) ,
  (store_heap heap_pre (multiset_insert (S_prefix_2) (x)) (i + 1 ) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
|--
  EX (S_prefix: (@multiset Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix input (i + 1 ) ) ”
  &&  (store_heap heap_pre S_prefix (i + 1 ) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (S_prefix_2: (@multiset Z)) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i )) ,
  TT && emp 
|--
  “ (BuildPrefixState (multiset_insert (S_prefix_2) (x)) input (i + 1 ) ) ”
  &&  emp
).

Definition build_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (S_prefix_2: (@multiset Z)) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix_2 input i )) ,
  (BuildPrefixState (multiset_insert (S_prefix_2) (x)) input (i + 1 ) )
.

Definition build_return_wit_1 := 
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  (IntArray.full heap_pre n_pre input )
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre )
) \/
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  (IntArray.full heap_pre n_pre input )
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre )
).

Definition build_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)) (PreH4 : ((Zlength (input)) = n_pre)) ,
  (IntArray.full heap_pre n_pre input )
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre )
.

Definition build_return_wit_2 := 
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (S_prefix: (@multiset Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i )) ,
  (store_heap heap_pre S_prefix i )
  **  (IntArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)) )
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre )
) \/
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (S_prefix: (@multiset Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i )) ,
  (store_heap heap_pre S_prefix i )
  **  (IntArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)) )
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre )
).

Definition build_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (S_prefix: (@multiset Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i )) ,
  (store_heap heap_pre S_prefix i )
  **  (IntArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)) )
|--
  (store_heap heap_pre (list_to_multiset (input)) n_pre )
.

Definition build_partial_solve_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (S_prefix: (@multiset Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i )) ,
  (store_heap heap_pre S_prefix i )
  **  (IntArray.seg heap_pre i n_pre (sublist (i) (n_pre) (input)) )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix input i ) ”
  &&  (((heap_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - i ) (sublist (i) (n_pre) (input)) 0))
  **  (IntArray.missing_i heap_pre i i n_pre (sublist (i) (n_pre) (input)) )
  **  (store_heap heap_pre S_prefix i )
.

Definition build_partial_solve_wit_2_pure := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (S_prefix: (@multiset Z)) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i )) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (store_heap heap_pre S_prefix i )
  **  (IntArray.undef_seg heap_pre i (i + 1 ) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < heap_capacity) ”
.

Definition build_partial_solve_wit_2_aux := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (S_prefix: (@multiset Z)) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildPrefixState S_prefix input i )) ,
  (store_heap heap_pre S_prefix i )
  **  (IntArray.undef_seg heap_pre i (i + 1 ) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < heap_capacity) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (x = (Znth i input 0)) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (BuildPrefixState S_prefix input i ) ”
  &&  (store_heap heap_pre S_prefix i )
  **  (IntArray.undef_seg heap_pre i (i + 1 ) )
  **  (IntArray.seg heap_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
.

Definition build_partial_solve_wit_2 := build_partial_solve_wit_2_pure -> build_partial_solve_wit_2_aux.

(*----- Function pop -----*)

Definition pop_safety_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before n_pre )) (PreH4 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH5 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH6 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full heap_pre n_pre before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_2 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before n_pre )) (PreH4 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH5 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH6 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre before )
  **  ((( &( "ret" ) )) # Int  |-> (Znth 0 before 0))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_3 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre before )
  **  ((( &( "ret" ) )) # Int  |-> (Znth 0 before 0))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_4 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre before )
  **  ((( &( "ret" ) )) # Int  |-> (Znth 0 before 0))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_5 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre before )
  **  ((( &( "ret" ) )) # Int  |-> (Znth 0 before 0))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_6 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  (IntArray.full heap_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before 0)) (before)) )
  **  ((( &( "ret" ) )) # Int  |-> (Znth 0 before 0))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pop_safety_wit_7 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth 0 before 0))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre )) (PreH6 : (PrefixMaximum before n_pre ret )) (PreH7 : (multiset_maximum S_before ret )) (PreH8 : (0 <= idx)) (PreH9 : (idx < (n_pre - 1 ))) (PreH10 : (0 <= ((idx * 2 ) + 1 ))) (PreH11 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx )) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_8 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth 0 before 0))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre )) (PreH6 : (PrefixMaximum before n_pre ret )) (PreH7 : (multiset_maximum S_before ret )) (PreH8 : (0 <= idx)) (PreH9 : (idx < (n_pre - 1 ))) (PreH10 : (0 <= ((idx * 2 ) + 1 ))) (PreH11 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx )) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((idx * 2 ) + 1 )) ”
.

Definition pop_safety_wit_9 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth 0 before 0))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre )) (PreH6 : (PrefixMaximum before n_pre ret )) (PreH7 : (multiset_maximum S_before ret )) (PreH8 : (0 <= idx)) (PreH9 : (idx < (n_pre - 1 ))) (PreH10 : (0 <= ((idx * 2 ) + 1 ))) (PreH11 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx )) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ ((idx * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx * 2 )) ”
.

Definition pop_safety_wit_10 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth 0 before 0))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre )) (PreH6 : (PrefixMaximum before n_pre ret )) (PreH7 : (multiset_maximum S_before ret )) (PreH8 : (0 <= idx)) (PreH9 : (idx < (n_pre - 1 ))) (PreH10 : (0 <= ((idx * 2 ) + 1 ))) (PreH11 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx )) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pop_safety_wit_11 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth 0 before 0))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre )) (PreH6 : (PrefixMaximum before n_pre ret )) (PreH7 : (multiset_maximum S_before ret )) (PreH8 : (0 <= idx)) (PreH9 : (idx < (n_pre - 1 ))) (PreH10 : (0 <= ((idx * 2 ) + 1 ))) (PreH11 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx )) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_12 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth 0 before 0))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre )) (PreH6 : (PrefixMaximum before n_pre ret )) (PreH7 : (multiset_maximum S_before ret )) (PreH8 : (0 <= idx)) (PreH9 : (idx < (n_pre - 1 ))) (PreH10 : (0 <= ((idx * 2 ) + 1 ))) (PreH11 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH12 : (PopLoopState before current n_pre idx )) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_13 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((idx * 2 ) + 1 )) ”
.

Definition pop_safety_wit_14 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ ((idx * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx * 2 )) ”
.

Definition pop_safety_wit_15 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pop_safety_wit_16 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_17 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> ((idx * 2 ) + 1 ))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ ((((idx * 2 ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((idx * 2 ) + 1 ) + 1 )) ”
.

Definition pop_safety_wit_18 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> ((idx * 2 ) + 1 ))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_safety_wit_19 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  ((( &( "largest" ) )) # Int  |-> ((idx * 2 ) + 1 ))
  **  ((( &( "right" ) )) # Int  |-> (((idx * 2 ) + 1 ) + 1 ))
  **  ((( &( "left" ) )) # Int  |-> ((idx * 2 ) + 1 ))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_20 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  ((( &( "largest" ) )) # Int  |-> ((idx * 2 ) + 1 ))
  **  ((( &( "right" ) )) # Int  |-> (((idx * 2 ) + 1 ) + 1 ))
  **  ((( &( "left" ) )) # Int  |-> ((idx * 2 ) + 1 ))
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full heap_pre n_pre current )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_entail_wit_1 := 
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) ,
  (store_heap heap_pre S_before n_pre )
|--
  EX (before: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre (Znth 0 before 0) ) ” 
  &&  “ ((Znth 0 before 0) = (multiset_max (S_before))) ” 
  &&  “ (multiset_maximum S_before (Znth 0 before 0) ) ”
  &&  (IntArray.full heap_pre n_pre before )
) \/
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) ,
  (store_heap heap_pre S_before n_pre )
|--
  EX (before: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre (Znth 0 before 0) ) ” 
  &&  “ ((Znth 0 before 0) = (multiset_max (S_before))) ” 
  &&  “ (multiset_maximum S_before (Znth 0 before 0) ) ”
  &&  (IntArray.full heap_pre n_pre before )
).

Definition pop_entail_wit_2 := 
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre (replace_Znth (0) ((Znth (n_pre - 1 ) before 0)) (before)) )
|--
  EX (current: (@list Z))  (before_2: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ ((Znth 0 before 0) = (Znth 0 before_2 0)) ” 
  &&  “ ((Znth 0 before 0) = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before_2 n_pre ) ” 
  &&  “ (PrefixMaximum before_2 n_pre (Znth 0 before 0) ) ” 
  &&  “ (multiset_maximum S_before (Znth 0 before 0) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (n_pre - 1 )) ” 
  &&  “ (0 <= ((0 * 2 ) + 1 )) ” 
  &&  “ (((0 * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState before_2 current n_pre 0 ) ”
  &&  (IntArray.full heap_pre n_pre current )
) \/
(
forall (n_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  TT && emp 
|--
  EX (before_2: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ ((Znth 0 before 0) = (Znth 0 before_2 0)) ” 
  &&  “ (heap_representation S_before before_2 n_pre ) ” 
  &&  “ (PrefixMaximum before_2 n_pre (Znth 0 before 0) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (n_pre - 1 )) ” 
  &&  “ (0 <= ((0 * 2 ) + 1 )) ” 
  &&  “ (((0 * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState before_2 (replace_Znth (0) ((Znth (n_pre - 1 ) before 0)) (before)) n_pre 0 ) ”
  &&  emp
).

Definition pop_entail_wit_3_1 := 
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current_2: (@list Z)) (idx: Z) (before_2: (@list Z)) (ret: Z) (PreH1 : ((Znth ((idx * 2 ) + 1 ) current_2 0) < (Znth (((idx * 2 ) + 1 ) + 1 ) current_2 0))) (PreH2 : ((((idx * 2 ) + 1 ) + 1 ) < (n_pre - 1 ))) (PreH3 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (ret = (Znth 0 before_2 0))) (PreH7 : (ret = (multiset_max (S_before)))) (PreH8 : (heap_representation S_before before_2 n_pre )) (PreH9 : (PrefixMaximum before_2 n_pre ret )) (PreH10 : (multiset_maximum S_before ret )) (PreH11 : (0 <= idx)) (PreH12 : (idx < (n_pre - 1 ))) (PreH13 : (0 <= ((idx * 2 ) + 1 ))) (PreH14 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH15 : (PopLoopState before_2 current_2 n_pre idx )) ,
  (IntArray.full heap_pre n_pre current_2 )
|--
  EX (current: (@list Z))  (before: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) = ((idx * 2 ) + 1 )) ” 
  &&  “ ((((idx * 2 ) + 1 ) + 1 ) = (((idx * 2 ) + 1 ) + 1 )) ” 
  &&  “ (0 <= (((idx * 2 ) + 1 ) + 1 )) ” 
  &&  “ ((((idx * 2 ) + 1 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current (n_pre - 1 ) idx (((idx * 2 ) + 1 ) + 1 ) ) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (IntArray.full heap_pre n_pre current )
) \/
(
forall (n_pre: Z) (S_before: (@multiset Z)) (current_2: (@list Z)) (idx: Z) (before_2: (@list Z)) (ret: Z) (PreH1 : ((Znth ((idx * 2 ) + 1 ) current_2 0) < (Znth (((idx * 2 ) + 1 ) + 1 ) current_2 0))) (PreH2 : ((((idx * 2 ) + 1 ) + 1 ) < (n_pre - 1 ))) (PreH3 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (ret = (Znth 0 before_2 0))) (PreH7 : (ret = (multiset_max (S_before)))) (PreH8 : (heap_representation S_before before_2 n_pre )) (PreH9 : (PrefixMaximum before_2 n_pre ret )) (PreH10 : (multiset_maximum S_before ret )) (PreH11 : (0 <= idx)) (PreH12 : (idx < (n_pre - 1 ))) (PreH13 : (0 <= ((idx * 2 ) + 1 ))) (PreH14 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH15 : (PopLoopState before_2 current_2 n_pre idx )) ,
  TT && emp 
|--
  EX (before: (@list Z)) ,
  “ ((Znth 0 before_2 0) = (Znth 0 before 0)) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre (Znth 0 before_2 0) ) ” 
  &&  “ (0 <= (((idx * 2 ) + 1 ) + 1 )) ” 
  &&  “ (PopSelectedChild current_2 (n_pre - 1 ) idx (((idx * 2 ) + 1 ) + 1 ) ) ” 
  &&  “ (PopLoopState before current_2 n_pre idx ) ”
  &&  emp
).

Definition pop_entail_wit_3_2 := 
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current_2: (@list Z)) (idx: Z) (before_2: (@list Z)) (ret: Z) (PreH1 : ((((idx * 2 ) + 1 ) + 1 ) >= (n_pre - 1 ))) (PreH2 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (ret = (Znth 0 before_2 0))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before_2 n_pre )) (PreH8 : (PrefixMaximum before_2 n_pre ret )) (PreH9 : (multiset_maximum S_before ret )) (PreH10 : (0 <= idx)) (PreH11 : (idx < (n_pre - 1 ))) (PreH12 : (0 <= ((idx * 2 ) + 1 ))) (PreH13 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH14 : (PopLoopState before_2 current_2 n_pre idx )) ,
  (IntArray.full heap_pre n_pre current_2 )
|--
  EX (current: (@list Z))  (before: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) = ((idx * 2 ) + 1 )) ” 
  &&  “ ((((idx * 2 ) + 1 ) + 1 ) = (((idx * 2 ) + 1 ) + 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current (n_pre - 1 ) idx ((idx * 2 ) + 1 ) ) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (IntArray.full heap_pre n_pre current )
) \/
(
forall (n_pre: Z) (S_before: (@multiset Z)) (current_2: (@list Z)) (idx: Z) (before_2: (@list Z)) (ret: Z) (PreH1 : ((((idx * 2 ) + 1 ) + 1 ) >= (n_pre - 1 ))) (PreH2 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (ret = (Znth 0 before_2 0))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before_2 n_pre )) (PreH8 : (PrefixMaximum before_2 n_pre ret )) (PreH9 : (multiset_maximum S_before ret )) (PreH10 : (0 <= idx)) (PreH11 : (idx < (n_pre - 1 ))) (PreH12 : (0 <= ((idx * 2 ) + 1 ))) (PreH13 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH14 : (PopLoopState before_2 current_2 n_pre idx )) ,
  TT && emp 
|--
  EX (before: (@list Z)) ,
  “ ((Znth 0 before_2 0) = (Znth 0 before 0)) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre (Znth 0 before_2 0) ) ” 
  &&  “ (PopSelectedChild current_2 (n_pre - 1 ) idx ((idx * 2 ) + 1 ) ) ” 
  &&  “ (PopLoopState before current_2 n_pre idx ) ”
  &&  emp
).

Definition pop_entail_wit_3_3 := 
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current_2: (@list Z)) (idx: Z) (before_2: (@list Z)) (ret: Z) (PreH1 : ((Znth ((idx * 2 ) + 1 ) current_2 0) >= (Znth (((idx * 2 ) + 1 ) + 1 ) current_2 0))) (PreH2 : ((((idx * 2 ) + 1 ) + 1 ) < (n_pre - 1 ))) (PreH3 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (ret = (Znth 0 before_2 0))) (PreH7 : (ret = (multiset_max (S_before)))) (PreH8 : (heap_representation S_before before_2 n_pre )) (PreH9 : (PrefixMaximum before_2 n_pre ret )) (PreH10 : (multiset_maximum S_before ret )) (PreH11 : (0 <= idx)) (PreH12 : (idx < (n_pre - 1 ))) (PreH13 : (0 <= ((idx * 2 ) + 1 ))) (PreH14 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH15 : (PopLoopState before_2 current_2 n_pre idx )) ,
  (IntArray.full heap_pre n_pre current_2 )
|--
  EX (current: (@list Z))  (before: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) = ((idx * 2 ) + 1 )) ” 
  &&  “ ((((idx * 2 ) + 1 ) + 1 ) = (((idx * 2 ) + 1 ) + 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current (n_pre - 1 ) idx ((idx * 2 ) + 1 ) ) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (IntArray.full heap_pre n_pre current )
) \/
(
forall (n_pre: Z) (S_before: (@multiset Z)) (current_2: (@list Z)) (idx: Z) (before_2: (@list Z)) (ret: Z) (PreH1 : ((Znth ((idx * 2 ) + 1 ) current_2 0) >= (Znth (((idx * 2 ) + 1 ) + 1 ) current_2 0))) (PreH2 : ((((idx * 2 ) + 1 ) + 1 ) < (n_pre - 1 ))) (PreH3 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (ret = (Znth 0 before_2 0))) (PreH7 : (ret = (multiset_max (S_before)))) (PreH8 : (heap_representation S_before before_2 n_pre )) (PreH9 : (PrefixMaximum before_2 n_pre ret )) (PreH10 : (multiset_maximum S_before ret )) (PreH11 : (0 <= idx)) (PreH12 : (idx < (n_pre - 1 ))) (PreH13 : (0 <= ((idx * 2 ) + 1 ))) (PreH14 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH15 : (PopLoopState before_2 current_2 n_pre idx )) ,
  TT && emp 
|--
  EX (before: (@list Z)) ,
  “ ((Znth 0 before_2 0) = (Znth 0 before 0)) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre (Znth 0 before_2 0) ) ” 
  &&  “ (PopSelectedChild current_2 (n_pre - 1 ) idx ((idx * 2 ) + 1 ) ) ” 
  &&  “ (PopLoopState before current_2 n_pre idx ) ”
  &&  emp
).

Definition pop_entail_wit_4 := 
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before_2: (@list Z)) (current_2: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : ((Znth idx current_2 0) < (Znth largest current_2 0))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before_2 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre )) (PreH7 : (PrefixMaximum before_2 n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (left = ((idx * 2 ) + 1 ))) (PreH12 : (right = (left + 1 ))) (PreH13 : (0 <= largest)) (PreH14 : (largest < (n_pre - 1 ))) (PreH15 : (PopSelectedChild current_2 (n_pre - 1 ) idx largest )) (PreH16 : (PopLoopState before_2 current_2 n_pre idx )) ,
  (IntArray.full heap_pre n_pre (replace_Znth (largest) ((Znth idx current_2 0)) ((replace_Znth (idx) ((Znth largest current_2 0)) (current_2)))) )
|--
  EX (current: (@list Z))  (before: (@list Z)) ,
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (0 <= ((largest * 2 ) + 1 )) ” 
  &&  “ (((largest * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState before current n_pre largest ) ”
  &&  (IntArray.full heap_pre n_pre current )
) \/
(
forall (n_pre: Z) (S_before: (@multiset Z)) (before_2: (@list Z)) (current_2: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : ((Znth idx current_2 0) < (Znth largest current_2 0))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before_2 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before_2 n_pre )) (PreH7 : (PrefixMaximum before_2 n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (left = ((idx * 2 ) + 1 ))) (PreH12 : (right = (left + 1 ))) (PreH13 : (0 <= largest)) (PreH14 : (largest < (n_pre - 1 ))) (PreH15 : (PopSelectedChild current_2 (n_pre - 1 ) idx largest )) (PreH16 : (PopLoopState before_2 current_2 n_pre idx )) ,
  TT && emp 
|--
  EX (before: (@list Z)) ,
  “ ((Znth 0 before_2 0) = (Znth 0 before 0)) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre (Znth 0 before_2 0) ) ” 
  &&  “ (0 <= ((largest * 2 ) + 1 )) ” 
  &&  “ (((largest * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState before (replace_Znth (largest) ((Znth idx current_2 0)) ((replace_Znth (idx) ((Znth largest current_2 0)) (current_2)))) n_pre largest ) ”
  &&  emp
).

Definition pop_return_wit_1 := 
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) >= (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  “ (multiset_maximum S_before ret ) ”
  &&  (store_heap heap_pre (multiset_remove (S_before) (ret)) (n_pre - 1 ) )
  **  (IntArray.undef_seg heap_pre (n_pre - 1 ) n_pre )
) \/
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) >= (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  (store_heap heap_pre (multiset_remove (S_before) (ret)) (n_pre - 1 ) )
  **  (IntArray.undef_seg heap_pre (n_pre - 1 ) n_pre )
).

Definition pop_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : (((idx * 2 ) + 1 ) >= (n_pre - 1 ))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (0 <= ((idx * 2 ) + 1 ))) (PreH12 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH13 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  (store_heap heap_pre (multiset_remove (S_before) (ret)) (n_pre - 1 ) )
  **  (IntArray.undef_seg heap_pre (n_pre - 1 ) n_pre )
.

Definition pop_return_wit_2 := 
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (current: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : ((Znth idx current 0) >= (Znth largest current 0))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (left = ((idx * 2 ) + 1 ))) (PreH12 : (right = (left + 1 ))) (PreH13 : (0 <= largest)) (PreH14 : (largest < (n_pre - 1 ))) (PreH15 : (PopSelectedChild current (n_pre - 1 ) idx largest )) (PreH16 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  “ (multiset_maximum S_before ret ) ”
  &&  (store_heap heap_pre (multiset_remove (S_before) (ret)) (n_pre - 1 ) )
  **  (IntArray.undef_seg heap_pre (n_pre - 1 ) n_pre )
) \/
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (current: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : ((Znth idx current 0) >= (Znth largest current 0))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (left = ((idx * 2 ) + 1 ))) (PreH12 : (right = (left + 1 ))) (PreH13 : (0 <= largest)) (PreH14 : (largest < (n_pre - 1 ))) (PreH15 : (PopSelectedChild current (n_pre - 1 ) idx largest )) (PreH16 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  (store_heap heap_pre (multiset_remove (S_before) (ret)) (n_pre - 1 ) )
  **  (IntArray.undef_seg heap_pre (n_pre - 1 ) n_pre )
).

Definition pop_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (current: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : ((Znth idx current 0) >= (Znth largest current 0))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (left = ((idx * 2 ) + 1 ))) (PreH12 : (right = (left + 1 ))) (PreH13 : (0 <= largest)) (PreH14 : (largest < (n_pre - 1 ))) (PreH15 : (PopSelectedChild current (n_pre - 1 ) idx largest )) (PreH16 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  (store_heap heap_pre (multiset_remove (S_before) (ret)) (n_pre - 1 ) )
  **  (IntArray.undef_seg heap_pre (n_pre - 1 ) n_pre )
.

Definition pop_return_wit_3 := 
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre before )
|--
  “ (multiset_maximum S_before (Znth 0 before 0) ) ”
  &&  (store_heap heap_pre (multiset_remove (S_before) ((Znth 0 before 0))) (n_pre - 1 ) )
  **  (IntArray.undef_seg heap_pre (n_pre - 1 ) n_pre )
) \/
(
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre before )
|--
  (store_heap heap_pre (multiset_remove (S_before) ((Znth 0 before 0))) (n_pre - 1 ) )
  **  (IntArray.undef_seg heap_pre (n_pre - 1 ) n_pre )
).

Definition pop_return_wit_3_split_goal_spatial := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre = 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre before )
|--
  (store_heap heap_pre (multiset_remove (S_before) ((Znth 0 before 0))) (n_pre - 1 ) )
  **  (IntArray.undef_seg heap_pre (n_pre - 1 ) n_pre )
.

Definition pop_partial_solve_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before n_pre )) (PreH4 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH5 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH6 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre before )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre (Znth 0 before 0) ) ” 
  &&  “ ((Znth 0 before 0) = (multiset_max (S_before))) ” 
  &&  “ (multiset_maximum S_before (Znth 0 before 0) ) ”
  &&  (((heap_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 before 0))
  **  (IntArray.missing_i heap_pre 0 0 n_pre before )
.

Definition pop_partial_solve_wit_2 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre before )
|--
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre (Znth 0 before 0) ) ” 
  &&  “ ((Znth 0 before 0) = (multiset_max (S_before))) ” 
  &&  “ (multiset_maximum S_before (Znth 0 before 0) ) ”
  &&  (((heap_pre + ((n_pre - 1 ) * sizeof(INT)))) # Int  |-> (Znth (n_pre - 1 ) before 0))
  **  (IntArray.missing_i heap_pre (n_pre - 1 ) 0 n_pre before )
.

Definition pop_partial_solve_wit_3 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (PreH1 : (n_pre <> 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (heap_representation S_before before n_pre )) (PreH5 : (PrefixMaximum before n_pre (Znth 0 before 0) )) (PreH6 : ((Znth 0 before 0) = (multiset_max (S_before)))) (PreH7 : (multiset_maximum S_before (Znth 0 before 0) )) ,
  (IntArray.full heap_pre n_pre before )
|--
  “ (n_pre <> 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre (Znth 0 before 0) ) ” 
  &&  “ ((Znth 0 before 0) = (multiset_max (S_before))) ” 
  &&  “ (multiset_maximum S_before (Znth 0 before 0) ) ”
  &&  (((heap_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i heap_pre 0 0 n_pre before )
.

Definition pop_partial_solve_wit_4 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : ((((idx * 2 ) + 1 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (ret = (Znth 0 before 0))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before n_pre )) (PreH8 : (PrefixMaximum before n_pre ret )) (PreH9 : (multiset_maximum S_before ret )) (PreH10 : (0 <= idx)) (PreH11 : (idx < (n_pre - 1 ))) (PreH12 : (0 <= ((idx * 2 ) + 1 ))) (PreH13 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH14 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  “ ((((idx * 2 ) + 1 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (((heap_pre + (((idx * 2 ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((idx * 2 ) + 1 ) current 0))
  **  (IntArray.missing_i heap_pre ((idx * 2 ) + 1 ) 0 n_pre current )
.

Definition pop_partial_solve_wit_5 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (current: (@list Z)) (idx: Z) (before: (@list Z)) (ret: Z) (PreH1 : ((((idx * 2 ) + 1 ) + 1 ) < (n_pre - 1 ))) (PreH2 : (((idx * 2 ) + 1 ) < (n_pre - 1 ))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (ret = (Znth 0 before 0))) (PreH6 : (ret = (multiset_max (S_before)))) (PreH7 : (heap_representation S_before before n_pre )) (PreH8 : (PrefixMaximum before n_pre ret )) (PreH9 : (multiset_maximum S_before ret )) (PreH10 : (0 <= idx)) (PreH11 : (idx < (n_pre - 1 ))) (PreH12 : (0 <= ((idx * 2 ) + 1 ))) (PreH13 : (((idx * 2 ) + 1 ) <= INT_MAX)) (PreH14 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  “ ((((idx * 2 ) + 1 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) < (n_pre - 1 )) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (0 <= ((idx * 2 ) + 1 )) ” 
  &&  “ (((idx * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (((heap_pre + ((((idx * 2 ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth (((idx * 2 ) + 1 ) + 1 ) current 0))
  **  (IntArray.missing_i heap_pre (((idx * 2 ) + 1 ) + 1 ) 0 n_pre current )
.

Definition pop_partial_solve_wit_6 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (current: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth 0 before 0))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre )) (PreH6 : (PrefixMaximum before n_pre ret )) (PreH7 : (multiset_maximum S_before ret )) (PreH8 : (0 <= idx)) (PreH9 : (idx < (n_pre - 1 ))) (PreH10 : (left = ((idx * 2 ) + 1 ))) (PreH11 : (right = (left + 1 ))) (PreH12 : (0 <= largest)) (PreH13 : (largest < (n_pre - 1 ))) (PreH14 : (PopSelectedChild current (n_pre - 1 ) idx largest )) (PreH15 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (((heap_pre + (idx * sizeof(INT)))) # Int  |-> (Znth idx current 0))
  **  (IntArray.missing_i heap_pre idx 0 n_pre current )
.

Definition pop_partial_solve_wit_7 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (current: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : (1 < n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (ret = (Znth 0 before 0))) (PreH4 : (ret = (multiset_max (S_before)))) (PreH5 : (heap_representation S_before before n_pre )) (PreH6 : (PrefixMaximum before n_pre ret )) (PreH7 : (multiset_maximum S_before ret )) (PreH8 : (0 <= idx)) (PreH9 : (idx < (n_pre - 1 ))) (PreH10 : (left = ((idx * 2 ) + 1 ))) (PreH11 : (right = (left + 1 ))) (PreH12 : (0 <= largest)) (PreH13 : (largest < (n_pre - 1 ))) (PreH14 : (PopSelectedChild current (n_pre - 1 ) idx largest )) (PreH15 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (((heap_pre + (largest * sizeof(INT)))) # Int  |-> (Znth largest current 0))
  **  (IntArray.missing_i heap_pre largest 0 n_pre current )
.

Definition pop_partial_solve_wit_8 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (current: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : ((Znth idx current 0) < (Znth largest current 0))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (left = ((idx * 2 ) + 1 ))) (PreH12 : (right = (left + 1 ))) (PreH13 : (0 <= largest)) (PreH14 : (largest < (n_pre - 1 ))) (PreH15 : (PopSelectedChild current (n_pre - 1 ) idx largest )) (PreH16 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  “ ((Znth idx current 0) < (Znth largest current 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (((heap_pre + (idx * sizeof(INT)))) # Int  |-> (Znth idx current 0))
  **  (IntArray.missing_i heap_pre idx 0 n_pre current )
.

Definition pop_partial_solve_wit_9 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (current: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : ((Znth idx current 0) < (Znth largest current 0))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (left = ((idx * 2 ) + 1 ))) (PreH12 : (right = (left + 1 ))) (PreH13 : (0 <= largest)) (PreH14 : (largest < (n_pre - 1 ))) (PreH15 : (PopSelectedChild current (n_pre - 1 ) idx largest )) (PreH16 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  “ ((Znth idx current 0) < (Znth largest current 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (((heap_pre + (largest * sizeof(INT)))) # Int  |-> (Znth largest current 0))
  **  (IntArray.missing_i heap_pre largest 0 n_pre current )
.

Definition pop_partial_solve_wit_10 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (current: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : ((Znth idx current 0) < (Znth largest current 0))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (left = ((idx * 2 ) + 1 ))) (PreH12 : (right = (left + 1 ))) (PreH13 : (0 <= largest)) (PreH14 : (largest < (n_pre - 1 ))) (PreH15 : (PopSelectedChild current (n_pre - 1 ) idx largest )) (PreH16 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre current )
|--
  “ ((Znth idx current 0) < (Znth largest current 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (((heap_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i heap_pre idx 0 n_pre current )
.

Definition pop_partial_solve_wit_11 := 
forall (n_pre: Z) (heap_pre: Z) (S_before: (@multiset Z)) (before: (@list Z)) (current: (@list Z)) (ret: Z) (idx: Z) (left: Z) (right: Z) (largest: Z) (PreH1 : ((Znth idx current 0) < (Znth largest current 0))) (PreH2 : (1 < n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (ret = (Znth 0 before 0))) (PreH5 : (ret = (multiset_max (S_before)))) (PreH6 : (heap_representation S_before before n_pre )) (PreH7 : (PrefixMaximum before n_pre ret )) (PreH8 : (multiset_maximum S_before ret )) (PreH9 : (0 <= idx)) (PreH10 : (idx < (n_pre - 1 ))) (PreH11 : (left = ((idx * 2 ) + 1 ))) (PreH12 : (right = (left + 1 ))) (PreH13 : (0 <= largest)) (PreH14 : (largest < (n_pre - 1 ))) (PreH15 : (PopSelectedChild current (n_pre - 1 ) idx largest )) (PreH16 : (PopLoopState before current n_pre idx )) ,
  (IntArray.full heap_pre n_pre (replace_Znth (idx) ((Znth largest current 0)) (current)) )
|--
  “ ((Znth idx current 0) < (Znth largest current 0)) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ (ret = (Znth 0 before 0)) ” 
  &&  “ (ret = (multiset_max (S_before))) ” 
  &&  “ (heap_representation S_before before n_pre ) ” 
  &&  “ (PrefixMaximum before n_pre ret ) ” 
  &&  “ (multiset_maximum S_before ret ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (n_pre - 1 )) ” 
  &&  “ (left = ((idx * 2 ) + 1 )) ” 
  &&  “ (right = (left + 1 )) ” 
  &&  “ (0 <= largest) ” 
  &&  “ (largest < (n_pre - 1 )) ” 
  &&  “ (PopSelectedChild current (n_pre - 1 ) idx largest ) ” 
  &&  “ (PopLoopState before current n_pre idx ) ”
  &&  (((heap_pre + (largest * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i heap_pre largest 0 n_pre (replace_Znth (idx) ((Znth largest current 0)) (current)) )
.

(*----- Function heap_sort -----*)

Definition heap_sort_safety_wit_1 := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix: (@list Z)) (active: (@multiset Z)) (i: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((multiset_size (active)) = i)) (PreH7 : ((Zlength (suffix)) = (n_pre - i ))) (PreH8 : (HeapSortState input active suffix )) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_heap heap_pre active i )
  **  (IntArray.seg heap_pre i n_pre suffix )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition heap_sort_safety_wit_2 := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix: (@list Z)) (active: (@multiset Z)) (i: Z) (retval: Z) (PreH1 : (multiset_maximum active retval )) (PreH2 : (i > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((multiset_size (active)) = i)) (PreH9 : ((Zlength (suffix)) = (n_pre - i ))) (PreH10 : (HeapSortState input active suffix )) ,
  (store_heap heap_pre (multiset_remove (active) (retval)) (i - 1 ) )
  **  (IntArray.undef_seg heap_pre (i - 1 ) i )
  **  ((( &( "extracted" ) )) # Int  |-> retval)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg heap_pre i n_pre suffix )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition heap_sort_safety_wit_3 := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix: (@list Z)) (active: (@multiset Z)) (i: Z) (retval: Z) (PreH1 : (multiset_maximum active retval )) (PreH2 : (i > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((multiset_size (active)) = i)) (PreH9 : ((Zlength (suffix)) = (n_pre - i ))) (PreH10 : (HeapSortState input active suffix )) ,
  (store_heap heap_pre (multiset_remove (active) (retval)) (i - 1 ) )
  **  (IntArray.undef_seg heap_pre (i - 1 ) i )
  **  ((( &( "extracted" ) )) # Int  |-> retval)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg heap_pre i n_pre suffix )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition heap_sort_safety_wit_4 := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix: (@list Z)) (active: (@multiset Z)) (i: Z) (retval: Z) (PreH1 : (multiset_maximum active retval )) (PreH2 : (i > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((multiset_size (active)) = i)) (PreH9 : ((Zlength (suffix)) = (n_pre - i ))) (PreH10 : (HeapSortState input active suffix )) ,
  (((heap_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> retval)
  **  (store_heap heap_pre (multiset_remove (active) (retval)) (i - 1 ) )
  **  ((( &( "extracted" ) )) # Int  |-> retval)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg heap_pre i n_pre suffix )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition heap_sort_entail_wit_1 := 
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (store_heap heap_pre (list_to_multiset (input)) n_pre )
|--
  EX (suffix: (@list Z))  (active: (@multiset Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ ((multiset_size (active)) = n_pre) ” 
  &&  “ ((Zlength (suffix)) = (n_pre - n_pre )) ” 
  &&  “ (HeapSortState input active suffix ) ”
  &&  (store_heap heap_pre active n_pre )
  **  (IntArray.seg heap_pre n_pre n_pre suffix )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  TT && emp 
|--
  “ (HeapSortState input (list_to_multiset (input)) (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = (n_pre - n_pre )) ” 
  &&  “ ((multiset_size ((list_to_multiset (input)))) = n_pre) ”
  &&  emp
).

Definition heap_sort_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (HeapSortState input (list_to_multiset (input)) (@nil Z) )
.

Definition heap_sort_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((Zlength ((@nil Z))) = (n_pre - n_pre ))
.

Definition heap_sort_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((multiset_size ((list_to_multiset (input)))) = n_pre)
.

Definition heap_sort_entail_wit_2 := 
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix_2: (@list Z)) (active_2: (@multiset Z)) (i: Z) (retval: Z) (PreH1 : (multiset_maximum active_2 retval )) (PreH2 : (i > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((multiset_size (active_2)) = i)) (PreH9 : ((Zlength (suffix_2)) = (n_pre - i ))) (PreH10 : (HeapSortState input active_2 suffix_2 )) ,
  (((heap_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> retval)
  **  (store_heap heap_pre (multiset_remove (active_2) (retval)) (i - 1 ) )
  **  (IntArray.seg heap_pre i n_pre suffix_2 )
|--
  EX (suffix: (@list Z))  (active: (@multiset Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= n_pre) ” 
  &&  “ ((multiset_size (active)) = (i - 1 )) ” 
  &&  “ ((Zlength (suffix)) = (n_pre - (i - 1 ) )) ” 
  &&  “ (HeapSortState input active suffix ) ”
  &&  (store_heap heap_pre active (i - 1 ) )
  **  (IntArray.seg heap_pre (i - 1 ) n_pre suffix )
) \/
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix_2: (@list Z)) (active_2: (@multiset Z)) (i: Z) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (multiset_maximum active_2 retval )) (PreH4 : (i > 0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= heap_capacity)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((multiset_size (active_2)) = i)) (PreH11 : ((Zlength (suffix_2)) = (n_pre - i ))) (PreH12 : (HeapSortState input active_2 suffix_2 )) ,
  (((heap_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> retval)
  **  (store_heap heap_pre (multiset_remove (active_2) (retval)) (i - 1 ) )
  **  (IntArray.seg heap_pre i n_pre suffix_2 )
|--
  EX (suffix: (@list Z))  (active: (@multiset Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= n_pre) ” 
  &&  “ ((multiset_size (active)) = (i - 1 )) ” 
  &&  “ ((Zlength (suffix)) = (n_pre - (i - 1 ) )) ” 
  &&  “ (HeapSortState input active suffix ) ”
  &&  (store_heap heap_pre active (i - 1 ) )
  **  (IntArray.seg heap_pre (i - 1 ) n_pre suffix )
).

Definition heap_sort_return_wit_1 := 
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix: (@list Z)) (active: (@multiset Z)) (i: Z) (PreH1 : (i <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((multiset_size (active)) = i)) (PreH8 : ((Zlength (suffix)) = (n_pre - i ))) (PreH9 : (HeapSortState input active suffix )) ,
  (store_heap heap_pre active i )
  **  (IntArray.seg heap_pre i n_pre suffix )
|--
  EX (output: (@list Z)) ,
  “ (Permutation input output ) ” 
  &&  “ (increasing output ) ”
  &&  (IntArray.full heap_pre n_pre output )
) \/
(
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix: (@list Z)) (active: (@multiset Z)) (i: Z) (PreH1 : (i <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((multiset_size (active)) = i)) (PreH8 : ((Zlength (suffix)) = (n_pre - i ))) (PreH9 : (HeapSortState input active suffix )) ,
  (store_heap heap_pre active i )
  **  (IntArray.seg heap_pre i n_pre suffix )
|--
  EX (output: (@list Z)) ,
  “ (Permutation input output ) ” 
  &&  “ (increasing output ) ”
  &&  (IntArray.full heap_pre n_pre output )
).

Definition heap_sort_partial_solve_wit_1_pure := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full heap_pre n_pre input )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ ((Zlength (input)) = n_pre) ”
.

Definition heap_sort_partial_solve_wit_1_aux := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (IntArray.full heap_pre n_pre input )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ ((Zlength (input)) = n_pre) ”
  &&  (IntArray.full heap_pre n_pre input )
.

Definition heap_sort_partial_solve_wit_1 := heap_sort_partial_solve_wit_1_pure -> heap_sort_partial_solve_wit_1_aux.

Definition heap_sort_partial_solve_wit_2_pure := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix: (@list Z)) (active: (@multiset Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((multiset_size (active)) = i)) (PreH8 : ((Zlength (suffix)) = (n_pre - i ))) (PreH9 : (HeapSortState input active suffix )) ,
  ((( &( "extracted" ) )) # Int  |->_)
  **  ((( &( "heap" ) )) # Ptr  |-> heap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_heap heap_pre active i )
  **  (IntArray.seg heap_pre i n_pre suffix )
|--
  “ (1 <= i) ” 
  &&  “ (i <= heap_capacity) ”
.

Definition heap_sort_partial_solve_wit_2_aux := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix: (@list Z)) (active: (@multiset Z)) (i: Z) (PreH1 : (i > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((multiset_size (active)) = i)) (PreH8 : ((Zlength (suffix)) = (n_pre - i ))) (PreH9 : (HeapSortState input active suffix )) ,
  (store_heap heap_pre active i )
  **  (IntArray.seg heap_pre i n_pre suffix )
|--
  “ (1 <= i) ” 
  &&  “ (i <= heap_capacity) ” 
  &&  “ (i > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((multiset_size (active)) = i) ” 
  &&  “ ((Zlength (suffix)) = (n_pre - i )) ” 
  &&  “ (HeapSortState input active suffix ) ”
  &&  (store_heap heap_pre active i )
  **  (IntArray.seg heap_pre i n_pre suffix )
.

Definition heap_sort_partial_solve_wit_2 := heap_sort_partial_solve_wit_2_pure -> heap_sort_partial_solve_wit_2_aux.

Definition heap_sort_partial_solve_wit_3 := 
forall (n_pre: Z) (heap_pre: Z) (input: (@list Z)) (suffix: (@list Z)) (active: (@multiset Z)) (i: Z) (retval: Z) (PreH1 : (multiset_maximum active retval )) (PreH2 : (i > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((multiset_size (active)) = i)) (PreH9 : ((Zlength (suffix)) = (n_pre - i ))) (PreH10 : (HeapSortState input active suffix )) ,
  (store_heap heap_pre (multiset_remove (active) (retval)) (i - 1 ) )
  **  (IntArray.undef_seg heap_pre (i - 1 ) i )
  **  (IntArray.seg heap_pre i n_pre suffix )
|--
  “ (multiset_maximum active retval ) ” 
  &&  “ (i > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= heap_capacity) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((multiset_size (active)) = i) ” 
  &&  “ ((Zlength (suffix)) = (n_pre - i )) ” 
  &&  “ (HeapSortState input active suffix ) ”
  &&  (((heap_pre + ((i - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (store_heap heap_pre (multiset_remove (active) (retval)) (i - 1 ) )
  **  (IntArray.seg heap_pre i n_pre suffix )
.

Module Type VC_Correct.


Axiom proof_of_push_safety_wit_1 : push_safety_wit_1.
Axiom proof_of_push_safety_wit_2 : push_safety_wit_2.
Axiom proof_of_push_safety_wit_3 : push_safety_wit_3.
Axiom proof_of_push_safety_wit_4 : push_safety_wit_4.
Axiom proof_of_push_safety_wit_5 : push_safety_wit_5.
Axiom proof_of_push_entail_wit_1 : push_entail_wit_1.
Axiom proof_of_push_entail_wit_2 : push_entail_wit_2.
Axiom proof_of_push_entail_wit_3 : push_entail_wit_3.
Axiom proof_of_push_return_wit_1 : push_return_wit_1.
Axiom proof_of_push_return_wit_2 : push_return_wit_2.
Axiom proof_of_push_partial_solve_wit_1 : push_partial_solve_wit_1.
Axiom proof_of_push_partial_solve_wit_2 : push_partial_solve_wit_2.
Axiom proof_of_push_partial_solve_wit_3 : push_partial_solve_wit_3.
Axiom proof_of_push_partial_solve_wit_4 : push_partial_solve_wit_4.
Axiom proof_of_push_partial_solve_wit_5 : push_partial_solve_wit_5.
Axiom proof_of_push_partial_solve_wit_6 : push_partial_solve_wit_6.
Axiom proof_of_push_partial_solve_wit_7 : push_partial_solve_wit_7.
Axiom proof_of_build_safety_wit_1 : build_safety_wit_1.
Axiom proof_of_build_safety_wit_2 : build_safety_wit_2.
Axiom proof_of_build_safety_wit_3 : build_safety_wit_3.
Axiom proof_of_build_entail_wit_1 : build_entail_wit_1.
Axiom proof_of_build_entail_wit_2 : build_entail_wit_2.
Axiom proof_of_build_entail_wit_3 : build_entail_wit_3.
Axiom proof_of_build_return_wit_1 : build_return_wit_1.
Axiom proof_of_build_return_wit_2 : build_return_wit_2.
Axiom proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1.
Axiom proof_of_build_partial_solve_wit_2_pure : build_partial_solve_wit_2_pure.
Axiom proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2.
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
Axiom proof_of_pop_entail_wit_1 : pop_entail_wit_1.
Axiom proof_of_pop_entail_wit_2 : pop_entail_wit_2.
Axiom proof_of_pop_entail_wit_3_1 : pop_entail_wit_3_1.
Axiom proof_of_pop_entail_wit_3_2 : pop_entail_wit_3_2.
Axiom proof_of_pop_entail_wit_3_3 : pop_entail_wit_3_3.
Axiom proof_of_pop_entail_wit_4 : pop_entail_wit_4.
Axiom proof_of_pop_return_wit_1 : pop_return_wit_1.
Axiom proof_of_pop_return_wit_2 : pop_return_wit_2.
Axiom proof_of_pop_return_wit_3 : pop_return_wit_3.
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
Axiom proof_of_heap_sort_safety_wit_1 : heap_sort_safety_wit_1.
Axiom proof_of_heap_sort_safety_wit_2 : heap_sort_safety_wit_2.
Axiom proof_of_heap_sort_safety_wit_3 : heap_sort_safety_wit_3.
Axiom proof_of_heap_sort_safety_wit_4 : heap_sort_safety_wit_4.
Axiom proof_of_heap_sort_entail_wit_1 : heap_sort_entail_wit_1.
Axiom proof_of_heap_sort_entail_wit_2 : heap_sort_entail_wit_2.
Axiom proof_of_heap_sort_return_wit_1 : heap_sort_return_wit_1.
Axiom proof_of_heap_sort_partial_solve_wit_1_pure : heap_sort_partial_solve_wit_1_pure.
Axiom proof_of_heap_sort_partial_solve_wit_1 : heap_sort_partial_solve_wit_1.
Axiom proof_of_heap_sort_partial_solve_wit_2_pure : heap_sort_partial_solve_wit_2_pure.
Axiom proof_of_heap_sort_partial_solve_wit_2 : heap_sort_partial_solve_wit_2.
Axiom proof_of_heap_sort_partial_solve_wit_3 : heap_sort_partial_solve_wit_3.

End VC_Correct.
