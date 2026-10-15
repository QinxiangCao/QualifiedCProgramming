import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance priority_queue_index_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string

noncomputable def push_safety_wit_1 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (child : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) <= child)) (PreH4 : (child <= n_pre)) (PreH5 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH6 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def push_safety_wit_2 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ (((child - 1) ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def push_safety_wit_3 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((child - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (child - 1)) ”

noncomputable def push_safety_wit_4 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def push_safety_wit_5 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def push_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) ,
  (store_heap key_pre data_pre S_before n_pre)
|--
  EX key_base : (List Int), EX data_base : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ (heap_representation S_before key_base data_base n_pre) ”
  &&  (intArray.full key_pre n_pre key_base)
  ** (intArray.undef_seg key_pre n_pre (n_pre + 1))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre n_pre data_base)
  ** (intArray.undef_seg data_pre n_pre (n_pre + 1))
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
) \/
(
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) ,
  (store_heap key_pre data_pre S_before n_pre)
|--
  EX key_base : (List Int), EX data_base : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ (heap_representation S_before key_base data_base n_pre) ”
  &&  (intArray.full key_pre n_pre key_base)
  ** (intArray.undef_seg key_pre n_pre (n_pre + 1))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre n_pre data_base)
  ** (intArray.undef_seg data_pre n_pre (n_pre + 1))
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
)

noncomputable def push_entail_wit_2 : Prop :=
  (
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_base : (List Int)) (data_base : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before key_base data_base n_pre)) ,
  (intArray.full data_pre (n_pre + 1) (data_base ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.full key_pre (n_pre + 1) (key_base ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  EX key_current : (List Int), EX data_current : (List Int), EX key_written : (List Int), EX data_written : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre n_pre data_x_pre key_x_pre) ”
  &&  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
) \/
(
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (S_before : (multiset (Int × Int))) (key_base : (List Int)) (data_base : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before key_base data_base n_pre)) ,
  TT && emp 
|--
  EX key_written : (List Int), EX data_written : (List Int),
  “ (n_pre <= n_pre) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written (key_base ++ (key_x_pre :: (@List.nil Int))) (data_base ++ (data_x_pre :: (@List.nil Int))) n_pre n_pre data_x_pre key_x_pre) ”
  &&  emp
)

noncomputable def push_entail_wit_3 : Prop :=
  (
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre)) (PreH7 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current_2)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current_2)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  EX key_current : (List Int), EX data_current : (List Int), EX key_written : (List Int), EX data_written : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= (Z.quot (child - 1) 2)) ” &&
  “ ((Z.quot (child - 1) 2) < child) ” &&
  “ ((Z.quot (child - 1) 2) <= n_pre) ” &&
  “ ((Z.quot (child - 1) 2) = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
) \/
(
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (S_before : (multiset (Int × Int))) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre)) (PreH7 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre)) ,
  TT && emp 
|--
  EX key_written : (List Int), EX data_written : (List Int),
  “ ((0 : Int) < child) ” &&
  “ ((0 : Int) <= (Z.quot (child - 1) 2)) ” &&
  “ ((Z.quot (child - 1) 2) < child) ” &&
  “ ((Z.quot (child - 1) 2) <= n_pre) ” &&
  “ ((Z.quot (child - 1) 2) = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current_2 data_current_2 n_pre child data_x_pre key_x_pre) ”
  &&  emp
)

noncomputable def push_entail_wit_4 : Prop :=
  (
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current_2 (0 : Int)) <= (Znth child key_current_2 (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current_2)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current_2)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  EX data_current : (List Int), EX key_written : (List Int), EX data_written : (List Int), EX key_current : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_current (0 : Int)) <= (Znth child key_current (0 : Int))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushResult S_before key_current data_current n_pre data_x_pre key_x_pre) ”
  &&  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
) \/
(
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (S_before : (multiset (Int × Int))) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current_2 (0 : Int)) <= (Znth child key_current_2 (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre)) ,
  TT && emp 
|--
  “ (PushResult S_before key_current_2 data_current_2 n_pre data_x_pre key_x_pre) ”
  &&  emp
)

noncomputable def push_entail_wit_4_split_goal_1 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (S_before : (multiset (Int × Int))) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current_2 (0 : Int)) <= (Znth child key_current_2 (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre)) ,
  (PushResult S_before key_current_2 data_current_2 n_pre data_x_pre key_x_pre)

noncomputable def push_entail_wit_5 : Prop :=
  (
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current_2 (0 : Int)) > (Znth child key_current_2 (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre)) ,
  (intArray.full data_pre (n_pre + 1) (replace_Znth (child) ((Znth parent data_current_2 (0 : Int))) ((replace_Znth (parent) ((Znth child data_current_2 (0 : Int))) (data_current_2)))))
  ** (intArray.full key_pre (n_pre + 1) (replace_Znth (child) ((Znth parent key_current_2 (0 : Int))) ((replace_Znth (parent) ((Znth child key_current_2 (0 : Int))) (key_current_2)))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  EX key_current : (List Int), EX data_current : (List Int), EX key_written : (List Int), EX data_written : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent <= n_pre) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre parent data_x_pre key_x_pre) ”
  &&  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
) \/
(
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (S_before : (multiset (Int × Int))) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current_2 (0 : Int)) > (Znth child key_current_2 (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written_2 data_written_2 S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 n_pre child data_x_pre key_x_pre)) ,
  TT && emp 
|--
  EX key_written : (List Int), EX data_written : (List Int),
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written (replace_Znth (child) ((Znth (heap_parent (child)) key_current_2 (0 : Int))) ((replace_Znth ((heap_parent (child))) ((Znth child key_current_2 (0 : Int))) (key_current_2)))) (replace_Znth (child) ((Znth (heap_parent (child)) data_current_2 (0 : Int))) ((replace_Znth ((heap_parent (child))) ((Znth child data_current_2 (0 : Int))) (data_current_2)))) n_pre (heap_parent (child)) data_x_pre key_x_pre) ”
  &&  emp
)

noncomputable def push_return_wit_1 : Prop :=
  (
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (child : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1))
) \/
(
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (child : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1))
)

noncomputable def push_return_wit_1_split_goal_spatial : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (child : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child <= n_pre)) (PreH6 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH7 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1))

noncomputable def push_return_wit_2 : Prop :=
  (
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child <= n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_current (0 : Int)) <= (Znth child key_current (0 : Int)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushResult S_before key_current data_current n_pre data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1))
) \/
(
forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child <= n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_current (0 : Int)) <= (Znth child key_current (0 : Int)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushResult S_before key_current data_current n_pre data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1))
)

noncomputable def push_return_wit_2_split_goal_spatial : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child <= n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_current (0 : Int)) <= (Znth child key_current (0 : Int)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushResult S_before key_current data_current n_pre data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  (store_heap key_pre data_pre (multiset_insert (S_before) ((heap_item (key_x_pre) (data_x_pre)))) (n_pre + 1))

noncomputable def push_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_base : (List Int)) (data_base : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before key_base data_base n_pre)) ,
  (intArray.full key_pre n_pre key_base)
  ** (intArray.undef_seg key_pre n_pre (n_pre + 1))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre n_pre data_base)
  ** (intArray.undef_seg data_pre n_pre (n_pre + 1))
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ (heap_representation S_before key_base data_base n_pre) ”
  &&  (((key_pre + (n_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.full key_pre n_pre key_base)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre n_pre data_base)
  ** (intArray.undef_seg data_pre n_pre (n_pre + 1))
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_2 : Prop :=
  forall (key_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_base : (List Int)) (data_base : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : (heap_representation S_before key_base data_base n_pre)) ,
  (intArray.full key_pre (n_pre + 1) (key_base ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre n_pre data_base)
  ** (intArray.undef_seg data_pre n_pre (n_pre + 1))
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ (heap_representation S_before key_base data_base n_pre) ”
  &&  (((data_pre + (n_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.full key_pre (n_pre + 1) (key_base ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre n_pre data_base)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_3 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child <= n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH10 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent key_current (0 : Int))))
  ** (intArray.missing_i key_pre parent (0 : Int) (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_4 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child <= n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent <= n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH10 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int |-> ((Znth child key_current (0 : Int))))
  ** (intArray.missing_i key_pre child (0 : Int) (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_5 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent key_current (0 : Int))))
  ** (intArray.missing_i key_pre parent (0 : Int) (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_6 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int |-> ((Znth child key_current (0 : Int))))
  ** (intArray.missing_i key_pre child (0 : Int) (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_7 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre parent (0 : Int) (n_pre + 1) key_current)
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_8 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) (replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre child (0 : Int) (n_pre + 1) (replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_9 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full key_pre (n_pre + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent data_current (0 : Int))))
  ** (intArray.missing_i data_pre parent (0 : Int) (n_pre + 1) data_current)
  ** (intArray.full key_pre (n_pre + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_10 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.full key_pre (n_pre + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int |-> ((Znth child data_current (0 : Int))))
  ** (intArray.missing_i data_pre child (0 : Int) (n_pre + 1) data_current)
  ** (intArray.full key_pre (n_pre + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_11 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full data_pre (n_pre + 1) data_current)
  ** (intArray.full key_pre (n_pre + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre parent (0 : Int) (n_pre + 1) data_current)
  ** (intArray.full key_pre (n_pre + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def push_partial_solve_wit_12 : Prop :=
  forall (key_x_pre : Int) (data_x_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child <= n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent <= n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre)) (PreH11 : (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre)) ,
  (intArray.full data_pre (n_pre + 1) (replace_Znth (parent) ((Znth child data_current (0 : Int))) (data_current)))
  ** (intArray.full key_pre (n_pre + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (PushSource key_written data_written S_before n_pre data_x_pre key_x_pre) ” &&
  “ (PushLoopState key_written data_written key_current data_current n_pre child data_x_pre key_x_pre) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre child (0 : Int) (n_pre + 1) (replace_Znth (parent) ((Znth child data_current (0 : Int))) (data_current)))
  ** (intArray.full key_pre (n_pre + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.undef_seg key_pre (n_pre + 1) heap_capacity)
  ** (intArray.undef_seg data_pre (n_pre + 1) heap_capacity)

noncomputable def build_safety_wit_1 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (key_input)) = n_pre)) (PreH4 : ((Zlength (data_input)) = n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full key_pre n_pre key_input)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre data_input)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_2 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (key_input)) = n_pre)) (PreH5 : ((Zlength (data_input)) = n_pre)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full key_pre n_pre key_input)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre data_input)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ False ”

noncomputable def build_safety_wit_3 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (S_prefix : (multiset (Int × Int))) (child : Int) (key_x : Int) (i : Int) (data_x : Int) (PreH1 : (data_x = (Znth i data_input (0 : Int)))) (PreH2 : (key_x = (Znth i key_input (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= child)) (PreH8 : (child <= i)) (PreH9 : ((Zlength (key_input)) = n_pre)) (PreH10 : ((Zlength (data_input)) = n_pre)) (PreH11 : (BuildPrefixState S_prefix key_input data_input i)) (PreH12 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH13 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "key_x" ) )) # Int |-> (key_x))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_safety_wit_4 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (S_prefix : (multiset (Int × Int))) (child : Int) (key_x : Int) (i : Int) (data_x : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix key_input data_input i)) (PreH13 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "key_x" ) )) # Int |-> (key_x))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ (((child - 1) ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def build_safety_wit_5 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (S_prefix : (multiset (Int × Int))) (child : Int) (key_x : Int) (i : Int) (data_x : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix key_input data_input i)) (PreH13 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "key_x" ) )) # Int |-> (key_x))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((child - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (child - 1)) ”

noncomputable def build_safety_wit_6 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (S_prefix : (multiset (Int × Int))) (child : Int) (key_x : Int) (i : Int) (data_x : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix key_input data_input i)) (PreH13 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "key_x" ) )) # Int |-> (key_x))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_7 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (S_prefix : (multiset (Int × Int))) (child : Int) (key_x : Int) (i : Int) (data_x : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix key_input data_input i)) (PreH13 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "key_x" ) )) # Int |-> (key_x))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def build_safety_wit_8 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (S_prefix : (multiset (Int × Int))) (child : Int) (key_x : Int) (i : Int) (data_x : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix key_input data_input i)) (PreH13 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_safety_wit_9 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : (data_x = (Znth i data_input (0 : Int)))) (PreH2 : (key_x = (Znth i key_input (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) < child)) (PreH8 : (child <= i)) (PreH9 : ((0 : Int) <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : ((Znth parent key_current (0 : Int)) <= (Znth child key_current (0 : Int)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH18 : (PushResult S_prefix key_current data_current i data_x key_x)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_entail_wit_1 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : ((Zlength (key_input)) = n_pre)) (PreH4 : ((Zlength (data_input)) = n_pre)) ,
  (intArray.full key_pre n_pre key_input)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre data_input)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  (“ (n_pre = (0 : Int)) ” &&
  “ (1 = 1) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ”
  &&  (intArray.full key_pre n_pre key_input)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre data_input)
  ** (intArray.undef_seg data_pre n_pre heap_capacity))
  ||
  (EX key_prefix : (List Int), EX data_prefix : (List Int), EX S_prefix : (multiset (Int × Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input 1) ” &&
  “ (heap_representation S_prefix key_prefix data_prefix 1) ”
  &&  (intArray.full key_pre 1 key_prefix)
  ** (intArray.seg key_pre 1 n_pre (sublist (1) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre 1 data_prefix)
  ** (intArray.seg data_pre 1 n_pre (sublist (1) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity))

noncomputable def build_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_prefix : (List Int)) (data_prefix : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH9 : (heap_representation S_prefix_2 key_prefix data_prefix i)) ,
  (intArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)))
  ** (intArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)))
  ** (intArray.full key_pre i key_prefix)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre i data_prefix)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  EX key_current : (List Int), EX data_current : (List Int), EX key_written : (List Int), EX data_written : (List Int), EX S_prefix : (multiset (Int × Int)),
  “ ((Znth (i - i) (sublist (i) (n_pre) (data_input)) (0 : Int)) = (Znth i data_input (0 : Int))) ” &&
  “ ((Znth (i - i) (sublist (i) (n_pre) (key_input)) (0 : Int)) = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= i) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i (Znth (i - i) (sublist (i) (n_pre) (data_input)) (0 : Int)) (Znth (i - i) (sublist (i) (n_pre) (key_input)) (0 : Int))) ” &&
  “ (PushLoopState key_written data_written key_current data_current i i (Znth (i - i) (sublist (i) (n_pre) (data_input)) (0 : Int)) (Znth (i - i) (sublist (i) (n_pre) (key_input)) (0 : Int))) ”
  &&  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
) \/
(
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_prefix : (List Int)) (data_prefix : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH9 : (heap_representation S_prefix_2 key_prefix data_prefix i)) ,
  (intArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)))
  ** (intArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)))
  ** (intArray.full key_pre i key_prefix)
  ** (intArray.full data_pre i data_prefix)
|--
  EX key_current : (List Int), EX data_current : (List Int), EX key_written : (List Int), EX data_written : (List Int), EX S_prefix : (multiset (Int × Int)),
  “ ((Znth (i - i) (sublist (i) (n_pre) (data_input)) (0 : Int)) = (Znth i data_input (0 : Int))) ” &&
  “ ((Znth (i - i) (sublist (i) (n_pre) (key_input)) (0 : Int)) = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= i) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i (Znth (i - i) (sublist (i) (n_pre) (data_input)) (0 : Int)) (Znth (i - i) (sublist (i) (n_pre) (key_input)) (0 : Int))) ” &&
  “ (PushLoopState key_written data_written key_current data_current i i (Znth (i - i) (sublist (i) (n_pre) (data_input)) (0 : Int)) (Znth (i - i) (sublist (i) (n_pre) (key_input)) (0 : Int))) ”
  &&  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
)

noncomputable def build_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (child : Int) (key_x : Int) (i : Int) (data_x : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH13 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x)) (PreH14 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i child data_x key_x)) ,
  (intArray.full key_pre (i + 1) key_current_2)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current_2)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  EX key_current : (List Int), EX data_current : (List Int), EX key_written : (List Int), EX data_written : (List Int), EX S_prefix : (multiset (Int × Int)),
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= (Z.quot (child - 1) 2)) ” &&
  “ ((Z.quot (child - 1) 2) < child) ” &&
  “ ((Z.quot (child - 1) 2) <= i) ” &&
  “ ((Z.quot (child - 1) 2) = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
) \/
(
forall (n_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (child : Int) (key_x : Int) (i : Int) (data_x : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH13 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x)) (PreH14 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i child data_x key_x)) ,
  TT && emp 
|--
  EX key_written : (List Int), EX data_written : (List Int), EX S_prefix : (multiset (Int × Int)),
  “ ((0 : Int) < child) ” &&
  “ ((0 : Int) <= (Z.quot (child - 1) 2)) ” &&
  “ ((Z.quot (child - 1) 2) < child) ” &&
  “ ((Z.quot (child - 1) 2) <= i) ” &&
  “ ((Z.quot (child - 1) 2) = (heap_parent (child))) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i (Znth i data_input (0 : Int)) (Znth i key_input (0 : Int))) ” &&
  “ (PushLoopState key_written data_written key_current_2 data_current_2 i child (Znth i data_input (0 : Int)) (Znth i key_input (0 : Int))) ”
  &&  emp
)

noncomputable def build_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current_2 (0 : Int)) <= (Znth child key_current_2 (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH17 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x)) (PreH18 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i child data_x key_x)) ,
  (intArray.full key_pre (i + 1) key_current_2)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current_2)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  EX data_current : (List Int), EX key_written : (List Int), EX data_written : (List Int), EX S_prefix : (multiset (Int × Int)), EX key_current : (List Int),
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_current (0 : Int)) <= (Znth child key_current (0 : Int))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushResult S_prefix key_current data_current i data_x key_x) ”
  &&  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
) \/
(
forall (n_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current_2 (0 : Int)) <= (Znth child key_current_2 (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH17 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x)) (PreH18 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i child data_x key_x)) ,
  TT && emp 
|--
  EX key_written : (List Int), EX data_written : (List Int), EX S_prefix : (multiset (Int × Int)),
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i (Znth i data_input (0 : Int)) (Znth i key_input (0 : Int))) ” &&
  “ (PushResult S_prefix key_current_2 data_current_2 i (Znth i data_input (0 : Int)) (Znth i key_input (0 : Int))) ”
  &&  emp
)

noncomputable def build_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current_2 (0 : Int)) > (Znth child key_current_2 (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH17 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x)) (PreH18 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i child data_x key_x)) ,
  (intArray.full data_pre (i + 1) (replace_Znth (child) ((Znth parent data_current_2 (0 : Int))) ((replace_Znth (parent) ((Znth child data_current_2 (0 : Int))) (data_current_2)))))
  ** (intArray.full key_pre (i + 1) (replace_Znth (child) ((Znth parent key_current_2 (0 : Int))) ((replace_Znth (parent) ((Znth child key_current_2 (0 : Int))) (key_current_2)))))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  EX key_current : (List Int), EX data_current : (List Int), EX key_written : (List Int), EX data_written : (List Int), EX S_prefix : (multiset (Int × Int)),
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent <= i) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i parent data_x key_x) ”
  &&  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
) \/
(
forall (n_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (key_written_2 : (List Int)) (data_written_2 : (List Int)) (key_current_2 : (List Int)) (data_current_2 : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current_2 (0 : Int)) > (Znth child key_current_2 (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH17 : (PushSource key_written_2 data_written_2 S_prefix_2 i data_x key_x)) (PreH18 : (PushLoopState key_written_2 data_written_2 key_current_2 data_current_2 i child data_x key_x)) ,
  TT && emp 
|--
  EX key_written : (List Int), EX data_written : (List Int), EX S_prefix : (multiset (Int × Int)),
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i (Znth i data_input (0 : Int)) (Znth i key_input (0 : Int))) ” &&
  “ (PushLoopState key_written data_written (replace_Znth (child) ((Znth (heap_parent (child)) key_current_2 (0 : Int))) ((replace_Znth ((heap_parent (child))) ((Znth child key_current_2 (0 : Int))) (key_current_2)))) (replace_Znth (child) ((Znth (heap_parent (child)) data_current_2 (0 : Int))) ((replace_Znth ((heap_parent (child))) ((Znth child data_current_2 (0 : Int))) (data_current_2)))) i (heap_parent (child)) (Znth i data_input (0 : Int)) (Znth i key_input (0 : Int))) ”
  &&  emp
)

noncomputable def build_entail_wit_6_1 : Prop :=
  (
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (child : Int) (key_x : Int) (i : Int) (data_x : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH13 : (PushSource key_written data_written S_prefix_2 i data_x key_x)) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  EX key_prefix : (List Int), EX data_prefix : (List Int), EX S_prefix : (multiset (Int × Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input (i + 1)) ” &&
  “ (heap_representation S_prefix key_prefix data_prefix (i + 1)) ”
  &&  (intArray.full key_pre (i + 1) key_prefix)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_prefix)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
) \/
(
forall (n_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (key_written : (List Int)) (data_written : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (child : Int) (key_x : Int) (i : Int) (data_x : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= child)) (PreH9 : (child <= i)) (PreH10 : ((Zlength (key_input)) = n_pre)) (PreH11 : ((Zlength (data_input)) = n_pre)) (PreH12 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH13 : (PushSource key_written data_written S_prefix_2 i data_x key_x)) (PreH14 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  TT && emp 
|--
  EX S_prefix : (multiset (Int × Int)),
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (key_input))) ” &&
  “ (BuildPrefixState S_prefix key_input data_input (i + 1)) ” &&
  “ (heap_representation S_prefix key_current data_current (i + 1)) ”
  &&  emp
)

noncomputable def build_entail_wit_6_2 : Prop :=
  (
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : (data_x = (Znth i data_input (0 : Int)))) (PreH2 : (key_x = (Znth i key_input (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) < child)) (PreH8 : (child <= i)) (PreH9 : ((0 : Int) <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : ((Znth parent key_current (0 : Int)) <= (Znth child key_current (0 : Int)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix_2 i data_x key_x)) (PreH18 : (PushResult S_prefix_2 key_current data_current i data_x key_x)) ,
  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  EX key_prefix : (List Int), EX data_prefix : (List Int), EX S_prefix : (multiset (Int × Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input (i + 1)) ” &&
  “ (heap_representation S_prefix key_prefix data_prefix (i + 1)) ”
  &&  (intArray.full key_pre (i + 1) key_prefix)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_prefix)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
) \/
(
forall (n_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix_2 : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : (data_x = (Znth i data_input (0 : Int)))) (PreH2 : (key_x = (Znth i key_input (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) < child)) (PreH8 : (child <= i)) (PreH9 : ((0 : Int) <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : ((Znth parent key_current (0 : Int)) <= (Znth child key_current (0 : Int)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix_2 key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix_2 i data_x key_x)) (PreH18 : (PushResult S_prefix_2 key_current data_current i data_x key_x)) ,
  TT && emp 
|--
  EX S_prefix : (multiset (Int × Int)),
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (key_input))) ” &&
  “ (BuildPrefixState S_prefix key_input data_input (i + 1)) ” &&
  “ (heap_representation S_prefix key_current data_current (i + 1)) ”
  &&  emp
)

noncomputable def build_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (key_input)) = n_pre)) (PreH5 : ((Zlength (data_input)) = n_pre)) ,
  (intArray.full key_pre n_pre key_input)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre data_input)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre)
) \/
(
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (key_input)) = n_pre)) (PreH5 : ((Zlength (data_input)) = n_pre)) ,
  (intArray.full key_pre n_pre key_input)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre data_input)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre)
)

noncomputable def build_return_wit_1_split_goal_spatial : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = 1)) (PreH4 : ((Zlength (key_input)) = n_pre)) (PreH5 : ((Zlength (data_input)) = n_pre)) ,
  (intArray.full key_pre n_pre key_input)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre data_input)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre)

noncomputable def build_return_wit_2 : Prop :=
  (
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_prefix : (List Int)) (data_prefix : (List Int)) (S_prefix : (multiset (Int × Int))) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix key_input data_input i)) (PreH9 : (heap_representation S_prefix key_prefix data_prefix i)) ,
  (intArray.full key_pre i key_prefix)
  ** (intArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre i data_prefix)
  ** (intArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre)
) \/
(
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_prefix : (List Int)) (data_prefix : (List Int)) (S_prefix : (multiset (Int × Int))) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix key_input data_input i)) (PreH9 : (heap_representation S_prefix key_prefix data_prefix i)) ,
  (intArray.full key_pre i key_prefix)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre i data_prefix)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre)
)

noncomputable def build_return_wit_2_split_goal_spatial : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_prefix : (List Int)) (data_prefix : (List Int)) (S_prefix : (multiset (Int × Int))) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix key_input data_input i)) (PreH9 : (heap_representation S_prefix key_prefix data_prefix i)) ,
  (intArray.full key_pre i key_prefix)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre i data_prefix)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  (store_heap key_pre data_pre (list_to_multiset ((pair_list (key_input) (data_input)))) n_pre)

noncomputable def build_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_prefix : (List Int)) (data_prefix : (List Int)) (S_prefix : (multiset (Int × Int))) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix key_input data_input i)) (PreH9 : (heap_representation S_prefix key_prefix data_prefix i)) ,
  (intArray.full key_pre i key_prefix)
  ** (intArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre i data_prefix)
  ** (intArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (heap_representation S_prefix key_prefix data_prefix i) ”
  &&  (((data_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i - i) (sublist (i) (n_pre) (data_input)) (0 : Int))))
  ** (intArray.missing_i data_pre i i n_pre (sublist (i) (n_pre) (data_input)))
  ** (intArray.full key_pre i key_prefix)
  ** (intArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre i data_prefix)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (key_prefix : (List Int)) (data_prefix : (List Int)) (S_prefix : (multiset (Int × Int))) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= heap_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (key_input)) = n_pre)) (PreH7 : ((Zlength (data_input)) = n_pre)) (PreH8 : (BuildPrefixState S_prefix key_input data_input i)) (PreH9 : (heap_representation S_prefix key_prefix data_prefix i)) ,
  (intArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)))
  ** (intArray.full key_pre i key_prefix)
  ** (intArray.seg key_pre i n_pre (sublist (i) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre i data_prefix)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (heap_representation S_prefix key_prefix data_prefix i) ”
  &&  (((key_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i - i) (sublist (i) (n_pre) (key_input)) (0 : Int))))
  ** (intArray.missing_i key_pre i i n_pre (sublist (i) (n_pre) (key_input)))
  ** (intArray.seg data_pre i n_pre (sublist (i) (n_pre) (data_input)))
  ** (intArray.full key_pre i key_prefix)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre i data_prefix)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : (data_x = (Znth i data_input (0 : Int)))) (PreH2 : (key_x = (Znth i key_input (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) < child)) (PreH8 : (child <= i)) (PreH9 : ((0 : Int) <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : ((Zlength (key_input)) = n_pre)) (PreH14 : ((Zlength (data_input)) = n_pre)) (PreH15 : (BuildPrefixState S_prefix key_input data_input i)) (PreH16 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH17 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent key_current (0 : Int))))
  ** (intArray.missing_i key_pre parent (0 : Int) (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : (data_x = (Znth i data_input (0 : Int)))) (PreH2 : (key_x = (Znth i key_input (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) < child)) (PreH8 : (child <= i)) (PreH9 : ((0 : Int) <= parent)) (PreH10 : (parent < child)) (PreH11 : (parent <= i)) (PreH12 : (parent = (heap_parent (child)))) (PreH13 : ((Zlength (key_input)) = n_pre)) (PreH14 : ((Zlength (data_input)) = n_pre)) (PreH15 : (BuildPrefixState S_prefix key_input data_input i)) (PreH16 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH17 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int |-> ((Znth child key_current (0 : Int))))
  ** (intArray.missing_i key_pre child (0 : Int) (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent key_current (0 : Int))))
  ** (intArray.missing_i key_pre parent (0 : Int) (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int |-> ((Znth child key_current (0 : Int))))
  ** (intArray.missing_i key_pre child (0 : Int) (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_7 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full key_pre (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre parent (0 : Int) (i + 1) key_current)
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_8 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full key_pre (i + 1) (replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre child (0 : Int) (i + 1) (replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_9 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full key_pre (i + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre (i + 1) data_current)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent data_current (0 : Int))))
  ** (intArray.missing_i data_pre parent (0 : Int) (i + 1) data_current)
  ** (intArray.full key_pre (i + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_10 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full data_pre (i + 1) data_current)
  ** (intArray.full key_pre (i + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int |-> ((Znth child data_current (0 : Int))))
  ** (intArray.missing_i data_pre child (0 : Int) (i + 1) data_current)
  ** (intArray.full key_pre (i + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_11 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full data_pre (i + 1) data_current)
  ** (intArray.full key_pre (i + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre parent (0 : Int) (i + 1) data_current)
  ** (intArray.full key_pre (i + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def build_partial_solve_wit_12 : Prop :=
  forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (data_input : (List Int)) (key_input : (List Int)) (S_prefix : (multiset (Int × Int))) (key_written : (List Int)) (data_written : (List Int)) (key_current : (List Int)) (data_current : (List Int)) (data_x : Int) (i : Int) (key_x : Int) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int)))) (PreH2 : (data_x = (Znth i data_input (0 : Int)))) (PreH3 : (key_x = (Znth i key_input (0 : Int)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) < child)) (PreH9 : (child <= i)) (PreH10 : ((0 : Int) <= parent)) (PreH11 : (parent < child)) (PreH12 : (parent <= i)) (PreH13 : (parent = (heap_parent (child)))) (PreH14 : ((Zlength (key_input)) = n_pre)) (PreH15 : ((Zlength (data_input)) = n_pre)) (PreH16 : (BuildPrefixState S_prefix key_input data_input i)) (PreH17 : (PushSource key_written data_written S_prefix i data_x key_x)) (PreH18 : (PushLoopState key_written data_written key_current data_current i child data_x key_x)) ,
  (intArray.full data_pre (i + 1) (replace_Znth (parent) ((Znth child data_current (0 : Int))) (data_current)))
  ** (intArray.full key_pre (i + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  “ ((Znth parent key_current (0 : Int)) > (Znth child key_current (0 : Int))) ” &&
  “ (data_x = (Znth i data_input (0 : Int))) ” &&
  “ (key_x = (Znth i key_input (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child <= i) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent <= i) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Zlength (key_input)) = n_pre) ” &&
  “ ((Zlength (data_input)) = n_pre) ” &&
  “ (BuildPrefixState S_prefix key_input data_input i) ” &&
  “ (PushSource key_written data_written S_prefix i data_x key_x) ” &&
  “ (PushLoopState key_written data_written key_current data_current i child data_x key_x) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre child (0 : Int) (i + 1) (replace_Znth (parent) ((Znth child data_current (0 : Int))) (data_current)))
  ** (intArray.full key_pre (i + 1) (replace_Znth (child) ((Znth parent key_current (0 : Int))) ((replace_Znth (parent) ((Znth child key_current (0 : Int))) (key_current)))))
  ** (intArray.seg key_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (key_input)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.seg data_pre (i + 1) n_pre (sublist ((i + 1)) (n_pre) (data_input)))
  ** (intArray.undef_seg data_pre n_pre heap_capacity)

noncomputable def pop_safety_wit_1 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre)) (PreH4 : (PrefixMinimum before_key before_data n_pre popped)) (PreH5 : (multiset_minimum S_before popped)) ,
  ((( &( "result_key" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pop_safety_wit_2 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre)) (PreH4 : (PrefixMinimum before_key before_data n_pre popped)) (PreH5 : (multiset_minimum S_before popped)) ,
  ((( &( "result_data" ) )) # Int |->_)
  ** (intArray.full key_pre n_pre before_key)
  ** ((( &( "result_key" ) )) # Int |-> ((Znth (0 : Int) before_key (0 : Int))))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pop_safety_wit_3 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : (heap_representation S_before before_key before_data n_pre)) (PreH6 : (PrefixMinimum before_key before_data n_pre popped)) (PreH7 : (multiset_minimum S_before popped)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_4 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pop_safety_wit_5 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def pop_safety_wit_6 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_7 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  (intArray.full key_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_key (0 : Int))) (before_key)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pop_safety_wit_8 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  (intArray.full key_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_key (0 : Int))) (before_key)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def pop_safety_wit_9 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  (intArray.full key_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_key (0 : Int))) (before_key)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_10 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  ((( &( "idx" ) )) # Int |->_)
  ** (intArray.full data_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_data (0 : Int))) (before_data)))
  ** (intArray.full key_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_key (0 : Int))) (before_key)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pop_safety_wit_11 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : ((0 : Int) <= ((idx * 2) + 1))) (PreH8 : (((idx * 2) + 1) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre)) (PreH10 : (PrefixMinimum before_key before_data n_pre popped)) (PreH11 : (multiset_minimum S_before popped)) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def pop_safety_wit_12 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : ((0 : Int) <= ((idx * 2) + 1))) (PreH8 : (((idx * 2) + 1) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre)) (PreH10 : (PrefixMinimum before_key before_data n_pre popped)) (PreH11 : (multiset_minimum S_before popped)) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (((idx * 2) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((idx * 2) + 1)) ”

noncomputable def pop_safety_wit_13 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : ((0 : Int) <= ((idx * 2) + 1))) (PreH8 : (((idx * 2) + 1) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre)) (PreH10 : (PrefixMinimum before_key before_data n_pre popped)) (PreH11 : (multiset_minimum S_before popped)) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((idx * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (idx * 2)) ”

noncomputable def pop_safety_wit_14 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : ((0 : Int) <= ((idx * 2) + 1))) (PreH8 : (((idx * 2) + 1) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre)) (PreH10 : (PrefixMinimum before_key before_data n_pre popped)) (PreH11 : (multiset_minimum S_before popped)) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def pop_safety_wit_15 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : ((0 : Int) <= ((idx * 2) + 1))) (PreH8 : (((idx * 2) + 1) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre)) (PreH10 : (PrefixMinimum before_key before_data n_pre popped)) (PreH11 : (multiset_minimum S_before popped)) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_16 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : ((0 : Int) <= ((idx * 2) + 1))) (PreH8 : (((idx * 2) + 1) <= INT_MAX)) (PreH9 : (heap_representation S_before before_key before_data n_pre)) (PreH10 : (PrefixMinimum before_key before_data n_pre popped)) (PreH11 : (multiset_minimum S_before popped)) (PreH12 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_17 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : ((0 : Int) <= ((idx * 2) + 1))) (PreH9 : (((idx * 2) + 1) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre)) (PreH11 : (PrefixMinimum before_key before_data n_pre popped)) (PreH12 : (multiset_minimum S_before popped)) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (((idx * 2) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((idx * 2) + 1)) ”

noncomputable def pop_safety_wit_18 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : ((0 : Int) <= ((idx * 2) + 1))) (PreH9 : (((idx * 2) + 1) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre)) (PreH11 : (PrefixMinimum before_key before_data n_pre popped)) (PreH12 : (multiset_minimum S_before popped)) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((idx * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (idx * 2)) ”

noncomputable def pop_safety_wit_19 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : ((0 : Int) <= ((idx * 2) + 1))) (PreH9 : (((idx * 2) + 1) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre)) (PreH11 : (PrefixMinimum before_key before_data n_pre popped)) (PreH12 : (multiset_minimum S_before popped)) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def pop_safety_wit_20 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : ((0 : Int) <= ((idx * 2) + 1))) (PreH9 : (((idx * 2) + 1) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre)) (PreH11 : (PrefixMinimum before_key before_data n_pre popped)) (PreH12 : (multiset_minimum S_before popped)) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_21 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : ((0 : Int) <= ((idx * 2) + 1))) (PreH9 : (((idx * 2) + 1) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre)) (PreH11 : (PrefixMinimum before_key before_data n_pre popped)) (PreH12 : (multiset_minimum S_before popped)) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |-> (((idx * 2) + 1)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((((idx * 2) + 1) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((idx * 2) + 1) + 1)) ”

noncomputable def pop_safety_wit_22 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped : (Int × Int)) (result_key : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : ((0 : Int) <= ((idx * 2) + 1))) (PreH9 : (((idx * 2) + 1) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre)) (PreH11 : (PrefixMinimum before_key before_data n_pre popped)) (PreH12 : (multiset_minimum S_before popped)) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |-> (((idx * 2) + 1)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_safety_wit_23 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : (left = ((idx * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (n_pre - 1))) (PreH12 : ((0 : Int) <= right)) (PreH13 : (right <= (n_pre - 1))) (PreH14 : (heap_representation S_before before_key before_data n_pre)) (PreH15 : (PrefixMinimum before_key before_data n_pre popped)) (PreH16 : (multiset_minimum S_before popped)) (PreH17 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "smallest" ) )) # Int |-> (smallest))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def pop_safety_wit_24 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : (left = ((idx * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (n_pre - 1))) (PreH12 : ((0 : Int) <= right)) (PreH13 : (right <= (n_pre - 1))) (PreH14 : (heap_representation S_before before_key before_data n_pre)) (PreH15 : (PrefixMinimum before_key before_data n_pre popped)) (PreH16 : (multiset_minimum S_before popped)) (PreH17 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "smallest" ) )) # Int |-> (smallest))
  ** (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pop_entail_wit_1 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (PreH1 : (1 <= n_pre)) ,
  (store_heap key_pre data_pre S_before n_pre)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX popped : (Int × Int), EX before_key : (List Int), EX before_data : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (PreH1 : (1 <= n_pre)) ,
  (store_heap key_pre data_pre S_before n_pre)
|--
  EX popped : (Int × Int), EX before_key : (List Int), EX before_data : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
)

noncomputable def pop_entail_wit_2 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped_2 : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre)) (PreH4 : (PrefixMinimum before_key before_data n_pre popped_2)) (PreH5 : (multiset_minimum S_before popped_2)) ,
  (intArray.full data_pre n_pre before_data)
  ** (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX before_key_2 : (List Int), EX before_data_2 : (List Int), EX popped : (Int × Int),
  “ ((Znth (0 : Int) before_key (0 : Int)) = (item_key (popped))) ” &&
  “ ((Znth (0 : Int) before_data (0 : Int)) = (item_data (popped))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (heap_representation S_before before_key_2 before_data_2 n_pre) ” &&
  “ (PrefixMinimum before_key_2 before_data_2 n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (intArray.full key_pre n_pre before_key_2)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data_2)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped_2 : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre)) (PreH4 : (PrefixMinimum before_key before_data n_pre popped_2)) (PreH5 : (multiset_minimum S_before popped_2)) ,
  TT && emp 
|--
  EX popped : (Int × Int),
  “ ((Znth (0 : Int) before_key (0 : Int)) = (item_key (popped))) ” &&
  “ ((Znth (0 : Int) before_data (0 : Int)) = (item_data (popped))) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  emp
)

noncomputable def pop_entail_wit_3 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (n_pre = 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (heap_representation S_before before_key before_data n_pre)) (PreH7 : (PrefixMinimum before_key before_data n_pre popped_2)) (PreH8 : (multiset_minimum S_before popped_2)) ,
  (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX popped : (Int × Int),
  “ (n_pre = 1) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (0 : Int))
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (n_pre = 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (heap_representation S_before before_key before_data n_pre)) (PreH7 : (PrefixMinimum before_key before_data n_pre popped_2)) (PreH8 : (multiset_minimum S_before popped_2)) ,
  (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  EX popped : (Int × Int),
  “ (n_pre = 1) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (0 : Int))
)

noncomputable def pop_entail_wit_4 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH7 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH8 : (multiset_minimum S_before popped_2)) ,
  (intArray.full key_pre n_pre before_key_2)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data_2)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (n_pre ≠ 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH7 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH8 : (multiset_minimum S_before popped_2)) ,
  TT && emp 
|--
  EX popped : (Int × Int),
  “ ((item_key (popped_2)) = (item_key (popped))) ” &&
  “ ((item_data (popped_2)) = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ (PrefixMinimum before_key_2 before_data_2 n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  emp
)

noncomputable def pop_entail_wit_5 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH9 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH10 : (multiset_minimum S_before popped_2)) ,
  (intArray.full data_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_data_2 (0 : Int))) (before_data_2)))
  ** (intArray.full key_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_key_2 (0 : Int))) (before_key_2)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX current_key : (List Int), EX current_data : (List Int), EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (((0 : Int) * 2) + 1)) ” &&
  “ ((((0 : Int) * 2) + 1) <= INT_MAX) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre (0 : Int)) ”
  &&  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH9 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH10 : (multiset_minimum S_before popped_2)) ,
  TT && emp 
|--
  EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ ((item_key (popped_2)) = (item_key (popped))) ” &&
  “ ((item_data (popped_2)) = (item_data (popped))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (((0 : Int) * 2) + 1)) ” &&
  “ ((((0 : Int) * 2) + 1) <= INT_MAX) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_key_2 (0 : Int))) (before_key_2)) (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_data_2 (0 : Int))) (before_data_2)) n_pre (0 : Int)) ”
  &&  emp
)

noncomputable def pop_entail_wit_6 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (idx : Int) (result_data : Int) (popped_2 : (Int × Int)) (result_key : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : ((0 : Int) <= ((idx * 2) + 1))) (PreH9 : (((idx * 2) + 1) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH11 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH12 : (multiset_minimum S_before popped_2)) (PreH13 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  (intArray.full key_pre n_pre current_key_2)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data_2)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX current_key : (List Int), EX current_data : (List Int), EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (((idx * 2) + 1) = ((idx * 2) + 1)) ” &&
  “ ((((idx * 2) + 1) + 1) = (((idx * 2) + 1) + 1)) ” &&
  “ (((idx * 2) + 1) = ((idx * 2) + 1)) ” &&
  “ ((0 : Int) <= ((idx * 2) + 1)) ” &&
  “ (((idx * 2) + 1) < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (((idx * 2) + 1) + 1)) ” &&
  “ ((((idx * 2) + 1) + 1) <= (n_pre - 1)) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (S_before : (multiset (Int × Int))) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (idx : Int) (result_data : Int) (popped_2 : (Int × Int)) (result_key : Int) (PreH1 : (((idx * 2) + 1) < (n_pre - 1))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : ((0 : Int) <= ((idx * 2) + 1))) (PreH9 : (((idx * 2) + 1) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH11 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH12 : (multiset_minimum S_before popped_2)) (PreH13 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  TT && emp 
|--
  EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ ((item_key (popped_2)) = (item_key (popped))) ” &&
  “ ((item_data (popped_2)) = (item_data (popped))) ” &&
  “ ((0 : Int) <= (((idx * 2) + 1) + 1)) ” &&
  “ ((((idx * 2) + 1) + 1) <= (n_pre - 1)) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre idx) ”
  &&  emp
)

noncomputable def pop_entail_wit_7_1 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth right current_key_2 (0 : Int)) < (Znth left current_key_2 (0 : Int)))) (PreH2 : (right < (n_pre - 1))) (PreH3 : (result_key = (item_key (popped_2)))) (PreH4 : (result_data = (item_data (popped_2)))) (PreH5 : (1 < n_pre)) (PreH6 : (n_pre <= heap_capacity)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx < (n_pre - 1))) (PreH9 : (left = ((idx * 2) + 1))) (PreH10 : (right = (left + 1))) (PreH11 : (smallest = left)) (PreH12 : ((0 : Int) <= left)) (PreH13 : (left < (n_pre - 1))) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right <= (n_pre - 1))) (PreH16 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH17 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH18 : (multiset_minimum S_before popped_2)) (PreH19 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  (intArray.full key_pre n_pre current_key_2)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data_2)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX current_data : (List Int), EX before_key : (List Int), EX before_data : (List Int), EX current_key : (List Int), EX popped : (Int × Int),
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx right) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth right current_key_2 (0 : Int)) < (Znth left current_key_2 (0 : Int)))) (PreH2 : (right < (n_pre - 1))) (PreH3 : (result_key = (item_key (popped_2)))) (PreH4 : (result_data = (item_data (popped_2)))) (PreH5 : (1 < n_pre)) (PreH6 : (n_pre <= heap_capacity)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx < (n_pre - 1))) (PreH9 : (left = ((idx * 2) + 1))) (PreH10 : (right = (left + 1))) (PreH11 : (smallest = left)) (PreH12 : ((0 : Int) <= left)) (PreH13 : (left < (n_pre - 1))) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right <= (n_pre - 1))) (PreH16 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH17 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH18 : (multiset_minimum S_before popped_2)) (PreH19 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  TT && emp 
|--
  EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ ((item_key (popped_2)) = (item_key (popped))) ” &&
  “ ((item_data (popped_2)) = (item_data (popped))) ” &&
  “ (PopSelectedChild current_key_2 (n_pre - 1) idx (left + 1)) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre idx) ”
  &&  emp
)

noncomputable def pop_entail_wit_7_2 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (right >= (n_pre - 1))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : (smallest = left)) (PreH11 : ((0 : Int) <= left)) (PreH12 : (left < (n_pre - 1))) (PreH13 : ((0 : Int) <= right)) (PreH14 : (right <= (n_pre - 1))) (PreH15 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH16 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH17 : (multiset_minimum S_before popped_2)) (PreH18 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  (intArray.full key_pre n_pre current_key_2)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data_2)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX current_data : (List Int), EX before_key : (List Int), EX before_data : (List Int), EX current_key : (List Int), EX popped : (Int × Int),
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (right >= (n_pre - 1))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : (smallest = left)) (PreH11 : ((0 : Int) <= left)) (PreH12 : (left < (n_pre - 1))) (PreH13 : ((0 : Int) <= right)) (PreH14 : (right <= (n_pre - 1))) (PreH15 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH16 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH17 : (multiset_minimum S_before popped_2)) (PreH18 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  TT && emp 
|--
  EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ ((item_key (popped_2)) = (item_key (popped))) ” &&
  “ ((item_data (popped_2)) = (item_data (popped))) ” &&
  “ (PopSelectedChild current_key_2 (n_pre - 1) idx left) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre idx) ”
  &&  emp
)

noncomputable def pop_entail_wit_7_3 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth right current_key_2 (0 : Int)) >= (Znth left current_key_2 (0 : Int)))) (PreH2 : (right < (n_pre - 1))) (PreH3 : (result_key = (item_key (popped_2)))) (PreH4 : (result_data = (item_data (popped_2)))) (PreH5 : (1 < n_pre)) (PreH6 : (n_pre <= heap_capacity)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx < (n_pre - 1))) (PreH9 : (left = ((idx * 2) + 1))) (PreH10 : (right = (left + 1))) (PreH11 : (smallest = left)) (PreH12 : ((0 : Int) <= left)) (PreH13 : (left < (n_pre - 1))) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right <= (n_pre - 1))) (PreH16 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH17 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH18 : (multiset_minimum S_before popped_2)) (PreH19 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  (intArray.full key_pre n_pre current_key_2)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data_2)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX current_data : (List Int), EX before_key : (List Int), EX before_data : (List Int), EX current_key : (List Int), EX popped : (Int × Int),
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth right current_key_2 (0 : Int)) >= (Znth left current_key_2 (0 : Int)))) (PreH2 : (right < (n_pre - 1))) (PreH3 : (result_key = (item_key (popped_2)))) (PreH4 : (result_data = (item_data (popped_2)))) (PreH5 : (1 < n_pre)) (PreH6 : (n_pre <= heap_capacity)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx < (n_pre - 1))) (PreH9 : (left = ((idx * 2) + 1))) (PreH10 : (right = (left + 1))) (PreH11 : (smallest = left)) (PreH12 : ((0 : Int) <= left)) (PreH13 : (left < (n_pre - 1))) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right <= (n_pre - 1))) (PreH16 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH17 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH18 : (multiset_minimum S_before popped_2)) (PreH19 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  TT && emp 
|--
  EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ ((item_key (popped_2)) = (item_key (popped))) ” &&
  “ ((item_data (popped_2)) = (item_data (popped))) ” &&
  “ (PopSelectedChild current_key_2 (n_pre - 1) idx left) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key_2 current_data_2 n_pre idx) ”
  &&  emp
)

noncomputable def pop_entail_wit_8 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key_2 (0 : Int)) <= (Znth smallest current_key_2 (0 : Int)))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key_2 (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH14 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH15 : (multiset_minimum S_before popped_2)) (PreH16 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  (intArray.full key_pre n_pre current_key_2)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data_2)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX current_data : (List Int), EX before_key : (List Int), EX before_data : (List Int), EX current_key : (List Int), EX popped : (Int × Int),
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (n_pre - 1)) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right <= (n_pre - 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ ((Znth idx current_key (0 : Int)) <= (Znth smallest current_key (0 : Int))) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopReadyState before_key before_data current_key current_data n_pre popped) ”
  &&  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key_2 (0 : Int)) <= (Znth smallest current_key_2 (0 : Int)))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key_2 (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH14 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH15 : (multiset_minimum S_before popped_2)) (PreH16 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  TT && emp 
|--
  EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ ((item_key (popped_2)) = (item_key (popped))) ” &&
  “ ((item_data (popped_2)) = (item_data (popped))) ” &&
  “ ((0 : Int) <= ((idx * 2) + 1)) ” &&
  “ (((idx * 2) + 1) < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= (n_pre - 1)) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopReadyState before_key before_data current_key_2 current_data_2 n_pre popped) ”
  &&  emp
)

noncomputable def pop_entail_wit_9 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key_2 (0 : Int)) > (Znth smallest current_key_2 (0 : Int)))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key_2 (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH14 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH15 : (multiset_minimum S_before popped_2)) (PreH16 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  (intArray.full data_pre n_pre (replace_Znth (smallest) ((Znth idx current_data_2 (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_data_2 (0 : Int))) (current_data_2)))))
  ** (intArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key_2 (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_key_2 (0 : Int))) (current_key_2)))))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX current_key : (List Int), EX current_data : (List Int), EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ ((0 : Int) <= ((smallest * 2) + 1)) ” &&
  “ (((smallest * 2) + 1) <= INT_MAX) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre smallest) ”
  &&  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (n_pre : Int) (S_before : (multiset (Int × Int))) (before_key_2 : (List Int)) (before_data_2 : (List Int)) (current_key_2 : (List Int)) (current_data_2 : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key_2 (0 : Int)) > (Znth smallest current_key_2 (0 : Int)))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key_2 (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key_2 before_data_2 n_pre)) (PreH14 : (PrefixMinimum before_key_2 before_data_2 n_pre popped_2)) (PreH15 : (multiset_minimum S_before popped_2)) (PreH16 : (PopLoopState before_key_2 before_data_2 current_key_2 current_data_2 n_pre idx)) ,
  TT && emp 
|--
  EX before_key : (List Int), EX before_data : (List Int), EX popped : (Int × Int),
  “ ((item_key (popped_2)) = (item_key (popped))) ” &&
  “ ((item_data (popped_2)) = (item_data (popped))) ” &&
  “ ((0 : Int) <= ((smallest * 2) + 1)) ” &&
  “ (((smallest * 2) + 1) <= INT_MAX) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data (replace_Znth (smallest) ((Znth idx current_key_2 (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_key_2 (0 : Int))) (current_key_2)))) (replace_Znth (smallest) ((Znth idx current_data_2 (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_data_2 (0 : Int))) (current_data_2)))) n_pre smallest) ”
  &&  emp
)

noncomputable def pop_return_wit_1 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped_2 : (Int × Int)) (result_key : Int) (PreH1 : (((idx * 2) + 1) >= (n_pre - 1))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : ((0 : Int) <= ((idx * 2) + 1))) (PreH9 : (((idx * 2) + 1) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre)) (PreH11 : (PrefixMinimum before_key before_data n_pre popped_2)) (PreH12 : (multiset_minimum S_before popped_2)) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  EX data_out_pre_v : Int, EX popped : (Int × Int), EX key_out_pre_v : Int,
  “ (key_out_pre_v = (item_key (popped))) ” &&
  “ (data_out_pre_v = (item_data (popped))) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  ((key_out_pre) # Int |-> (key_out_pre_v))
  ** ((data_out_pre) # Int |-> (data_out_pre_v))
  ** (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1))
) \/
(
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (current_key : (List Int)) (current_data : (List Int)) (before_key : (List Int)) (before_data : (List Int)) (idx : Int) (result_data : Int) (popped_2 : (Int × Int)) (result_key : Int) (PreH1 : (((idx * 2) + 1) >= (n_pre - 1))) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : ((0 : Int) <= ((idx * 2) + 1))) (PreH9 : (((idx * 2) + 1) <= INT_MAX)) (PreH10 : (heap_representation S_before before_key before_data n_pre)) (PreH11 : (PrefixMinimum before_key before_data n_pre popped_2)) (PreH12 : (multiset_minimum S_before popped_2)) (PreH13 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  EX popped : (Int × Int),
  “ (result_data = (item_data (popped))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1))
)

noncomputable def pop_return_wit_2 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : (left = ((idx * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (n_pre - 1))) (PreH11 : ((0 : Int) <= right)) (PreH12 : (right <= (n_pre - 1))) (PreH13 : ((0 : Int) <= smallest)) (PreH14 : (smallest < (n_pre - 1))) (PreH15 : ((Znth idx current_key (0 : Int)) <= (Znth smallest current_key (0 : Int)))) (PreH16 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH17 : (heap_representation S_before before_key before_data n_pre)) (PreH18 : (PrefixMinimum before_key before_data n_pre popped_2)) (PreH19 : (multiset_minimum S_before popped_2)) (PreH20 : (PopReadyState before_key before_data current_key current_data n_pre popped_2)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  EX data_out_pre_v : Int, EX popped : (Int × Int), EX key_out_pre_v : Int,
  “ (key_out_pre_v = (item_key (popped))) ” &&
  “ (data_out_pre_v = (item_data (popped))) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  ((key_out_pre) # Int |-> (key_out_pre_v))
  ** ((data_out_pre) # Int |-> (data_out_pre_v))
  ** (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1))
) \/
(
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (result_key = (item_key (popped_2)))) (PreH2 : (result_data = (item_data (popped_2)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : (left = ((idx * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (n_pre - 1))) (PreH11 : ((0 : Int) <= right)) (PreH12 : (right <= (n_pre - 1))) (PreH13 : ((0 : Int) <= smallest)) (PreH14 : (smallest < (n_pre - 1))) (PreH15 : ((Znth idx current_key (0 : Int)) <= (Znth smallest current_key (0 : Int)))) (PreH16 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH17 : (heap_representation S_before before_key before_data n_pre)) (PreH18 : (PrefixMinimum before_key before_data n_pre popped_2)) (PreH19 : (multiset_minimum S_before popped_2)) (PreH20 : (PopReadyState before_key before_data current_key current_data n_pre popped_2)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
|--
  EX popped : (Int × Int),
  “ (result_data = (item_data (popped))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1))
)

noncomputable def pop_return_wit_3 : Prop :=
  (
forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (n_pre = 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (multiset_minimum S_before popped_2)) ,
  (store_heap key_pre data_pre (multiset_remove (S_before) (popped_2)) (0 : Int))
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  EX data_out_pre_v : Int, EX popped : (Int × Int), EX key_out_pre_v : Int,
  “ (key_out_pre_v = (item_key (popped))) ” &&
  “ (data_out_pre_v = (item_data (popped))) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  ((key_out_pre) # Int |-> (key_out_pre_v))
  ** ((data_out_pre) # Int |-> (data_out_pre_v))
  ** (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1))
) \/
(
forall (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (n_pre = 1)) (PreH2 : (result_key = (item_key (popped_2)))) (PreH3 : (result_data = (item_data (popped_2)))) (PreH4 : (multiset_minimum S_before popped_2)) ,
  (store_heap key_pre data_pre (multiset_remove (S_before) (popped_2)) (0 : Int))
|--
  EX popped : (Int × Int),
  “ (result_data = (item_data (popped))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (store_heap key_pre data_pre (multiset_remove (S_before) (popped)) (n_pre - 1))
)

noncomputable def pop_partial_solve_wit_1 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre)) (PreH4 : (PrefixMinimum before_key before_data n_pre popped)) (PreH5 : (multiset_minimum S_before popped)) ,
  (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (((key_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) before_key (0 : Int))))
  ** (intArray.missing_i key_pre (0 : Int) (0 : Int) n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_2 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= heap_capacity)) (PreH3 : (heap_representation S_before before_key before_data n_pre)) (PreH4 : (PrefixMinimum before_key before_data n_pre popped)) (PreH5 : (multiset_minimum S_before popped)) ,
  (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (((data_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) before_data (0 : Int))))
  ** (intArray.missing_i data_pre (0 : Int) (0 : Int) n_pre before_data)
  ** (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_3 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (((key_pre + ((n_pre - 1) * sizeof(INT)))) # Int |-> ((Znth (n_pre - 1) before_key (0 : Int))))
  ** (intArray.missing_i key_pre (n_pre - 1) (0 : Int) n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_4 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  (intArray.full key_pre n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (((key_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre (0 : Int) (0 : Int) n_pre before_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_5 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  (intArray.full key_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_key (0 : Int))) (before_key)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre before_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (((data_pre + ((n_pre - 1) * sizeof(INT)))) # Int |-> ((Znth (n_pre - 1) before_data (0 : Int))))
  ** (intArray.missing_i data_pre (n_pre - 1) (0 : Int) n_pre before_data)
  ** (intArray.full key_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_key (0 : Int))) (before_key)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_6 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= (n_pre - 1))) (PreH6 : ((n_pre - 1) < n_pre)) (PreH7 : ((n_pre - 1) <= INT_MAX)) (PreH8 : (heap_representation S_before before_key before_data n_pre)) (PreH9 : (PrefixMinimum before_key before_data n_pre popped)) (PreH10 : (multiset_minimum S_before popped)) ,
  (intArray.full data_pre n_pre before_data)
  ** (intArray.full key_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_key (0 : Int))) (before_key)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ”
  &&  (((data_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre (0 : Int) (0 : Int) n_pre before_data)
  ** (intArray.full key_pre n_pre (replace_Znth ((0 : Int)) ((Znth (n_pre - 1) before_key (0 : Int))) (before_key)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_7 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (right < (n_pre - 1))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : (smallest = left)) (PreH11 : ((0 : Int) <= left)) (PreH12 : (left < (n_pre - 1))) (PreH13 : ((0 : Int) <= right)) (PreH14 : (right <= (n_pre - 1))) (PreH15 : (heap_representation S_before before_key before_data n_pre)) (PreH16 : (PrefixMinimum before_key before_data n_pre popped)) (PreH17 : (multiset_minimum S_before popped)) (PreH18 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (right < (n_pre - 1)) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ (smallest = left) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (n_pre - 1)) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right <= (n_pre - 1)) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((key_pre + (right * sizeof(INT)))) # Int |-> ((Znth right current_key (0 : Int))))
  ** (intArray.missing_i key_pre right (0 : Int) n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_8 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (right < (n_pre - 1))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : (smallest = left)) (PreH11 : ((0 : Int) <= left)) (PreH12 : (left < (n_pre - 1))) (PreH13 : ((0 : Int) <= right)) (PreH14 : (right <= (n_pre - 1))) (PreH15 : (heap_representation S_before before_key before_data n_pre)) (PreH16 : (PrefixMinimum before_key before_data n_pre popped)) (PreH17 : (multiset_minimum S_before popped)) (PreH18 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (right < (n_pre - 1)) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ (smallest = left) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (n_pre - 1)) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right <= (n_pre - 1)) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((key_pre + (left * sizeof(INT)))) # Int |-> ((Znth left current_key (0 : Int))))
  ** (intArray.missing_i key_pre left (0 : Int) n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_9 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : (left = ((idx * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : ((0 : Int) <= smallest)) (PreH10 : (smallest < (n_pre - 1))) (PreH11 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH12 : (heap_representation S_before before_key before_data n_pre)) (PreH13 : (PrefixMinimum before_key before_data n_pre popped)) (PreH14 : (multiset_minimum S_before popped)) (PreH15 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((key_pre + (idx * sizeof(INT)))) # Int |-> ((Znth idx current_key (0 : Int))))
  ** (intArray.missing_i key_pre idx (0 : Int) n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_10 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (result_key = (item_key (popped)))) (PreH2 : (result_data = (item_data (popped)))) (PreH3 : (1 < n_pre)) (PreH4 : (n_pre <= heap_capacity)) (PreH5 : ((0 : Int) <= idx)) (PreH6 : (idx < (n_pre - 1))) (PreH7 : (left = ((idx * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : ((0 : Int) <= smallest)) (PreH10 : (smallest < (n_pre - 1))) (PreH11 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH12 : (heap_representation S_before before_key before_data n_pre)) (PreH13 : (PrefixMinimum before_key before_data n_pre popped)) (PreH14 : (multiset_minimum S_before popped)) (PreH15 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int |-> ((Znth smallest current_key (0 : Int))))
  ** (intArray.missing_i key_pre smallest (0 : Int) n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_11 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int)))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key before_data n_pre)) (PreH14 : (PrefixMinimum before_key before_data n_pre popped)) (PreH15 : (multiset_minimum S_before popped)) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((key_pre + (idx * sizeof(INT)))) # Int |-> ((Znth idx current_key (0 : Int))))
  ** (intArray.missing_i key_pre idx (0 : Int) n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_12 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int)))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key before_data n_pre)) (PreH14 : (PrefixMinimum before_key before_data n_pre popped)) (PreH15 : (multiset_minimum S_before popped)) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int |-> ((Znth smallest current_key (0 : Int))))
  ** (intArray.missing_i key_pre smallest (0 : Int) n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_13 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int)))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key before_data n_pre)) (PreH14 : (PrefixMinimum before_key before_data n_pre popped)) (PreH15 : (multiset_minimum S_before popped)) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((key_pre + (idx * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre idx (0 : Int) n_pre current_key)
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_14 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int)))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key before_data n_pre)) (PreH14 : (PrefixMinimum before_key before_data n_pre popped)) (PreH15 : (multiset_minimum S_before popped)) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre (replace_Znth (idx) ((Znth smallest current_key (0 : Int))) (current_key)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre smallest (0 : Int) n_pre (replace_Znth (idx) ((Znth smallest current_key (0 : Int))) (current_key)))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_15 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int)))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key before_data n_pre)) (PreH14 : (PrefixMinimum before_key before_data n_pre popped)) (PreH15 : (multiset_minimum S_before popped)) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_key (0 : Int))) (current_key)))))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.full data_pre n_pre current_data)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((data_pre + (idx * sizeof(INT)))) # Int |-> ((Znth idx current_data (0 : Int))))
  ** (intArray.missing_i data_pre idx (0 : Int) n_pre current_data)
  ** (intArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_key (0 : Int))) (current_key)))))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_16 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int)))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key before_data n_pre)) (PreH14 : (PrefixMinimum before_key before_data n_pre popped)) (PreH15 : (multiset_minimum S_before popped)) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full data_pre n_pre current_data)
  ** (intArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_key (0 : Int))) (current_key)))))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((data_pre + (smallest * sizeof(INT)))) # Int |-> ((Znth smallest current_data (0 : Int))))
  ** (intArray.missing_i data_pre smallest (0 : Int) n_pre current_data)
  ** (intArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_key (0 : Int))) (current_key)))))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_17 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int)))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key before_data n_pre)) (PreH14 : (PrefixMinimum before_key before_data n_pre popped)) (PreH15 : (multiset_minimum S_before popped)) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full data_pre n_pre current_data)
  ** (intArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_key (0 : Int))) (current_key)))))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((data_pre + (idx * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre idx (0 : Int) n_pre current_data)
  ** (intArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_key (0 : Int))) (current_key)))))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pop_partial_solve_wit_18 : Prop :=
  forall (key_out_pre : Int) (data_out_pre : Int) (n_pre : Int) (data_pre : Int) (key_pre : Int) (S_before : (multiset (Int × Int))) (before_key : (List Int)) (before_data : (List Int)) (current_key : (List Int)) (current_data : (List Int)) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (idx : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int)))) (PreH2 : (result_key = (item_key (popped)))) (PreH3 : (result_data = (item_data (popped)))) (PreH4 : (1 < n_pre)) (PreH5 : (n_pre <= heap_capacity)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx < (n_pre - 1))) (PreH8 : (left = ((idx * 2) + 1))) (PreH9 : (right = (left + 1))) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < (n_pre - 1))) (PreH12 : (PopSelectedChild current_key (n_pre - 1) idx smallest)) (PreH13 : (heap_representation S_before before_key before_data n_pre)) (PreH14 : (PrefixMinimum before_key before_data n_pre popped)) (PreH15 : (multiset_minimum S_before popped)) (PreH16 : (PopLoopState before_key before_data current_key current_data n_pre idx)) ,
  (intArray.full data_pre n_pre (replace_Znth (idx) ((Znth smallest current_data (0 : Int))) (current_data)))
  ** (intArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_key (0 : Int))) (current_key)))))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((Znth idx current_key (0 : Int)) > (Znth smallest current_key (0 : Int))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (1 < n_pre) ” &&
  “ (n_pre <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < (n_pre - 1)) ” &&
  “ (left = ((idx * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < (n_pre - 1)) ” &&
  “ (PopSelectedChild current_key (n_pre - 1) idx smallest) ” &&
  “ (heap_representation S_before before_key before_data n_pre) ” &&
  “ (PrefixMinimum before_key before_data n_pre popped) ” &&
  “ (multiset_minimum S_before popped) ” &&
  “ (PopLoopState before_key before_data current_key current_data n_pre idx) ”
  &&  (((data_pre + (smallest * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre smallest (0 : Int) n_pre (replace_Znth (idx) ((Znth smallest current_data (0 : Int))) (current_data)))
  ** (intArray.full key_pre n_pre (replace_Znth (smallest) ((Znth idx current_key (0 : Int))) ((replace_Znth (idx) ((Znth smallest current_key (0 : Int))) (current_key)))))
  ** (intArray.undef_seg key_pre n_pre heap_capacity)
  ** (intArray.undef_seg data_pre n_pre heap_capacity)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)


structure VC_Correct : Type where
  proof_of_push_safety_wit_1 : push_safety_wit_1
  proof_of_push_safety_wit_2 : push_safety_wit_2
  proof_of_push_safety_wit_3 : push_safety_wit_3
  proof_of_push_safety_wit_4 : push_safety_wit_4
  proof_of_push_safety_wit_5 : push_safety_wit_5
  proof_of_push_partial_solve_wit_1 : push_partial_solve_wit_1
  proof_of_push_partial_solve_wit_2 : push_partial_solve_wit_2
  proof_of_push_partial_solve_wit_3 : push_partial_solve_wit_3
  proof_of_push_partial_solve_wit_4 : push_partial_solve_wit_4
  proof_of_push_partial_solve_wit_5 : push_partial_solve_wit_5
  proof_of_push_partial_solve_wit_6 : push_partial_solve_wit_6
  proof_of_push_partial_solve_wit_7 : push_partial_solve_wit_7
  proof_of_push_partial_solve_wit_8 : push_partial_solve_wit_8
  proof_of_push_partial_solve_wit_9 : push_partial_solve_wit_9
  proof_of_push_partial_solve_wit_10 : push_partial_solve_wit_10
  proof_of_push_partial_solve_wit_11 : push_partial_solve_wit_11
  proof_of_push_partial_solve_wit_12 : push_partial_solve_wit_12
  proof_of_build_safety_wit_1 : build_safety_wit_1
  proof_of_build_safety_wit_2 : build_safety_wit_2
  proof_of_build_safety_wit_3 : build_safety_wit_3
  proof_of_build_safety_wit_4 : build_safety_wit_4
  proof_of_build_safety_wit_5 : build_safety_wit_5
  proof_of_build_safety_wit_6 : build_safety_wit_6
  proof_of_build_safety_wit_7 : build_safety_wit_7
  proof_of_build_safety_wit_8 : build_safety_wit_8
  proof_of_build_safety_wit_9 : build_safety_wit_9
  proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1
  proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2
  proof_of_build_partial_solve_wit_3 : build_partial_solve_wit_3
  proof_of_build_partial_solve_wit_4 : build_partial_solve_wit_4
  proof_of_build_partial_solve_wit_5 : build_partial_solve_wit_5
  proof_of_build_partial_solve_wit_6 : build_partial_solve_wit_6
  proof_of_build_partial_solve_wit_7 : build_partial_solve_wit_7
  proof_of_build_partial_solve_wit_8 : build_partial_solve_wit_8
  proof_of_build_partial_solve_wit_9 : build_partial_solve_wit_9
  proof_of_build_partial_solve_wit_10 : build_partial_solve_wit_10
  proof_of_build_partial_solve_wit_11 : build_partial_solve_wit_11
  proof_of_build_partial_solve_wit_12 : build_partial_solve_wit_12
  proof_of_pop_safety_wit_1 : pop_safety_wit_1
  proof_of_pop_safety_wit_2 : pop_safety_wit_2
  proof_of_pop_safety_wit_3 : pop_safety_wit_3
  proof_of_pop_safety_wit_4 : pop_safety_wit_4
  proof_of_pop_safety_wit_5 : pop_safety_wit_5
  proof_of_pop_safety_wit_6 : pop_safety_wit_6
  proof_of_pop_safety_wit_7 : pop_safety_wit_7
  proof_of_pop_safety_wit_8 : pop_safety_wit_8
  proof_of_pop_safety_wit_9 : pop_safety_wit_9
  proof_of_pop_safety_wit_10 : pop_safety_wit_10
  proof_of_pop_safety_wit_11 : pop_safety_wit_11
  proof_of_pop_safety_wit_12 : pop_safety_wit_12
  proof_of_pop_safety_wit_13 : pop_safety_wit_13
  proof_of_pop_safety_wit_14 : pop_safety_wit_14
  proof_of_pop_safety_wit_15 : pop_safety_wit_15
  proof_of_pop_safety_wit_16 : pop_safety_wit_16
  proof_of_pop_safety_wit_17 : pop_safety_wit_17
  proof_of_pop_safety_wit_18 : pop_safety_wit_18
  proof_of_pop_safety_wit_19 : pop_safety_wit_19
  proof_of_pop_safety_wit_20 : pop_safety_wit_20
  proof_of_pop_safety_wit_21 : pop_safety_wit_21
  proof_of_pop_safety_wit_22 : pop_safety_wit_22
  proof_of_pop_safety_wit_23 : pop_safety_wit_23
  proof_of_pop_safety_wit_24 : pop_safety_wit_24
  proof_of_pop_partial_solve_wit_1 : pop_partial_solve_wit_1
  proof_of_pop_partial_solve_wit_2 : pop_partial_solve_wit_2
  proof_of_pop_partial_solve_wit_3 : pop_partial_solve_wit_3
  proof_of_pop_partial_solve_wit_4 : pop_partial_solve_wit_4
  proof_of_pop_partial_solve_wit_5 : pop_partial_solve_wit_5
  proof_of_pop_partial_solve_wit_6 : pop_partial_solve_wit_6
  proof_of_pop_partial_solve_wit_7 : pop_partial_solve_wit_7
  proof_of_pop_partial_solve_wit_8 : pop_partial_solve_wit_8
  proof_of_pop_partial_solve_wit_9 : pop_partial_solve_wit_9
  proof_of_pop_partial_solve_wit_10 : pop_partial_solve_wit_10
  proof_of_pop_partial_solve_wit_11 : pop_partial_solve_wit_11
  proof_of_pop_partial_solve_wit_12 : pop_partial_solve_wit_12
  proof_of_pop_partial_solve_wit_13 : pop_partial_solve_wit_13
  proof_of_pop_partial_solve_wit_14 : pop_partial_solve_wit_14
  proof_of_pop_partial_solve_wit_15 : pop_partial_solve_wit_15
  proof_of_pop_partial_solve_wit_16 : pop_partial_solve_wit_16
  proof_of_pop_partial_solve_wit_17 : pop_partial_solve_wit_17
  proof_of_pop_partial_solve_wit_18 : pop_partial_solve_wit_18
  proof_of_push_entail_wit_1 : push_entail_wit_1
  proof_of_push_entail_wit_2 : push_entail_wit_2
  proof_of_push_entail_wit_3 : push_entail_wit_3
  proof_of_push_entail_wit_4 : push_entail_wit_4
  proof_of_push_entail_wit_5 : push_entail_wit_5
  proof_of_push_return_wit_1 : push_return_wit_1
  proof_of_push_return_wit_2 : push_return_wit_2
  proof_of_build_entail_wit_1 : build_entail_wit_1
  proof_of_build_entail_wit_2 : build_entail_wit_2
  proof_of_build_entail_wit_3 : build_entail_wit_3
  proof_of_build_entail_wit_4 : build_entail_wit_4
  proof_of_build_entail_wit_5 : build_entail_wit_5
  proof_of_build_entail_wit_6_1 : build_entail_wit_6_1
  proof_of_build_entail_wit_6_2 : build_entail_wit_6_2
  proof_of_build_return_wit_1 : build_return_wit_1
  proof_of_build_return_wit_2 : build_return_wit_2
  proof_of_pop_entail_wit_1 : pop_entail_wit_1
  proof_of_pop_entail_wit_2 : pop_entail_wit_2
  proof_of_pop_entail_wit_3 : pop_entail_wit_3
  proof_of_pop_entail_wit_4 : pop_entail_wit_4
  proof_of_pop_entail_wit_5 : pop_entail_wit_5
  proof_of_pop_entail_wit_6 : pop_entail_wit_6
  proof_of_pop_entail_wit_7_1 : pop_entail_wit_7_1
  proof_of_pop_entail_wit_7_2 : pop_entail_wit_7_2
  proof_of_pop_entail_wit_7_3 : pop_entail_wit_7_3
  proof_of_pop_entail_wit_8 : pop_entail_wit_8
  proof_of_pop_entail_wit_9 : pop_entail_wit_9
  proof_of_pop_return_wit_1 : pop_return_wit_1
  proof_of_pop_return_wit_2 : pop_return_wit_2
  proof_of_pop_return_wit_3 : pop_return_wit_3

end SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_goal
