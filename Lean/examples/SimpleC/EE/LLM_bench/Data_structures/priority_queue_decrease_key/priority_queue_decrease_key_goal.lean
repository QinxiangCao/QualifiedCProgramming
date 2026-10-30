import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance priority_queue_decrease_key_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def pqdk_sift_up_safety_wit_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= child)) (PreH4 : (child < n_pre)) (PreH5 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pqdk_sift_up_safety_wit_2 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (((child - 1) ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def pqdk_sift_up_safety_wit_3 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((child - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (child - 1)) ”

noncomputable def pqdk_sift_up_safety_wit_4 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_sift_up_safety_wit_5 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  ((( &( "parent" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "child" ) )) # Int |-> (child))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def pqdk_sift_up_entail_wit_1 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (PreH1 : ((0 : Int) <= idx_pre)) (PreH2 : (idx_pre < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) ,
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity M n_pre idx_pre)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= idx_pre) ” &&
  “ (idx_pre < n_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre idx_pre) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (PreH1 : ((0 : Int) <= idx_pre)) (PreH2 : (idx_pre < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) ,
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity M n_pre idx_pre)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= idx_pre) ” &&
  “ (idx_pre < n_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre idx_pre) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
)

noncomputable def pqdk_sift_up_entail_wit_2 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values_2)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values_2)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values_2)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= (Z.quot (child - 1) 2)) ” &&
  “ ((Z.quot (child - 1) 2) < child) ” &&
  “ ((Z.quot (child - 1) 2) < n_pre) ” &&
  “ ((Z.quot (child - 1) 2) = (heap_parent (child))) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child)) ,
  TT && emp 
|--
  “ ((Z.quot (child - 1) 2) = (heap_parent (child))) ” &&
  “ ((Z.quot (child - 1) 2) < n_pre) ” &&
  “ ((Z.quot (child - 1) 2) < child) ” &&
  “ ((0 : Int) <= (Z.quot (child - 1) 2)) ”
  &&  emp
)

noncomputable def pqdk_sift_up_entail_wit_2_split_goal_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child)) ,
  ((Z.quot (child - 1) 2) = (heap_parent (child)))

noncomputable def pqdk_sift_up_entail_wit_2_split_goal_2 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child)) ,
  ((Z.quot (child - 1) 2) < n_pre)

noncomputable def pqdk_sift_up_entail_wit_2_split_goal_3 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child)) ,
  ((Z.quot (child - 1) 2) < child)

noncomputable def pqdk_sift_up_entail_wit_2_split_goal_4 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (child : Int) (PreH1 : (child > (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child)) ,
  ((0 : Int) <= (Z.quot (child - 1) 2))

noncomputable def pqdk_sift_up_entail_wit_3 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child)) ,
  (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values_2)
|--
  EX pos_values : (List Int), EX data_values_2 : (List Int), EX key_values_2 : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values_2 (0 : Int)) > (Znth child key_values_2 (0 : Int))) ” &&
  “ ((Znth parent key_values (0 : Int)) = (Znth parent key_values_2 (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) = (Znth parent data_values_2 (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values_2 (0 : Int))) ” &&
  “ ((Znth parent data_values_2 (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values_2 (0 : Int))) ” &&
  “ ((Znth child data_values_2 (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values_2 data_values_2 pos_values data_bound_pre n_pre child) ”
  &&  (intArray.full key_pre n_pre key_values_2)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values_2)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child)) ,
  TT && emp 
|--
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ”
  &&  emp
)

noncomputable def pqdk_sift_up_entail_wit_3_split_goal_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child)) ,
  ((Znth child data_values (0 : Int)) < data_bound_pre)

noncomputable def pqdk_sift_up_entail_wit_3_split_goal_2 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child)) ,
  ((0 : Int) <= (Znth child data_values (0 : Int)))

noncomputable def pqdk_sift_up_entail_wit_3_split_goal_3 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child)) ,
  ((Znth parent data_values (0 : Int)) < data_bound_pre)

noncomputable def pqdk_sift_up_entail_wit_3_split_goal_4 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values_2 data_bound_pre n_pre child)) ,
  ((0 : Int) <= (Znth parent data_values (0 : Int)))

noncomputable def pqdk_sift_up_entail_wit_4 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 (0 : Int)) > (Znth child key_values_2 (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values_2 (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values_2 (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values_2 (0 : Int)))) (PreH13 : ((Znth parent data_values_2 (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values_2 (0 : Int)))) (PreH15 : ((Znth child data_values_2 (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child)) ,
  (intArray.full data_pre n_pre (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))))
  ** (intArray.full key_pre n_pre (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 (0 : Int))) (key_values_2)))))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values_2 (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values_2 (0 : Int))) (child) (pos_values_2)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < n_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre parent) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 (0 : Int)) > (Znth child key_values_2 (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values_2 (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values_2 (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values_2 (0 : Int)))) (PreH13 : ((Znth parent data_values_2 (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values_2 (0 : Int)))) (PreH15 : ((Znth child data_values_2 (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child)) ,
  TT && emp 
|--
  “ (SiftUpState M (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 (0 : Int))) (key_values_2)))) (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))) (replace_Znth ((Znth child data_values_2 (0 : Int))) (parent) ((replace_Znth (tmp_data) (child) (pos_values_2)))) data_bound_pre n_pre parent) ”
  &&  emp
)

noncomputable def pqdk_sift_up_entail_wit_4_split_goal_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values_2 (0 : Int)) > (Znth child key_values_2 (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values_2 (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values_2 (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values_2 (0 : Int)))) (PreH13 : ((Znth parent data_values_2 (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values_2 (0 : Int)))) (PreH15 : ((Znth child data_values_2 (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre child)) ,
  (SiftUpState M (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values_2 (0 : Int))) (key_values_2)))) (replace_Znth (child) (tmp_data) ((replace_Znth (parent) ((Znth child data_values_2 (0 : Int))) (data_values_2)))) (replace_Znth ((Znth child data_values_2 (0 : Int))) (parent) ((replace_Znth (tmp_data) (child) (pos_values_2)))) data_bound_pre n_pre parent)

noncomputable def pqdk_sift_up_return_wit_1 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)
) \/
(
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)
)

noncomputable def pqdk_sift_up_return_wit_1_split_goal_spatial : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (PreH1 : (child <= (0 : Int))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= child)) (PreH5 : (child < n_pre)) (PreH6 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)

noncomputable def pqdk_sift_up_return_wit_2 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) <= (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)
) \/
(
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) <= (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)
)

noncomputable def pqdk_sift_up_return_wit_2_split_goal_spatial : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) <= (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)

noncomputable def pqdk_sift_up_partial_solve_wit_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent key_values (0 : Int))))
  ** (intArray.missing_i key_pre parent (0 : Int) n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_up_partial_solve_wit_2 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int |-> ((Znth child key_values (0 : Int))))
  ** (intArray.missing_i key_pre child (0 : Int) n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_up_partial_solve_wit_3 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent key_values (0 : Int))))
  ** (intArray.missing_i key_pre parent (0 : Int) n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_up_partial_solve_wit_4 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (PreH1 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) < child)) (PreH5 : (child < n_pre)) (PreH6 : ((0 : Int) <= parent)) (PreH7 : (parent < child)) (PreH8 : (parent < n_pre)) (PreH9 : (parent = (heap_parent (child)))) (PreH10 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent data_values (0 : Int))))
  ** (intArray.missing_i data_pre parent (0 : Int) n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_up_partial_solve_wit_5 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values (0 : Int)))) (PreH13 : ((Znth parent data_values (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values (0 : Int)))) (PreH15 : ((Znth child data_values (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth parent key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth parent data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int |-> ((Znth parent data_values (0 : Int))))
  ** (intArray.missing_i data_pre parent (0 : Int) n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_up_partial_solve_wit_6 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values (0 : Int)))) (PreH13 : ((Znth parent data_values (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values (0 : Int)))) (PreH15 : ((Znth child data_values (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth parent key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth parent data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((pos_pre + ((Znth parent data_values (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i pos_pre (Znth parent data_values (0 : Int)) (0 : Int) data_bound_pre pos_values)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_up_partial_solve_wit_7 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values (0 : Int)))) (PreH13 : ((Znth parent data_values (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values (0 : Int)))) (PreH15 : ((Znth child data_values (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth parent key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth parent data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int |-> ((Znth child data_values (0 : Int))))
  ** (intArray.missing_i data_pre child (0 : Int) n_pre data_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_up_partial_solve_wit_8 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values (0 : Int)))) (PreH13 : ((Znth parent data_values (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values (0 : Int)))) (PreH15 : ((Znth child data_values (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full data_pre n_pre data_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth parent key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth parent data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((pos_pre + ((Znth child data_values (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i pos_pre (Znth child data_values (0 : Int)) (0 : Int) data_bound_pre (replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_up_partial_solve_wit_9 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values (0 : Int)))) (PreH13 : ((Znth parent data_values (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values (0 : Int)))) (PreH15 : ((Znth child data_values (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth parent key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth parent data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int |-> ((Znth child key_values (0 : Int))))
  ** (intArray.missing_i key_pre child (0 : Int) n_pre key_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_up_partial_solve_wit_10 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values (0 : Int)))) (PreH13 : ((Znth parent data_values (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values (0 : Int)))) (PreH15 : ((Znth child data_values (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth parent key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth parent data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((key_pre + (parent * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre parent (0 : Int) n_pre key_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_up_partial_solve_wit_11 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values (0 : Int)))) (PreH13 : ((Znth parent data_values (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values (0 : Int)))) (PreH15 : ((Znth child data_values (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre (replace_Znth (parent) ((Znth child key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth parent key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth parent data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int |-> ((Znth child data_values (0 : Int))))
  ** (intArray.missing_i data_pre child (0 : Int) n_pre data_values)
  ** (intArray.full key_pre n_pre (replace_Znth (parent) ((Znth child key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_up_partial_solve_wit_12 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values (0 : Int)))) (PreH13 : ((Znth parent data_values (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values (0 : Int)))) (PreH15 : ((Znth child data_values (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre (replace_Znth (parent) ((Znth child key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth parent key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth parent data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((data_pre + (parent * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre parent (0 : Int) n_pre data_values)
  ** (intArray.full key_pre n_pre (replace_Znth (parent) ((Znth child key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_up_partial_solve_wit_13 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values (0 : Int)))) (PreH13 : ((Znth parent data_values (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values (0 : Int)))) (PreH15 : ((Znth child data_values (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full data_pre n_pre (replace_Znth (parent) ((Znth child data_values (0 : Int))) (data_values)))
  ** (intArray.full key_pre n_pre (replace_Znth (parent) ((Znth child key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth parent key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth parent data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre child (0 : Int) n_pre (replace_Znth (parent) ((Znth child key_values (0 : Int))) (key_values)))
  ** (intArray.full data_pre n_pre (replace_Znth (parent) ((Znth child data_values (0 : Int))) (data_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_up_partial_solve_wit_14 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (child : Int) (parent : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) < child)) (PreH4 : (child < n_pre)) (PreH5 : ((0 : Int) <= parent)) (PreH6 : (parent < child)) (PreH7 : (parent < n_pre)) (PreH8 : (parent = (heap_parent (child)))) (PreH9 : ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int)))) (PreH10 : (tmp_key = (Znth parent key_values (0 : Int)))) (PreH11 : (tmp_data = (Znth parent data_values (0 : Int)))) (PreH12 : ((0 : Int) <= (Znth parent data_values (0 : Int)))) (PreH13 : ((Znth parent data_values (0 : Int)) < data_bound_pre)) (PreH14 : ((0 : Int) <= (Znth child data_values (0 : Int)))) (PreH15 : ((Znth child data_values (0 : Int)) < data_bound_pre)) (PreH16 : (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child)) ,
  (intArray.full key_pre n_pre (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values (0 : Int))) (key_values)))))
  ** (intArray.full data_pre n_pre (replace_Znth (parent) ((Znth child data_values (0 : Int))) (data_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) < child) ” &&
  “ (child < n_pre) ” &&
  “ ((0 : Int) <= parent) ” &&
  “ (parent < child) ” &&
  “ (parent < n_pre) ” &&
  “ (parent = (heap_parent (child))) ” &&
  “ ((Znth parent key_values (0 : Int)) > (Znth child key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth parent key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth parent data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth parent data_values (0 : Int))) ” &&
  “ ((Znth parent data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth child data_values (0 : Int))) ” &&
  “ ((Znth child data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SiftUpState M key_values data_values pos_values data_bound_pre n_pre child) ”
  &&  (((data_pre + (child * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre child (0 : Int) n_pre (replace_Znth (parent) ((Znth child data_values (0 : Int))) (data_values)))
  ** (intArray.full key_pre n_pre (replace_Znth (child) (tmp_key) ((replace_Znth (parent) ((Znth child key_values (0 : Int))) (key_values)))))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth child data_values (0 : Int))) (parent) ((replace_Znth ((Znth parent data_values (0 : Int))) (child) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_down_safety_wit_1 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (((current * 2) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((current * 2) + 1)) ”
) \/
(
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (((current * 2) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((current * 2) + 1)) ”
)

noncomputable def pqdk_sift_down_safety_wit_1_split_goal_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (((current * 2) + 1) <= INT_MAX) ”

noncomputable def pqdk_sift_down_safety_wit_1_split_goal_2 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((INT_MIN) <= ((current * 2) + 1)) ”

noncomputable def pqdk_sift_down_safety_wit_2 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((current * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (current * 2)) ”
) \/
(
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((current * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (current * 2)) ”
)

noncomputable def pqdk_sift_down_safety_wit_2_split_goal_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((current * 2) <= INT_MAX) ”

noncomputable def pqdk_sift_down_safety_wit_2_split_goal_2 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((INT_MIN) <= (current * 2)) ”

noncomputable def pqdk_sift_down_safety_wit_3 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def pqdk_sift_down_safety_wit_4 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_sift_down_safety_wit_5 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (((current * 2) + 1) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (((current * 2) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((current * 2) + 1)) ”

noncomputable def pqdk_sift_down_safety_wit_6 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (((current * 2) + 1) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((current * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (current * 2)) ”

noncomputable def pqdk_sift_down_safety_wit_7 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (((current * 2) + 1) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def pqdk_sift_down_safety_wit_8 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (((current * 2) + 1) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_sift_down_safety_wit_9 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (((current * 2) + 1) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |-> (((current * 2) + 1)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((((current * 2) + 1) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((current * 2) + 1) + 1)) ”

noncomputable def pqdk_sift_down_safety_wit_10 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (((current * 2) + 1) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |-> (((current * 2) + 1)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx_pre))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_sift_down_entail_wit_1 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (PreH1 : ((0 : Int) <= idx_pre)) (PreH2 : (idx_pre < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) ,
  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity M n_pre idx_pre)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= idx_pre) ” &&
  “ (idx_pre < n_pre) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre idx_pre) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (idx_pre : Int) (PreH1 : ((0 : Int) <= idx_pre)) (PreH2 : (idx_pre < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) ,
  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity M n_pre idx_pre)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= idx_pre) ” &&
  “ (idx_pre < n_pre) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre idx_pre) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
)

noncomputable def pqdk_sift_down_entail_wit_2 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (PreH1 : (((current * 2) + 1) < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values_2)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values_2)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values_2)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (((current * 2) + 1) = ((current * 2) + 1)) ” &&
  “ ((((current * 2) + 1) + 1) = (((current * 2) + 1) + 1)) ” &&
  “ (((current * 2) + 1) = ((current * 2) + 1)) ” &&
  “ ((0 : Int) <= ((current * 2) + 1)) ” &&
  “ (((current * 2) + 1) < n_pre) ” &&
  “ ((0 : Int) <= (((current * 2) + 1) + 1)) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_down_entail_wit_3_1 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) < (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values_2)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values_2)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values_2)
|--
  EX data_values : (List Int), EX pos_values : (List Int), EX key_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < n_pre) ” &&
  “ (SelectedChild key_values n_pre current right) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) < (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  TT && emp 
|--
  “ (SelectedChild key_values_2 n_pre current (left + 1)) ”
  &&  emp
)

noncomputable def pqdk_sift_down_entail_wit_3_1_split_goal_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) < (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  (SelectedChild key_values_2 n_pre current (left + 1))

noncomputable def pqdk_sift_down_entail_wit_3_2 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (right >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : (smallest = left)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < n_pre)) (PreH11 : ((0 : Int) <= right)) (PreH12 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values_2)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values_2)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values_2)
|--
  EX data_values : (List Int), EX pos_values : (List Int), EX key_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (right >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : (smallest = left)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < n_pre)) (PreH11 : ((0 : Int) <= right)) (PreH12 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  TT && emp 
|--
  “ (SelectedChild key_values_2 n_pre current left) ”
  &&  emp
)

noncomputable def pqdk_sift_down_entail_wit_3_2_split_goal_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (right >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : (smallest = left)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < n_pre)) (PreH11 : ((0 : Int) <= right)) (PreH12 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  (SelectedChild key_values_2 n_pre current left)

noncomputable def pqdk_sift_down_entail_wit_3_3 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) >= (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values_2)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values_2)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values_2)
|--
  EX data_values : (List Int), EX pos_values : (List Int), EX key_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) >= (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  TT && emp 
|--
  “ (SelectedChild key_values_2 n_pre current left) ”
  &&  emp
)

noncomputable def pqdk_sift_down_entail_wit_3_3_split_goal_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth right key_values_2 (0 : Int)) >= (Znth left key_values_2 (0 : Int)))) (PreH2 : (right < n_pre)) (PreH3 : (n_pre <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= current)) (PreH6 : (current < n_pre)) (PreH7 : (left = ((current * 2) + 1))) (PreH8 : (right = (left + 1))) (PreH9 : (smallest = left)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < n_pre)) (PreH12 : ((0 : Int) <= right)) (PreH13 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  (SelectedChild key_values_2 n_pre current left)

noncomputable def pqdk_sift_down_entail_wit_4 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current)) ,
  (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values_2)
|--
  EX pos_values : (List Int), EX data_values_2 : (List Int), EX key_values_2 : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values_2 (0 : Int)) > (Znth smallest key_values_2 (0 : Int))) ” &&
  “ ((Znth current key_values (0 : Int)) = (Znth current key_values_2 (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) = (Znth current data_values_2 (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values_2 (0 : Int))) ” &&
  “ ((Znth current data_values_2 (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values_2 (0 : Int))) ” &&
  “ ((Znth smallest data_values_2 (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values_2 n_pre current smallest) ” &&
  “ (SiftDownState M key_values_2 data_values_2 pos_values data_bound_pre n_pre current) ”
  &&  (intArray.full key_pre n_pre key_values_2)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values_2)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current)) ,
  TT && emp 
|--
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ (current < smallest) ” &&
  “ (((current * 2) + 1) < n_pre) ”
  &&  emp
)

noncomputable def pqdk_sift_down_entail_wit_4_split_goal_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current)) ,
  ((Znth smallest data_values (0 : Int)) < data_bound_pre)

noncomputable def pqdk_sift_down_entail_wit_4_split_goal_2 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current)) ,
  ((0 : Int) <= (Znth smallest data_values (0 : Int)))

noncomputable def pqdk_sift_down_entail_wit_4_split_goal_3 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current)) ,
  ((Znth current data_values (0 : Int)) < data_bound_pre)

noncomputable def pqdk_sift_down_entail_wit_4_split_goal_4 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current)) ,
  ((0 : Int) <= (Znth current data_values (0 : Int)))

noncomputable def pqdk_sift_down_entail_wit_4_split_goal_5 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current)) ,
  (current < smallest)

noncomputable def pqdk_sift_down_entail_wit_4_split_goal_6 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values_2 data_bound_pre n_pre current)) ,
  (((current * 2) + 1) < n_pre)

noncomputable def pqdk_sift_down_entail_wit_5 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 (0 : Int)) > (Znth smallest key_values_2 (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values_2 (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values_2 (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values_2 (0 : Int)))) (PreH17 : ((Znth current data_values_2 (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values_2 (0 : Int)))) (PreH19 : ((Znth smallest data_values_2 (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest)) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  (intArray.full data_pre n_pre (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))))
  ** (intArray.full key_pre n_pre (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 (0 : Int))) (key_values_2)))))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values_2 (0 : Int))) (current) ((replace_Znth ((Znth current data_values_2 (0 : Int))) (smallest) (pos_values_2)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre smallest) ”
  &&  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 (0 : Int)) > (Znth smallest key_values_2 (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values_2 (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values_2 (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values_2 (0 : Int)))) (PreH17 : ((Znth current data_values_2 (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values_2 (0 : Int)))) (PreH19 : ((Znth smallest data_values_2 (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest)) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  TT && emp 
|--
  “ (SiftDownState M (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 (0 : Int))) (key_values_2)))) (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))) (replace_Znth ((Znth smallest data_values_2 (0 : Int))) (current) ((replace_Znth (tmp_data) (smallest) (pos_values_2)))) data_bound_pre n_pre smallest) ”
  &&  emp
)

noncomputable def pqdk_sift_down_entail_wit_5_split_goal_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (data_bound_pre : Int) (n_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values_2 (0 : Int)) > (Znth smallest key_values_2 (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values_2 (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values_2 (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values_2 (0 : Int)))) (PreH17 : ((Znth current data_values_2 (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values_2 (0 : Int)))) (PreH19 : ((Znth smallest data_values_2 (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values_2 n_pre current smallest)) (PreH21 : (SiftDownState M key_values_2 data_values_2 pos_values_2 data_bound_pre n_pre current)) ,
  (SiftDownState M (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values_2 (0 : Int))) (key_values_2)))) (replace_Znth (smallest) (tmp_data) ((replace_Znth (current) ((Znth smallest data_values_2 (0 : Int))) (data_values_2)))) (replace_Znth ((Znth smallest data_values_2 (0 : Int))) (current) ((replace_Znth (tmp_data) (smallest) (pos_values_2)))) data_bound_pre n_pre smallest)

noncomputable def pqdk_sift_down_return_wit_1 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (((current * 2) + 1) >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)
) \/
(
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (((current * 2) + 1) >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)
)

noncomputable def pqdk_sift_down_return_wit_1_split_goal_spatial : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (PreH1 : (((current * 2) + 1) >= n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)

noncomputable def pqdk_sift_down_return_wit_2 : Prop :=
  (
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) <= (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)
) \/
(
forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) <= (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)
)

noncomputable def pqdk_sift_down_return_wit_2_split_goal_spatial : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) <= (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M n_pre)

noncomputable def pqdk_sift_down_partial_solve_wit_1 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (right < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : (smallest = left)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < n_pre)) (PreH11 : ((0 : Int) <= right)) (PreH12 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (right < n_pre) ” &&
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ (smallest = left) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((key_pre + (right * sizeof(INT)))) # Int |-> ((Znth right key_values (0 : Int))))
  ** (intArray.missing_i key_pre right (0 : Int) n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_down_partial_solve_wit_2 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (right < n_pre)) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : (smallest = left)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < n_pre)) (PreH11 : ((0 : Int) <= right)) (PreH12 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (right < n_pre) ” &&
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ (smallest = left) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((key_pre + (left * sizeof(INT)))) # Int |-> ((Znth left key_values (0 : Int))))
  ** (intArray.missing_i key_pre left (0 : Int) n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_down_partial_solve_wit_3 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= smallest)) (PreH8 : (smallest < n_pre)) (PreH9 : (SelectedChild key_values n_pre current smallest)) (PreH10 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((key_pre + (current * sizeof(INT)))) # Int |-> ((Znth current key_values (0 : Int))))
  ** (intArray.missing_i key_pre current (0 : Int) n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_down_partial_solve_wit_4 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= smallest)) (PreH8 : (smallest < n_pre)) (PreH9 : (SelectedChild key_values n_pre current smallest)) (PreH10 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int |-> ((Znth smallest key_values (0 : Int))))
  ** (intArray.missing_i key_pre smallest (0 : Int) n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_down_partial_solve_wit_5 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((key_pre + (current * sizeof(INT)))) # Int |-> ((Znth current key_values (0 : Int))))
  ** (intArray.missing_i key_pre current (0 : Int) n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_down_partial_solve_wit_6 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (PreH1 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH2 : (n_pre <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= current)) (PreH5 : (current < n_pre)) (PreH6 : (left = ((current * 2) + 1))) (PreH7 : (right = (left + 1))) (PreH8 : ((0 : Int) <= smallest)) (PreH9 : (smallest < n_pre)) (PreH10 : (SelectedChild key_values n_pre current smallest)) (PreH11 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((data_pre + (current * sizeof(INT)))) # Int |-> ((Znth current data_values (0 : Int))))
  ** (intArray.missing_i data_pre current (0 : Int) n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_down_partial_solve_wit_7 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values (0 : Int)))) (PreH17 : ((Znth current data_values (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values (0 : Int)))) (PreH19 : ((Znth smallest data_values (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest)) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth current key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth current data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((data_pre + (current * sizeof(INT)))) # Int |-> ((Znth current data_values (0 : Int))))
  ** (intArray.missing_i data_pre current (0 : Int) n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_sift_down_partial_solve_wit_8 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values (0 : Int)))) (PreH17 : ((Znth current data_values (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values (0 : Int)))) (PreH19 : ((Znth smallest data_values (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest)) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth current key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth current data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((pos_pre + ((Znth current data_values (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i pos_pre (Znth current data_values (0 : Int)) (0 : Int) data_bound_pre pos_values)
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_down_partial_solve_wit_9 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values (0 : Int)))) (PreH17 : ((Znth current data_values (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values (0 : Int)))) (PreH19 : ((Znth smallest data_values (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest)) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth current key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth current data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((data_pre + (smallest * sizeof(INT)))) # Int |-> ((Znth smallest data_values (0 : Int))))
  ** (intArray.missing_i data_pre smallest (0 : Int) n_pre data_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_down_partial_solve_wit_10 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values (0 : Int)))) (PreH17 : ((Znth current data_values (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values (0 : Int)))) (PreH19 : ((Znth smallest data_values (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest)) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full data_pre n_pre data_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth current key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth current data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((pos_pre + ((Znth smallest data_values (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i pos_pre (Znth smallest data_values (0 : Int)) (0 : Int) data_bound_pre (replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_down_partial_solve_wit_11 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values (0 : Int)))) (PreH17 : ((Znth current data_values (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values (0 : Int)))) (PreH19 : ((Znth smallest data_values (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest)) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre key_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth current key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth current data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int |-> ((Znth smallest key_values (0 : Int))))
  ** (intArray.missing_i key_pre smallest (0 : Int) n_pre key_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_down_partial_solve_wit_12 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values (0 : Int)))) (PreH17 : ((Znth current data_values (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values (0 : Int)))) (PreH19 : ((Znth smallest data_values (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest)) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre key_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth current key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth current data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((key_pre + (current * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre current (0 : Int) n_pre key_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_down_partial_solve_wit_13 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values (0 : Int)))) (PreH17 : ((Znth current data_values (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values (0 : Int)))) (PreH19 : ((Znth smallest data_values (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest)) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre (replace_Znth (current) ((Znth smallest key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.full data_pre n_pre data_values)
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth current key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth current data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((data_pre + (smallest * sizeof(INT)))) # Int |-> ((Znth smallest data_values (0 : Int))))
  ** (intArray.missing_i data_pre smallest (0 : Int) n_pre data_values)
  ** (intArray.full key_pre n_pre (replace_Znth (current) ((Znth smallest key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_down_partial_solve_wit_14 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values (0 : Int)))) (PreH17 : ((Znth current data_values (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values (0 : Int)))) (PreH19 : ((Znth smallest data_values (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest)) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full data_pre n_pre data_values)
  ** (intArray.full key_pre n_pre (replace_Znth (current) ((Znth smallest key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth current key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth current data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((data_pre + (current * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre current (0 : Int) n_pre data_values)
  ** (intArray.full key_pre n_pre (replace_Znth (current) ((Znth smallest key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_down_partial_solve_wit_15 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values (0 : Int)))) (PreH17 : ((Znth current data_values (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values (0 : Int)))) (PreH19 : ((Znth smallest data_values (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest)) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full data_pre n_pre (replace_Znth (current) ((Znth smallest data_values (0 : Int))) (data_values)))
  ** (intArray.full key_pre n_pre (replace_Znth (current) ((Znth smallest key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth current key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth current data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((key_pre + (smallest * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre smallest (0 : Int) n_pre (replace_Znth (current) ((Znth smallest key_values (0 : Int))) (key_values)))
  ** (intArray.full data_pre n_pre (replace_Znth (current) ((Znth smallest data_values (0 : Int))) (data_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_sift_down_partial_solve_wit_16 : Prop :=
  forall (capacity : Int) (M : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (n_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (current : Int) (left : Int) (right : Int) (smallest : Int) (tmp_key : Int) (tmp_data : Int) (PreH1 : (n_pre <= capacity)) (PreH2 : (capacity <= heap_capacity)) (PreH3 : ((0 : Int) <= current)) (PreH4 : (current < n_pre)) (PreH5 : (left = ((current * 2) + 1))) (PreH6 : (right = (left + 1))) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left < n_pre)) (PreH9 : ((0 : Int) <= right)) (PreH10 : ((0 : Int) <= smallest)) (PreH11 : (smallest < n_pre)) (PreH12 : (current < smallest)) (PreH13 : ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int)))) (PreH14 : (tmp_key = (Znth current key_values (0 : Int)))) (PreH15 : (tmp_data = (Znth current data_values (0 : Int)))) (PreH16 : ((0 : Int) <= (Znth current data_values (0 : Int)))) (PreH17 : ((Znth current data_values (0 : Int)) < data_bound_pre)) (PreH18 : ((0 : Int) <= (Znth smallest data_values (0 : Int)))) (PreH19 : ((Znth smallest data_values (0 : Int)) < data_bound_pre)) (PreH20 : (SelectedChild key_values n_pre current smallest)) (PreH21 : (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current)) ,
  (intArray.full key_pre n_pre (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values (0 : Int))) (key_values)))))
  ** (intArray.full data_pre n_pre (replace_Znth (current) ((Znth smallest data_values (0 : Int))) (data_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)
|--
  “ (n_pre <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= current) ” &&
  “ (current < n_pre) ” &&
  “ (left = ((current * 2) + 1)) ” &&
  “ (right = (left + 1)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < n_pre) ” &&
  “ ((0 : Int) <= right) ” &&
  “ ((0 : Int) <= smallest) ” &&
  “ (smallest < n_pre) ” &&
  “ (current < smallest) ” &&
  “ ((Znth current key_values (0 : Int)) > (Znth smallest key_values (0 : Int))) ” &&
  “ (tmp_key = (Znth current key_values (0 : Int))) ” &&
  “ (tmp_data = (Znth current data_values (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth current data_values (0 : Int))) ” &&
  “ ((Znth current data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth smallest data_values (0 : Int))) ” &&
  “ ((Znth smallest data_values (0 : Int)) < data_bound_pre) ” &&
  “ (SelectedChild key_values n_pre current smallest) ” &&
  “ (SiftDownState M key_values data_values pos_values data_bound_pre n_pre current) ”
  &&  (((data_pre + (smallest * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre smallest (0 : Int) n_pre (replace_Znth (current) ((Znth smallest data_values (0 : Int))) (data_values)))
  ** (intArray.full key_pre n_pre (replace_Znth (smallest) (tmp_key) ((replace_Znth (current) ((Znth smallest key_values (0 : Int))) (key_values)))))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth smallest data_values (0 : Int))) (current) ((replace_Znth ((Znth current data_values (0 : Int))) (smallest) (pos_values)))))
  ** (intArray.undef_seg key_pre n_pre capacity)
  ** (intArray.undef_seg data_pre n_pre capacity)

noncomputable def pqdk_push_safety_wit_1 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)))
  ** (intArray.full data_pre (n + 1) (data_values ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((size_pre) # Int |-> (n))
|--
  “ ((n + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n + 1)) ”
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)))
  ** (intArray.full data_pre (n + 1) (data_values ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((size_pre) # Int |-> (n))
|--
  “ ((n + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n + 1)) ”
)

noncomputable def pqdk_push_safety_wit_1_split_goal_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)))
  ** (intArray.full data_pre (n + 1) (data_values ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((size_pre) # Int |-> (n))
|--
  “ ((n + 1) <= INT_MAX) ”

noncomputable def pqdk_push_safety_wit_1_split_goal_2 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)))
  ** (intArray.full data_pre (n + 1) (data_values ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((size_pre) # Int |-> (n))
|--
  “ ((INT_MIN) <= (n + 1)) ”

noncomputable def pqdk_push_safety_wit_2 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)))
  ** (intArray.full data_pre (n + 1) (data_values ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((size_pre) # Int |-> (n))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_push_safety_wit_3 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((size_pre) # Int |-> ((n + 1)))
  ** (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1) n)
|--
  “ ((n + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n + 1)) ”

noncomputable def pqdk_push_safety_wit_4 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((size_pre) # Int |-> ((n + 1)))
  ** (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1) n)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_push_entail_wit_1 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) ,
  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_absent M_before data_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_absent M_before data_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
)

noncomputable def pqdk_push_entail_wit_2 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)))
  ** (intArray.full data_pre (n + 1) (data_values ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((size_pre) # Int |-> ((n + 1)))
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ”
  &&  ((size_pre) # Int |-> ((n + 1)))
  ** (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1) n)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)))
  ** (intArray.full data_pre (n + 1) (data_values ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
|--
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1) n)
)

noncomputable def pqdk_push_entail_wit_2_split_goal_spatial : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (data_x_pre) (n) (pos_values)))
  ** (intArray.full data_pre (n + 1) (data_values ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
|--
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1) n)

noncomputable def pqdk_push_return_wit_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1))
  ** ((size_pre) # Int |-> ((n + 1)))
|--
  ((size_pre) # Int |-> ((n + 1)))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1))

noncomputable def pqdk_push_partial_solve_wit_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_absent M_before data_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (((key_pre + (n * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_push_partial_solve_wit_2 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_absent M_before data_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (((data_pre + (n * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full data_pre n data_values)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_push_partial_solve_wit_3 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full data_pre (n + 1) (data_values ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_absent M_before data_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (((pos_pre + (data_x_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i pos_pre data_x_pre (0 : Int) data_bound_pre pos_values)
  ** (intArray.full data_pre (n + 1) (data_values ++ (data_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg data_pre (n + 1) capacity)
  ** (intArray.full key_pre (n + 1) (key_values ++ (key_x_pre :: (@List.nil Int))))
  ** (intArray.undef_seg key_pre (n + 1) capacity)
  ** ((size_pre) # Int |-> (n))

noncomputable def pqdk_push_partial_solve_wit_4_pure : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((size_pre) # Int |-> ((n + 1)))
  ** (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1) n)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < (n + 1)) ” &&
  “ ((n + 1) <= capacity) ” &&
  “ (capacity <= heap_capacity) ”

noncomputable def pqdk_push_partial_solve_wit_4_aux : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  ((size_pre) # Int |-> ((n + 1)))
  ** (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1) n)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < (n + 1)) ” &&
  “ ((n + 1) <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ”
  &&  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1) n)
  ** ((size_pre) # Int |-> ((n + 1)))

noncomputable def pqdk_push_partial_solve_wit_4 : Prop := pqdk_push_partial_solve_wit_4_pure -> pqdk_push_partial_solve_wit_4_aux

noncomputable def pqdk_decrease_key_entail_wit_1 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) ,
  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ ((0 : Int) <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ ((0 : Int) <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
)

noncomputable def pqdk_decrease_key_entail_wit_2 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre pos_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values_2)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values_2)
  ** (intArray.undef_seg data_pre n capacity)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values_2 : (List Int),
  “ ((0 : Int) <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= (Znth data_x_pre pos_values (0 : Int))) ” &&
  “ ((Znth data_x_pre pos_values (0 : Int)) < n) ” &&
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ” &&
  “ (heap_index_of M_before data_values pos_values_2 data_x_pre (Znth data_x_pre pos_values (0 : Int))) ” &&
  “ (heap_representation M_before key_values data_values pos_values_2 data_bound_pre n) ”
  &&  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values_2)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n)) ,
  TT && emp 
|--
  “ (heap_index_of M_before data_values_2 pos_values data_x_pre (Znth data_x_pre pos_values (0 : Int))) ” &&
  “ ((Znth data_x_pre pos_values (0 : Int)) < n) ” &&
  “ ((0 : Int) <= (Znth data_x_pre pos_values (0 : Int))) ”
  &&  emp
)

noncomputable def pqdk_decrease_key_entail_wit_2_split_goal_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n)) ,
  (heap_index_of M_before data_values_2 pos_values data_x_pre (Znth data_x_pre pos_values (0 : Int)))

noncomputable def pqdk_decrease_key_entail_wit_2_split_goal_2 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n)) ,
  ((Znth data_x_pre pos_values (0 : Int)) < n)

noncomputable def pqdk_decrease_key_entail_wit_2_split_goal_3 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n)) ,
  ((0 : Int) <= (Znth data_x_pre pos_values (0 : Int)))

noncomputable def pqdk_decrease_key_entail_wit_3 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (idx : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx < n)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_index_of M_before data_values pos_values data_x_pre idx)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full key_pre n (replace_Znth (idx) (key_x_pre) (key_values)))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < n) ”
  &&  ((size_pre) # Int |-> (n))
  ** (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (idx : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx < n)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_index_of M_before data_values pos_values data_x_pre idx)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full key_pre n (replace_Znth (idx) (key_x_pre) (key_values)))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx)
)

noncomputable def pqdk_decrease_key_entail_wit_3_split_goal_spatial : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (idx : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx < n)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_index_of M_before data_values pos_values data_x_pre idx)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full key_pre n (replace_Znth (idx) (key_x_pre) (key_values)))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx)

noncomputable def pqdk_decrease_key_return_wit_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (idx : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx < n)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n)
  ** ((size_pre) # Int |-> (n))
|--
  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n)

noncomputable def pqdk_decrease_key_partial_solve_wit_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (((pos_pre + (data_x_pre * sizeof(INT)))) # Int |-> ((Znth data_x_pre pos_values (0 : Int))))
  ** (intArray.missing_i pos_pre data_x_pre (0 : Int) data_bound_pre pos_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)

noncomputable def pqdk_decrease_key_partial_solve_wit_2 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (idx : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx < n)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_index_of M_before data_values pos_values data_x_pre idx)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < n) ” &&
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ” &&
  “ (heap_index_of M_before data_values pos_values data_x_pre idx) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (((key_pre + (idx * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre idx (0 : Int) n key_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)

noncomputable def pqdk_decrease_key_partial_solve_wit_3_pure : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (idx : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx < n)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** ((size_pre) # Int |-> (n))
  ** (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx)
|--
  “ ((0 : Int) <= idx) ” &&
  “ (idx < n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ”

noncomputable def pqdk_decrease_key_partial_solve_wit_3_aux : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (idx : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= idx)) (PreH5 : (idx < n)) ,
  ((size_pre) # Int |-> (n))
  ** (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx)
|--
  “ ((0 : Int) <= idx) ” &&
  “ (idx < n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx < n) ”
  &&  (store_sift_up key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n idx)
  ** ((size_pre) # Int |-> (n))

noncomputable def pqdk_decrease_key_partial_solve_wit_3 : Prop := pqdk_decrease_key_partial_solve_wit_3_pure -> pqdk_decrease_key_partial_solve_wit_3_aux

noncomputable def pqdk_update_or_push_safety_wit_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre pos_values)
  ** ((( &( "idx" ) )) # Int |-> ((Znth data_x_pre pos_values (0 : Int))))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pqdk_update_or_push_entail_wit_1 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) ,
  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_update_or_add_pre M_before data_x_pre key_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_update_or_add_pre M_before data_x_pre key_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
)

noncomputable def pqdk_update_or_push_entail_wit_2 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((Znth data_x_pre pos_values (0 : Int)) < (0 : Int))) (PreH2 : ((0 : Int) <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre pos_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_absent M_before data_x_pre) ”
  &&  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((Znth data_x_pre pos_values (0 : Int)) < (0 : Int))) (PreH2 : ((0 : Int) <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre pos_values)
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
|--
  “ (partial_map_absent M_before data_x_pre) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
)

noncomputable def pqdk_update_or_push_entail_wit_2_split_goal_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((Znth data_x_pre pos_values (0 : Int)) < (0 : Int))) (PreH2 : ((0 : Int) <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre pos_values)
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
|--
  “ (partial_map_absent M_before data_x_pre) ”

noncomputable def pqdk_update_or_push_entail_wit_2_split_goal_spatial : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((Znth data_x_pre pos_values (0 : Int)) < (0 : Int))) (PreH2 : ((0 : Int) <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre pos_values)
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)

noncomputable def pqdk_update_or_push_entail_wit_3 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((Znth data_x_pre pos_values (0 : Int)) >= (0 : Int))) (PreH2 : ((0 : Int) <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre pos_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ”
  &&  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((Znth data_x_pre pos_values (0 : Int)) >= (0 : Int))) (PreH2 : ((0 : Int) <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre pos_values)
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
|--
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
)

noncomputable def pqdk_update_or_push_entail_wit_3_split_goal_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((Znth data_x_pre pos_values (0 : Int)) >= (0 : Int))) (PreH2 : ((0 : Int) <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre pos_values)
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
|--
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ”

noncomputable def pqdk_update_or_push_entail_wit_3_split_goal_spatial : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((Znth data_x_pre pos_values (0 : Int)) >= (0 : Int))) (PreH2 : ((0 : Int) <= n)) (PreH3 : (n < capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : ((0 : Int) <= data_x_pre)) (PreH6 : (data_x_pre < data_bound_pre)) (PreH7 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre pos_values)
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)

noncomputable def pqdk_update_or_push_entail_wit_4_1 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) ,
  ((size_pre) # Int |-> ((n + 1)))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1))
|--
  EX n_after : Int,
  “ (partial_map_update_or_add_size M_before n n_after data_x_pre key_x_pre) ”
  &&  ((size_pre) # Int |-> (n_after))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n_after)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1))
|--
  “ (partial_map_update_or_add_size M_before n (n + 1) data_x_pre key_x_pre) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) (n + 1))
)

noncomputable def pqdk_update_or_push_entail_wit_4_1_split_goal_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1))
|--
  “ (partial_map_update_or_add_size M_before n (n + 1) data_x_pre key_x_pre) ”

noncomputable def pqdk_update_or_push_entail_wit_4_1_split_goal_spatial : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_add (M_before) (data_x_pre) (key_x_pre)) (n + 1))
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) (n + 1))

noncomputable def pqdk_update_or_push_entail_wit_4_2 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) ,
  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n)
|--
  EX n_after : Int,
  “ (partial_map_update_or_add_size M_before n n_after data_x_pre key_x_pre) ”
  &&  ((size_pre) # Int |-> (n_after))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n_after)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n)
|--
  “ (partial_map_update_or_add_size M_before n n data_x_pre key_x_pre) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n)
)

noncomputable def pqdk_update_or_push_entail_wit_4_2_split_goal_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n)
|--
  “ (partial_map_update_or_add_size M_before n n data_x_pre key_x_pre) ”

noncomputable def pqdk_update_or_push_entail_wit_4_2_split_goal_spatial : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update (M_before) (data_x_pre) (key_x_pre)) n)
|--
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n)

noncomputable def pqdk_update_or_push_return_wit_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (n_after_2 : Int) (PreH1 : (partial_map_update_or_add_size M_before n n_after_2 data_x_pre key_x_pre)) ,
  ((size_pre) # Int |-> (n_after_2))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n_after_2)
|--
  EX n_after : Int,
  “ (partial_map_update_or_add_size M_before n n_after data_x_pre key_x_pre) ”
  &&  ((size_pre) # Int |-> (n_after))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_update_or_add (M_before) (data_x_pre) (key_x_pre)) n_after)

noncomputable def pqdk_update_or_push_partial_solve_wit_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_update_or_add_pre M_before data_x_pre key_x_pre)) (PreH7 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_update_or_add_pre M_before data_x_pre key_x_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (((pos_pre + (data_x_pre * sizeof(INT)))) # Int |-> ((Znth data_x_pre pos_values (0 : Int))))
  ** (intArray.missing_i pos_pre data_x_pre (0 : Int) data_bound_pre pos_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)

noncomputable def pqdk_update_or_push_partial_solve_wit_2_pure : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (idx : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_absent M_before data_x_pre) ”

noncomputable def pqdk_update_or_push_partial_solve_wit_2_aux : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_absent M_before data_x_pre)) ,
  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_absent M_before data_x_pre) ” &&
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_absent M_before data_x_pre) ”
  &&  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)

noncomputable def pqdk_update_or_push_partial_solve_wit_2 : Prop := pqdk_update_or_push_partial_solve_wit_2_pure -> pqdk_update_or_push_partial_solve_wit_2_aux

noncomputable def pqdk_update_or_push_partial_solve_wit_3_pure : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (idx : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_x" ) )) # Int |-> (data_x_pre))
  ** ((( &( "key_x" ) )) # Int |-> (key_x_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ”

noncomputable def pqdk_update_or_push_partial_solve_wit_3_aux : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_x_pre : Int) (key_x_pre : Int) (PreH1 : ((0 : Int) <= n)) (PreH2 : (n < capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : ((0 : Int) <= data_x_pre)) (PreH5 : (data_x_pre < data_bound_pre)) (PreH6 : (partial_map_decrease_key_pre M_before data_x_pre key_x_pre)) ,
  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  “ ((0 : Int) <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ” &&
  “ ((0 : Int) <= n) ” &&
  “ (n < capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= data_x_pre) ” &&
  “ (data_x_pre < data_bound_pre) ” &&
  “ (partial_map_decrease_key_pre M_before data_x_pre key_x_pre) ”
  &&  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)

noncomputable def pqdk_update_or_push_partial_solve_wit_3 : Prop := pqdk_update_or_push_partial_solve_wit_3_pure -> pqdk_update_or_push_partial_solve_wit_3_aux

noncomputable def pqdk_pop_safety_wit_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  ((( &( "result_key" ) )) # Int |->_)
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pqdk_pop_safety_wit_2 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  ((( &( "result_data" ) )) # Int |->_)
  ** (intArray.full key_pre n key_values)
  ** ((( &( "result_key" ) )) # Int |-> ((Znth (0 : Int) key_values (0 : Int))))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pqdk_pop_safety_wit_3 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (Znth (0 : Int) key_values (0 : Int)))) (PreH2 : (result_data = (Znth (0 : Int) data_values (0 : Int)))) (PreH3 : (1 <= n)) (PreH4 : (n <= capacity)) (PreH5 : (capacity <= heap_capacity)) (PreH6 : ((0 : Int) <= result_data)) (PreH7 : (result_data < data_bound_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def pqdk_pop_safety_wit_4 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (Znth (0 : Int) key_values (0 : Int)))) (PreH2 : (result_data = (Znth (0 : Int) data_values (0 : Int)))) (PreH3 : (1 <= n)) (PreH4 : (n <= capacity)) (PreH5 : (capacity <= heap_capacity)) (PreH6 : ((0 : Int) <= result_data)) (PreH7 : (result_data < data_bound_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_pop_safety_wit_5 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (Znth (0 : Int) key_values (0 : Int)))) (PreH2 : (result_data = (Znth (0 : Int) data_values (0 : Int)))) (PreH3 : (1 <= n)) (PreH4 : (n <= capacity)) (PreH5 : (capacity <= heap_capacity)) (PreH6 : ((0 : Int) <= result_data)) (PreH7 : (result_data < data_bound_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (result_data) ((-1)) (pos_values)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_pop_safety_wit_6 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (n = 1)) (PreH2 : (result_key = (Znth (0 : Int) key_values (0 : Int)))) (PreH3 : (result_data = (Znth (0 : Int) data_values (0 : Int)))) (PreH4 : (1 <= n)) (PreH5 : (n <= capacity)) (PreH6 : (capacity <= heap_capacity)) (PreH7 : ((0 : Int) <= result_data)) (PreH8 : (result_data < data_bound_pre)) (PreH9 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (result_data) ((-1)) (pos_values)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pqdk_pop_safety_wit_7 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((n - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n - 1)) ”

noncomputable def pqdk_pop_safety_wit_8 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_pop_safety_wit_9 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full data_pre n data_values)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pqdk_pop_safety_wit_10 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pqdk_pop_safety_wit_11 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((n - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n - 1)) ”

noncomputable def pqdk_pop_safety_wit_12 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_pop_safety_wit_13 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pqdk_pop_safety_wit_14 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((n - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n - 1)) ”

noncomputable def pqdk_pop_safety_wit_15 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_pop_safety_wit_16 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full data_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) data_values (0 : Int))) (data_values)))
  ** (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((n - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n - 1)) ”

noncomputable def pqdk_pop_safety_wit_17 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full data_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) data_values (0 : Int))) (data_values)))
  ** (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_pop_safety_wit_18 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : ((0 : Int) < (n - 1))) (PreH3 : ((n - 1) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> ((n - 1)))
  ** (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1) (0 : Int))
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((n - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n - 1)) ”

noncomputable def pqdk_pop_safety_wit_19 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : ((0 : Int) < (n - 1))) (PreH3 : ((n - 1) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> ((n - 1)))
  ** (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1) (0 : Int))
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pqdk_pop_safety_wit_20 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : ((0 : Int) < (n - 1))) (PreH3 : ((n - 1) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> ((n - 1)))
  ** (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1) (0 : Int))
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pqdk_pop_entail_wit_1 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  ((size_pre) # Int |-> (n))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity M_before n)
|--
  EX key_values : (List Int), EX data_values : (List Int), EX pos_values : (List Int),
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
)

noncomputable def pqdk_pop_entail_wit_2 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values_2 data_bound_pre n)) ,
  (intArray.full data_pre n data_values)
  ** (intArray.full key_pre n key_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values_2)
  ** ((data_out_pre) # Int |-> ((Znth (0 : Int) data_values (0 : Int))))
  ** ((key_out_pre) # Int |-> ((Znth (0 : Int) key_values (0 : Int))))
|--
  EX pos_values : (List Int), EX data_values_2 : (List Int), EX key_values_2 : (List Int),
  “ ((Znth (0 : Int) key_values (0 : Int)) = (Znth (0 : Int) key_values_2 (0 : Int))) ” &&
  “ ((Znth (0 : Int) data_values (0 : Int)) = (Znth (0 : Int) data_values_2 (0 : Int))) ” &&
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) data_values (0 : Int))) ” &&
  “ ((Znth (0 : Int) data_values (0 : Int)) < data_bound_pre) ” &&
  “ (heap_representation M_before key_values_2 data_values_2 pos_values data_bound_pre n) ”
  &&  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values_2)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values_2)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> ((Znth (0 : Int) data_values (0 : Int))))
  ** ((key_out_pre) # Int |-> ((Znth (0 : Int) key_values (0 : Int))))
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (data_bound_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values_2 data_bound_pre n)) ,
  TT && emp 
|--
  “ ((Znth (0 : Int) data_values (0 : Int)) < data_bound_pre) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) data_values (0 : Int))) ”
  &&  emp
)

noncomputable def pqdk_pop_entail_wit_2_split_goal_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (data_bound_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values_2 data_bound_pre n)) ,
  ((Znth (0 : Int) data_values (0 : Int)) < data_bound_pre)

noncomputable def pqdk_pop_entail_wit_2_split_goal_2 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (data_bound_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values_2 : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values_2 data_bound_pre n)) ,
  ((0 : Int) <= (Znth (0 : Int) data_values (0 : Int)))

noncomputable def pqdk_pop_entail_wit_3 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (n ≠ 1)) (PreH2 : (result_key = (Znth (0 : Int) key_values_2 (0 : Int)))) (PreH3 : (result_data = (Znth (0 : Int) data_values_2 (0 : Int)))) (PreH4 : (1 <= n)) (PreH5 : (n <= capacity)) (PreH6 : (capacity <= heap_capacity)) (PreH7 : ((0 : Int) <= result_data)) (PreH8 : (result_data < data_bound_pre)) (PreH9 : (heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (result_data) ((-1)) (pos_values_2)))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values_2)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values_2)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  EX key_values : (List Int), EX pos_values : (List Int), EX data_values : (List Int), EX popped : (Int × Int),
  “ (1 < n) ” &&
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ ((0 : Int) <= (n - 1)) ” &&
  “ ((n - 1) < n) ” &&
  “ ((0 : Int) <= (Znth (n - 1) data_values (0 : Int))) ” &&
  “ ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre) ” &&
  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped) ”
  &&  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (data_bound_pre : Int) (key_values_2 : (List Int)) (data_values_2 : (List Int)) (pos_values_2 : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (n ≠ 1)) (PreH2 : (result_key = (Znth (0 : Int) key_values_2 (0 : Int)))) (PreH3 : (result_data = (Znth (0 : Int) data_values_2 (0 : Int)))) (PreH4 : (1 <= n)) (PreH5 : (n <= capacity)) (PreH6 : (capacity <= heap_capacity)) (PreH7 : ((0 : Int) <= result_data)) (PreH8 : (result_data < data_bound_pre)) (PreH9 : (heap_representation M_before key_values_2 data_values_2 pos_values_2 data_bound_pre n)) ,
  TT && emp 
|--
  EX popped : (Int × Int),
  “ (1 < n) ” &&
  “ ((Znth (0 : Int) key_values_2 (0 : Int)) = (item_key (popped))) ” &&
  “ ((Znth (0 : Int) data_values_2 (0 : Int)) = (item_data (popped))) ” &&
  “ ((0 : Int) <= (n - 1)) ” &&
  “ ((n - 1) < n) ” &&
  “ ((0 : Int) <= (Znth (n - 1) data_values_2 (0 : Int))) ” &&
  “ ((Znth (n - 1) data_values_2 (0 : Int)) < data_bound_pre) ” &&
  “ (PopMarkedState M_before key_values_2 data_values_2 (replace_Znth ((Znth (0 : Int) data_values_2 (0 : Int))) ((-1)) (pos_values_2)) data_bound_pre n popped) ”
  &&  emp
)

noncomputable def pqdk_pop_entail_wit_4 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped_2 : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped_2)))) (PreH6 : (result_data = (item_data (popped_2)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped_2)) ,
  (intArray.full data_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) data_values (0 : Int))) (data_values)))
  ** (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** ((size_pre) # Int |-> ((n - 1)))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  EX popped : (Int × Int),
  “ (1 < n) ” &&
  “ ((0 : Int) < (n - 1)) ” &&
  “ ((n - 1) <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (partial_map_minimum M_before popped) ”
  &&  ((size_pre) # Int |-> ((n - 1)))
  ** (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1) (0 : Int))
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (popped_2 : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped_2)))) (PreH6 : (result_data = (item_data (popped_2)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped_2)) ,
  (intArray.full data_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) data_values (0 : Int))) (data_values)))
  ** (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
|--
  EX popped : (Int × Int),
  “ (1 < n) ” &&
  “ ((0 : Int) < (n - 1)) ” &&
  “ ((n - 1) <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (partial_map_minimum M_before popped) ”
  &&  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1) (0 : Int))
)

noncomputable def pqdk_pop_return_wit_1 : Prop :=
  (
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (n = 1)) (PreH2 : (result_key = (Znth (0 : Int) key_values (0 : Int)))) (PreH3 : (result_data = (Znth (0 : Int) data_values (0 : Int)))) (PreH4 : (1 <= n)) (PreH5 : (n <= capacity)) (PreH6 : (capacity <= heap_capacity)) (PreH7 : ((0 : Int) <= result_data)) (PreH8 : (result_data < data_bound_pre)) (PreH9 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (result_data) ((-1)) (pos_values)))
  ** ((size_pre) # Int |-> ((0 : Int)))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  EX data_out_v : Int, EX popped : (Int × Int), EX key_out_v : Int,
  “ (key_out_v = (item_key (popped))) ” &&
  “ (data_out_v = (item_data (popped))) ” &&
  “ (partial_map_minimum M_before popped) ”
  &&  ((key_out_pre) # Int |-> (key_out_v))
  ** ((data_out_pre) # Int |-> (data_out_v))
  ** ((size_pre) # Int |-> ((n - 1)))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1))
) \/
(
forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (data_bound_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (n = 1)) (PreH2 : (result_key = (Znth (0 : Int) key_values (0 : Int)))) (PreH3 : (result_data = (Znth (0 : Int) data_values (0 : Int)))) (PreH4 : (1 <= n)) (PreH5 : (n <= capacity)) (PreH6 : (capacity <= heap_capacity)) (PreH7 : ((0 : Int) <= result_data)) (PreH8 : (result_data < data_bound_pre)) (PreH9 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth (result_data) ((-1)) (pos_values)))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
|--
  EX popped : (Int × Int),
  “ (result_data = (item_data (popped))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ ((0 : Int) = (n - 1)) ” &&
  “ (partial_map_minimum M_before popped) ”
  &&  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1))
)

noncomputable def pqdk_pop_return_wit_2 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped_2 : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : ((0 : Int) < (n - 1))) (PreH3 : ((n - 1) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped_2)))) (PreH6 : (result_data = (item_data (popped_2)))) (PreH7 : (partial_map_minimum M_before popped_2)) ,
  (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped_2)))) (n - 1))
  ** ((size_pre) # Int |-> ((n - 1)))
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  EX data_out_v : Int, EX popped : (Int × Int), EX key_out_v : Int,
  “ (key_out_v = (item_key (popped))) ” &&
  “ (data_out_v = (item_data (popped))) ” &&
  “ (partial_map_minimum M_before popped) ”
  &&  ((key_out_pre) # Int |-> (key_out_v))
  ** ((data_out_pre) # Int |-> (data_out_v))
  ** ((size_pre) # Int |-> ((n - 1)))
  ** (store_heap key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1))

noncomputable def pqdk_pop_partial_solve_wit_1 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (((key_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) key_values (0 : Int))))
  ** (intArray.missing_i key_pre (0 : Int) (0 : Int) n key_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pqdk_pop_partial_solve_wit_2 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= capacity)) (PreH3 : (capacity <= heap_capacity)) (PreH4 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  (intArray.full key_pre n key_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)
|--
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (((data_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) data_values (0 : Int))))
  ** (intArray.missing_i data_pre (0 : Int) (0 : Int) n data_values)
  ** (intArray.full key_pre n key_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |->_)
  ** ((key_out_pre) # Int |->_)

noncomputable def pqdk_pop_partial_solve_wit_3 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (result_key = (Znth (0 : Int) key_values (0 : Int)))) (PreH2 : (result_data = (Znth (0 : Int) data_values (0 : Int)))) (PreH3 : (1 <= n)) (PreH4 : (n <= capacity)) (PreH5 : (capacity <= heap_capacity)) (PreH6 : ((0 : Int) <= result_data)) (PreH7 : (result_data < data_bound_pre)) (PreH8 : (heap_representation M_before key_values data_values pos_values data_bound_pre n)) ,
  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (result_key = (Znth (0 : Int) key_values (0 : Int))) ” &&
  “ (result_data = (Znth (0 : Int) data_values (0 : Int))) ” &&
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ ((0 : Int) <= result_data) ” &&
  “ (result_data < data_bound_pre) ” &&
  “ (heap_representation M_before key_values data_values pos_values data_bound_pre n) ”
  &&  (((pos_pre + (result_data * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i pos_pre result_data (0 : Int) data_bound_pre pos_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))

noncomputable def pqdk_pop_partial_solve_wit_4 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.full data_pre n data_values)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 < n) ” &&
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ ((0 : Int) <= (n - 1)) ” &&
  “ ((n - 1) < n) ” &&
  “ ((0 : Int) <= (Znth (n - 1) data_values (0 : Int))) ” &&
  “ ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre) ” &&
  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped) ”
  &&  (((data_pre + ((n - 1) * sizeof(INT)))) # Int |-> ((Znth (n - 1) data_values (0 : Int))))
  ** (intArray.missing_i data_pre (n - 1) (0 : Int) n data_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))

noncomputable def pqdk_pop_partial_solve_wit_5 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full data_pre n data_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** (intArray.full pos_pre data_bound_pre pos_values)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 < n) ” &&
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ ((0 : Int) <= (n - 1)) ” &&
  “ ((n - 1) < n) ” &&
  “ ((0 : Int) <= (Znth (n - 1) data_values (0 : Int))) ” &&
  “ ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre) ” &&
  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped) ”
  &&  (((pos_pre + ((Znth (n - 1) data_values (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i pos_pre (Znth (n - 1) data_values (0 : Int)) (0 : Int) data_bound_pre pos_values)
  ** (intArray.full data_pre n data_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))

noncomputable def pqdk_pop_partial_solve_wit_6 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.full key_pre n key_values)
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 < n) ” &&
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ ((0 : Int) <= (n - 1)) ” &&
  “ ((n - 1) < n) ” &&
  “ ((0 : Int) <= (Znth (n - 1) data_values (0 : Int))) ” &&
  “ ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre) ” &&
  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped) ”
  &&  (((key_pre + ((n - 1) * sizeof(INT)))) # Int |-> ((Znth (n - 1) key_values (0 : Int))))
  ** (intArray.missing_i key_pre (n - 1) (0 : Int) n key_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))

noncomputable def pqdk_pop_partial_solve_wit_7 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full key_pre n key_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 < n) ” &&
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ ((0 : Int) <= (n - 1)) ” &&
  “ ((n - 1) < n) ” &&
  “ ((0 : Int) <= (Znth (n - 1) data_values (0 : Int))) ” &&
  “ ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre) ” &&
  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped) ”
  &&  (((key_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i key_pre (0 : Int) (0 : Int) n key_values)
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))

noncomputable def pqdk_pop_partial_solve_wit_8 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** (intArray.full data_pre n data_values)
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 < n) ” &&
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ ((0 : Int) <= (n - 1)) ” &&
  “ ((n - 1) < n) ” &&
  “ ((0 : Int) <= (Znth (n - 1) data_values (0 : Int))) ” &&
  “ ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre) ” &&
  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped) ”
  &&  (((data_pre + ((n - 1) * sizeof(INT)))) # Int |-> ((Znth (n - 1) data_values (0 : Int))))
  ** (intArray.missing_i data_pre (n - 1) (0 : Int) n data_values)
  ** (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))

noncomputable def pqdk_pop_partial_solve_wit_9 : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (key_values : (List Int)) (data_values : (List Int)) (pos_values : (List Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : (1 <= n)) (PreH3 : (n <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : ((0 : Int) <= (n - 1))) (PreH8 : ((n - 1) < n)) (PreH9 : ((0 : Int) <= (Znth (n - 1) data_values (0 : Int)))) (PreH10 : ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre)) (PreH11 : (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped)) ,
  (intArray.full data_pre n data_values)
  ** (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ (1 < n) ” &&
  “ (1 <= n) ” &&
  “ (n <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ ((0 : Int) <= (n - 1)) ” &&
  “ ((n - 1) < n) ” &&
  “ ((0 : Int) <= (Znth (n - 1) data_values (0 : Int))) ” &&
  “ ((Znth (n - 1) data_values (0 : Int)) < data_bound_pre) ” &&
  “ (PopMarkedState M_before key_values data_values pos_values data_bound_pre n popped) ”
  &&  (((data_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i data_pre (0 : Int) (0 : Int) n data_values)
  ** (intArray.full key_pre n (replace_Znth ((0 : Int)) ((Znth (n - 1) key_values (0 : Int))) (key_values)))
  ** (intArray.full pos_pre data_bound_pre (replace_Znth ((Znth (n - 1) data_values (0 : Int))) ((0 : Int)) (pos_values)))
  ** ((size_pre) # Int |-> (n))
  ** (intArray.undef_seg key_pre n capacity)
  ** (intArray.undef_seg data_pre n capacity)
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))

noncomputable def pqdk_pop_partial_solve_wit_10_pure : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : ((0 : Int) < (n - 1))) (PreH3 : ((n - 1) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped)) ,
  ((( &( "key" ) )) # Ptr |-> (key_pre))
  ** ((( &( "data" ) )) # Ptr |-> (data_pre))
  ** ((( &( "pos" ) )) # Ptr |-> (pos_pre))
  ** ((( &( "size" ) )) # Ptr |-> (size_pre))
  ** ((( &( "data_bound" ) )) # Int |-> (data_bound_pre))
  ** ((( &( "data_out" ) )) # Ptr |-> (data_out_pre))
  ** ((( &( "key_out" ) )) # Ptr |-> (key_out_pre))
  ** ((( &( "n0" ) )) # Int |-> (n))
  ** ((( &( "result_key" ) )) # Int |-> (result_key))
  ** ((( &( "result_data" ) )) # Int |-> (result_data))
  ** ((size_pre) # Int |-> ((n - 1)))
  ** (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1) (0 : Int))
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < (n - 1)) ” &&
  “ ((n - 1) <= capacity) ” &&
  “ (capacity <= heap_capacity) ”

noncomputable def pqdk_pop_partial_solve_wit_10_aux : Prop :=
  forall (capacity : Int) (n : Int) (M_before : partial_map) (key_pre : Int) (data_pre : Int) (pos_pre : Int) (size_pre : Int) (data_bound_pre : Int) (data_out_pre : Int) (key_out_pre : Int) (popped : (Int × Int)) (result_key : Int) (result_data : Int) (PreH1 : (1 < n)) (PreH2 : ((0 : Int) < (n - 1))) (PreH3 : ((n - 1) <= capacity)) (PreH4 : (capacity <= heap_capacity)) (PreH5 : (result_key = (item_key (popped)))) (PreH6 : (result_data = (item_data (popped)))) (PreH7 : (partial_map_minimum M_before popped)) ,
  ((size_pre) # Int |-> ((n - 1)))
  ** (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1) (0 : Int))
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < (n - 1)) ” &&
  “ ((n - 1) <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (1 < n) ” &&
  “ ((0 : Int) < (n - 1)) ” &&
  “ ((n - 1) <= capacity) ” &&
  “ (capacity <= heap_capacity) ” &&
  “ (result_key = (item_key (popped))) ” &&
  “ (result_data = (item_data (popped))) ” &&
  “ (partial_map_minimum M_before popped) ”
  &&  (store_sift_down key_pre data_pre pos_pre data_bound_pre capacity (partial_map_remove (M_before) ((item_data (popped)))) (n - 1) (0 : Int))
  ** ((size_pre) # Int |-> ((n - 1)))
  ** ((data_out_pre) # Int |-> (result_data))
  ** ((key_out_pre) # Int |-> (result_key))

noncomputable def pqdk_pop_partial_solve_wit_10 : Prop := pqdk_pop_partial_solve_wit_10_pure -> pqdk_pop_partial_solve_wit_10_aux


structure VC_Correct : Type where
  proof_of_pqdk_sift_up_safety_wit_1 : pqdk_sift_up_safety_wit_1
  proof_of_pqdk_sift_up_safety_wit_2 : pqdk_sift_up_safety_wit_2
  proof_of_pqdk_sift_up_safety_wit_3 : pqdk_sift_up_safety_wit_3
  proof_of_pqdk_sift_up_safety_wit_4 : pqdk_sift_up_safety_wit_4
  proof_of_pqdk_sift_up_safety_wit_5 : pqdk_sift_up_safety_wit_5
  proof_of_pqdk_sift_up_partial_solve_wit_1 : pqdk_sift_up_partial_solve_wit_1
  proof_of_pqdk_sift_up_partial_solve_wit_2 : pqdk_sift_up_partial_solve_wit_2
  proof_of_pqdk_sift_up_partial_solve_wit_3 : pqdk_sift_up_partial_solve_wit_3
  proof_of_pqdk_sift_up_partial_solve_wit_4 : pqdk_sift_up_partial_solve_wit_4
  proof_of_pqdk_sift_up_partial_solve_wit_5 : pqdk_sift_up_partial_solve_wit_5
  proof_of_pqdk_sift_up_partial_solve_wit_6 : pqdk_sift_up_partial_solve_wit_6
  proof_of_pqdk_sift_up_partial_solve_wit_7 : pqdk_sift_up_partial_solve_wit_7
  proof_of_pqdk_sift_up_partial_solve_wit_8 : pqdk_sift_up_partial_solve_wit_8
  proof_of_pqdk_sift_up_partial_solve_wit_9 : pqdk_sift_up_partial_solve_wit_9
  proof_of_pqdk_sift_up_partial_solve_wit_10 : pqdk_sift_up_partial_solve_wit_10
  proof_of_pqdk_sift_up_partial_solve_wit_11 : pqdk_sift_up_partial_solve_wit_11
  proof_of_pqdk_sift_up_partial_solve_wit_12 : pqdk_sift_up_partial_solve_wit_12
  proof_of_pqdk_sift_up_partial_solve_wit_13 : pqdk_sift_up_partial_solve_wit_13
  proof_of_pqdk_sift_up_partial_solve_wit_14 : pqdk_sift_up_partial_solve_wit_14
  proof_of_pqdk_sift_down_safety_wit_3 : pqdk_sift_down_safety_wit_3
  proof_of_pqdk_sift_down_safety_wit_4 : pqdk_sift_down_safety_wit_4
  proof_of_pqdk_sift_down_safety_wit_5 : pqdk_sift_down_safety_wit_5
  proof_of_pqdk_sift_down_safety_wit_6 : pqdk_sift_down_safety_wit_6
  proof_of_pqdk_sift_down_safety_wit_7 : pqdk_sift_down_safety_wit_7
  proof_of_pqdk_sift_down_safety_wit_8 : pqdk_sift_down_safety_wit_8
  proof_of_pqdk_sift_down_safety_wit_9 : pqdk_sift_down_safety_wit_9
  proof_of_pqdk_sift_down_safety_wit_10 : pqdk_sift_down_safety_wit_10
  proof_of_pqdk_sift_down_entail_wit_2 : pqdk_sift_down_entail_wit_2
  proof_of_pqdk_sift_down_partial_solve_wit_1 : pqdk_sift_down_partial_solve_wit_1
  proof_of_pqdk_sift_down_partial_solve_wit_2 : pqdk_sift_down_partial_solve_wit_2
  proof_of_pqdk_sift_down_partial_solve_wit_3 : pqdk_sift_down_partial_solve_wit_3
  proof_of_pqdk_sift_down_partial_solve_wit_4 : pqdk_sift_down_partial_solve_wit_4
  proof_of_pqdk_sift_down_partial_solve_wit_5 : pqdk_sift_down_partial_solve_wit_5
  proof_of_pqdk_sift_down_partial_solve_wit_6 : pqdk_sift_down_partial_solve_wit_6
  proof_of_pqdk_sift_down_partial_solve_wit_7 : pqdk_sift_down_partial_solve_wit_7
  proof_of_pqdk_sift_down_partial_solve_wit_8 : pqdk_sift_down_partial_solve_wit_8
  proof_of_pqdk_sift_down_partial_solve_wit_9 : pqdk_sift_down_partial_solve_wit_9
  proof_of_pqdk_sift_down_partial_solve_wit_10 : pqdk_sift_down_partial_solve_wit_10
  proof_of_pqdk_sift_down_partial_solve_wit_11 : pqdk_sift_down_partial_solve_wit_11
  proof_of_pqdk_sift_down_partial_solve_wit_12 : pqdk_sift_down_partial_solve_wit_12
  proof_of_pqdk_sift_down_partial_solve_wit_13 : pqdk_sift_down_partial_solve_wit_13
  proof_of_pqdk_sift_down_partial_solve_wit_14 : pqdk_sift_down_partial_solve_wit_14
  proof_of_pqdk_sift_down_partial_solve_wit_15 : pqdk_sift_down_partial_solve_wit_15
  proof_of_pqdk_sift_down_partial_solve_wit_16 : pqdk_sift_down_partial_solve_wit_16
  proof_of_pqdk_push_safety_wit_2 : pqdk_push_safety_wit_2
  proof_of_pqdk_push_safety_wit_3 : pqdk_push_safety_wit_3
  proof_of_pqdk_push_safety_wit_4 : pqdk_push_safety_wit_4
  proof_of_pqdk_push_return_wit_1 : pqdk_push_return_wit_1
  proof_of_pqdk_push_partial_solve_wit_1 : pqdk_push_partial_solve_wit_1
  proof_of_pqdk_push_partial_solve_wit_2 : pqdk_push_partial_solve_wit_2
  proof_of_pqdk_push_partial_solve_wit_3 : pqdk_push_partial_solve_wit_3
  proof_of_pqdk_push_partial_solve_wit_4_pure : pqdk_push_partial_solve_wit_4_pure
  proof_of_pqdk_push_partial_solve_wit_4 : pqdk_push_partial_solve_wit_4
  proof_of_pqdk_decrease_key_return_wit_1 : pqdk_decrease_key_return_wit_1
  proof_of_pqdk_decrease_key_partial_solve_wit_1 : pqdk_decrease_key_partial_solve_wit_1
  proof_of_pqdk_decrease_key_partial_solve_wit_2 : pqdk_decrease_key_partial_solve_wit_2
  proof_of_pqdk_decrease_key_partial_solve_wit_3_pure : pqdk_decrease_key_partial_solve_wit_3_pure
  proof_of_pqdk_decrease_key_partial_solve_wit_3 : pqdk_decrease_key_partial_solve_wit_3
  proof_of_pqdk_update_or_push_safety_wit_1 : pqdk_update_or_push_safety_wit_1
  proof_of_pqdk_update_or_push_return_wit_1 : pqdk_update_or_push_return_wit_1
  proof_of_pqdk_update_or_push_partial_solve_wit_1 : pqdk_update_or_push_partial_solve_wit_1
  proof_of_pqdk_update_or_push_partial_solve_wit_2_pure : pqdk_update_or_push_partial_solve_wit_2_pure
  proof_of_pqdk_update_or_push_partial_solve_wit_2 : pqdk_update_or_push_partial_solve_wit_2
  proof_of_pqdk_update_or_push_partial_solve_wit_3_pure : pqdk_update_or_push_partial_solve_wit_3_pure
  proof_of_pqdk_update_or_push_partial_solve_wit_3 : pqdk_update_or_push_partial_solve_wit_3
  proof_of_pqdk_pop_safety_wit_1 : pqdk_pop_safety_wit_1
  proof_of_pqdk_pop_safety_wit_2 : pqdk_pop_safety_wit_2
  proof_of_pqdk_pop_safety_wit_3 : pqdk_pop_safety_wit_3
  proof_of_pqdk_pop_safety_wit_4 : pqdk_pop_safety_wit_4
  proof_of_pqdk_pop_safety_wit_5 : pqdk_pop_safety_wit_5
  proof_of_pqdk_pop_safety_wit_6 : pqdk_pop_safety_wit_6
  proof_of_pqdk_pop_safety_wit_7 : pqdk_pop_safety_wit_7
  proof_of_pqdk_pop_safety_wit_8 : pqdk_pop_safety_wit_8
  proof_of_pqdk_pop_safety_wit_9 : pqdk_pop_safety_wit_9
  proof_of_pqdk_pop_safety_wit_10 : pqdk_pop_safety_wit_10
  proof_of_pqdk_pop_safety_wit_11 : pqdk_pop_safety_wit_11
  proof_of_pqdk_pop_safety_wit_12 : pqdk_pop_safety_wit_12
  proof_of_pqdk_pop_safety_wit_13 : pqdk_pop_safety_wit_13
  proof_of_pqdk_pop_safety_wit_14 : pqdk_pop_safety_wit_14
  proof_of_pqdk_pop_safety_wit_15 : pqdk_pop_safety_wit_15
  proof_of_pqdk_pop_safety_wit_16 : pqdk_pop_safety_wit_16
  proof_of_pqdk_pop_safety_wit_17 : pqdk_pop_safety_wit_17
  proof_of_pqdk_pop_safety_wit_18 : pqdk_pop_safety_wit_18
  proof_of_pqdk_pop_safety_wit_19 : pqdk_pop_safety_wit_19
  proof_of_pqdk_pop_safety_wit_20 : pqdk_pop_safety_wit_20
  proof_of_pqdk_pop_return_wit_2 : pqdk_pop_return_wit_2
  proof_of_pqdk_pop_partial_solve_wit_1 : pqdk_pop_partial_solve_wit_1
  proof_of_pqdk_pop_partial_solve_wit_2 : pqdk_pop_partial_solve_wit_2
  proof_of_pqdk_pop_partial_solve_wit_3 : pqdk_pop_partial_solve_wit_3
  proof_of_pqdk_pop_partial_solve_wit_4 : pqdk_pop_partial_solve_wit_4
  proof_of_pqdk_pop_partial_solve_wit_5 : pqdk_pop_partial_solve_wit_5
  proof_of_pqdk_pop_partial_solve_wit_6 : pqdk_pop_partial_solve_wit_6
  proof_of_pqdk_pop_partial_solve_wit_7 : pqdk_pop_partial_solve_wit_7
  proof_of_pqdk_pop_partial_solve_wit_8 : pqdk_pop_partial_solve_wit_8
  proof_of_pqdk_pop_partial_solve_wit_9 : pqdk_pop_partial_solve_wit_9
  proof_of_pqdk_pop_partial_solve_wit_10_pure : pqdk_pop_partial_solve_wit_10_pure
  proof_of_pqdk_pop_partial_solve_wit_10 : pqdk_pop_partial_solve_wit_10
  proof_of_pqdk_sift_up_entail_wit_1 : pqdk_sift_up_entail_wit_1
  proof_of_pqdk_sift_up_entail_wit_2 : pqdk_sift_up_entail_wit_2
  proof_of_pqdk_sift_up_entail_wit_3 : pqdk_sift_up_entail_wit_3
  proof_of_pqdk_sift_up_entail_wit_4 : pqdk_sift_up_entail_wit_4
  proof_of_pqdk_sift_up_return_wit_1 : pqdk_sift_up_return_wit_1
  proof_of_pqdk_sift_up_return_wit_2 : pqdk_sift_up_return_wit_2
  proof_of_pqdk_sift_down_safety_wit_1 : pqdk_sift_down_safety_wit_1
  proof_of_pqdk_sift_down_safety_wit_2 : pqdk_sift_down_safety_wit_2
  proof_of_pqdk_sift_down_entail_wit_1 : pqdk_sift_down_entail_wit_1
  proof_of_pqdk_sift_down_entail_wit_3_1 : pqdk_sift_down_entail_wit_3_1
  proof_of_pqdk_sift_down_entail_wit_3_2 : pqdk_sift_down_entail_wit_3_2
  proof_of_pqdk_sift_down_entail_wit_3_3 : pqdk_sift_down_entail_wit_3_3
  proof_of_pqdk_sift_down_entail_wit_4 : pqdk_sift_down_entail_wit_4
  proof_of_pqdk_sift_down_entail_wit_5 : pqdk_sift_down_entail_wit_5
  proof_of_pqdk_sift_down_return_wit_1 : pqdk_sift_down_return_wit_1
  proof_of_pqdk_sift_down_return_wit_2 : pqdk_sift_down_return_wit_2
  proof_of_pqdk_push_safety_wit_1 : pqdk_push_safety_wit_1
  proof_of_pqdk_push_entail_wit_1 : pqdk_push_entail_wit_1
  proof_of_pqdk_push_entail_wit_2 : pqdk_push_entail_wit_2
  proof_of_pqdk_decrease_key_entail_wit_1 : pqdk_decrease_key_entail_wit_1
  proof_of_pqdk_decrease_key_entail_wit_2 : pqdk_decrease_key_entail_wit_2
  proof_of_pqdk_decrease_key_entail_wit_3 : pqdk_decrease_key_entail_wit_3
  proof_of_pqdk_update_or_push_entail_wit_1 : pqdk_update_or_push_entail_wit_1
  proof_of_pqdk_update_or_push_entail_wit_2 : pqdk_update_or_push_entail_wit_2
  proof_of_pqdk_update_or_push_entail_wit_3 : pqdk_update_or_push_entail_wit_3
  proof_of_pqdk_update_or_push_entail_wit_4_1 : pqdk_update_or_push_entail_wit_4_1
  proof_of_pqdk_update_or_push_entail_wit_4_2 : pqdk_update_or_push_entail_wit_4_2
  proof_of_pqdk_pop_entail_wit_1 : pqdk_pop_entail_wit_1
  proof_of_pqdk_pop_entail_wit_2 : pqdk_pop_entail_wit_2
  proof_of_pqdk_pop_entail_wit_3 : pqdk_pop_entail_wit_3
  proof_of_pqdk_pop_entail_wit_4 : pqdk_pop_entail_wit_4
  proof_of_pqdk_pop_return_wit_1 : pqdk_pop_return_wit_1

end SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_goal
