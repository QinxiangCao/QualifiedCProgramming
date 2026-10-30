import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_lib
open SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance container_with_most_water_nlogn_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def mergeHeightIndexRunsNLogN_safety_wit_1 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i (0 : Int))) (dest_i)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** ((( &( "sourceHeight" ) )) # Ptr |-> (sourceHeight_pre))
  ** ((( &( "sourceIndex" ) )) # Ptr |-> (sourceIndex_pre))
  ** ((( &( "destinationHeight" ) )) # Ptr |-> (destinationHeight_pre))
  ** ((( &( "destinationIndex" ) )) # Ptr |-> (destinationIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "middle" ) )) # Int |-> (middle_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "output" ) )) # Int |-> (output))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def mergeHeightIndexRunsNLogN_safety_wit_2 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i (0 : Int))) (dest_i)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** ((( &( "sourceHeight" ) )) # Ptr |-> (sourceHeight_pre))
  ** ((( &( "sourceIndex" ) )) # Ptr |-> (sourceIndex_pre))
  ** ((( &( "destinationHeight" ) )) # Ptr |-> (destinationHeight_pre))
  ** ((( &( "destinationIndex" ) )) # Ptr |-> (destinationIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "middle" ) )) # Int |-> (middle_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "output" ) )) # Int |-> (output))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def mergeHeightIndexRunsNLogN_safety_wit_3 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i (0 : Int))) (dest_i)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** ((( &( "sourceHeight" ) )) # Ptr |-> (sourceHeight_pre))
  ** ((( &( "sourceIndex" ) )) # Ptr |-> (sourceIndex_pre))
  ** ((( &( "destinationHeight" ) )) # Ptr |-> (destinationHeight_pre))
  ** ((( &( "destinationIndex" ) )) # Ptr |-> (destinationIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "middle" ) )) # Int |-> (middle_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "i" ) )) # Int |-> ((i + 1)))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "output" ) )) # Int |-> (output))
|--
  “ ((output + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (output + 1)) ”

noncomputable def mergeHeightIndexRunsNLogN_safety_wit_4 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i (0 : Int))) (dest_i)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** ((( &( "sourceHeight" ) )) # Ptr |-> (sourceHeight_pre))
  ** ((( &( "sourceIndex" ) )) # Ptr |-> (sourceIndex_pre))
  ** ((( &( "destinationHeight" ) )) # Ptr |-> (destinationHeight_pre))
  ** ((( &( "destinationIndex" ) )) # Ptr |-> (destinationIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "middle" ) )) # Int |-> (middle_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> ((j + 1)))
  ** ((( &( "output" ) )) # Int |-> (output))
|--
  “ ((output + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (output + 1)) ”

noncomputable def mergeHeightIndexRunsNLogN_safety_wit_5 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  ((( &( "sourceHeight" ) )) # Ptr |-> (sourceHeight_pre))
  ** ((( &( "sourceIndex" ) )) # Ptr |-> (sourceIndex_pre))
  ** ((( &( "destinationHeight" ) )) # Ptr |-> (destinationHeight_pre))
  ** ((( &( "destinationIndex" ) )) # Ptr |-> (destinationIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "middle" ) )) # Int |-> (middle_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "output" ) )) # Int |-> (output))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ False ”

noncomputable def mergeHeightIndexRunsNLogN_safety_wit_6 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (i : Int) (j : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i (0 : Int))) (dest_i)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** ((( &( "sourceHeight" ) )) # Ptr |-> (sourceHeight_pre))
  ** ((( &( "sourceIndex" ) )) # Ptr |-> (sourceIndex_pre))
  ** ((( &( "destinationHeight" ) )) # Ptr |-> (destinationHeight_pre))
  ** ((( &( "destinationIndex" ) )) # Ptr |-> (destinationIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "middle" ) )) # Int |-> (middle_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "output" ) )) # Int |-> (output))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def mergeHeightIndexRunsNLogN_safety_wit_7 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (i : Int) (j : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i (0 : Int))) (dest_i)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** ((( &( "sourceHeight" ) )) # Ptr |-> (sourceHeight_pre))
  ** ((( &( "sourceIndex" ) )) # Ptr |-> (sourceIndex_pre))
  ** ((( &( "destinationHeight" ) )) # Ptr |-> (destinationHeight_pre))
  ** ((( &( "destinationIndex" ) )) # Ptr |-> (destinationIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "middle" ) )) # Int |-> (middle_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> ((i + 1)))
  ** ((( &( "output" ) )) # Int |-> (output))
|--
  “ ((output + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (output + 1)) ”

noncomputable def mergeHeightIndexRunsNLogN_safety_wit_8 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i (0 : Int))) (dest_i)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** ((( &( "sourceHeight" ) )) # Ptr |-> (sourceHeight_pre))
  ** ((( &( "sourceIndex" ) )) # Ptr |-> (sourceIndex_pre))
  ** ((( &( "destinationHeight" ) )) # Ptr |-> (destinationHeight_pre))
  ** ((( &( "destinationIndex" ) )) # Ptr |-> (destinationIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "middle" ) )) # Int |-> (middle_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "output" ) )) # Int |-> (output))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def mergeHeightIndexRunsNLogN_safety_wit_9 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i (0 : Int))) (dest_i)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** ((( &( "sourceHeight" ) )) # Ptr |-> (sourceHeight_pre))
  ** ((( &( "sourceIndex" ) )) # Ptr |-> (sourceIndex_pre))
  ** ((( &( "destinationHeight" ) )) # Ptr |-> (destinationHeight_pre))
  ** ((( &( "destinationIndex" ) )) # Ptr |-> (destinationIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "middle" ) )) # Int |-> (middle_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> ((j + 1)))
  ** ((( &( "output" ) )) # Int |-> (output))
|--
  “ ((output + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (output + 1)) ”

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_1 : Prop :=
  (
forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (PreH1 : ((Zlength (source_h)) = count_pre)) (PreH2 : ((Zlength (source_i)) = count_pre)) (PreH3 : ((Zlength (dest0_h)) = count_pre)) (PreH4 : ((Zlength (dest0_i)) = count_pre)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre <= middle_pre)) (PreH7 : (middle_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (HeightIndexRangeDescendingNLogN source_h left_pre middle_pre)) (PreH10 : (HeightIndexRangeDescendingNLogN source_h middle_pre right_pre)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest0_h)
  ** (intArray.full destinationIndex_pre count_pre dest0_i)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= left_pre) ” &&
  “ (left_pre <= middle_pre) ” &&
  “ (middle_pre <= middle_pre) ” &&
  “ (middle_pre <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (left_pre = ((left_pre + (left_pre - left_pre)) + (middle_pre - middle_pre))) ” &&
  “ (left_pre <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre left_pre middle_pre left_pre) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
) \/
(
forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (PreH1 : ((Zlength (source_h)) = count_pre)) (PreH2 : ((Zlength (source_i)) = count_pre)) (PreH3 : ((Zlength (dest0_h)) = count_pre)) (PreH4 : ((Zlength (dest0_i)) = count_pre)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre <= middle_pre)) (PreH7 : (middle_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (HeightIndexRangeDescendingNLogN source_h left_pre middle_pre)) (PreH10 : (HeightIndexRangeDescendingNLogN source_h middle_pre right_pre)) ,
  TT && emp 
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest0_h dest0_i left_pre middle_pre right_pre left_pre middle_pre left_pre) ”
  &&  emp
)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (PreH1 : ((Zlength (source_h)) = count_pre)) (PreH2 : ((Zlength (source_i)) = count_pre)) (PreH3 : ((Zlength (dest0_h)) = count_pre)) (PreH4 : ((Zlength (dest0_i)) = count_pre)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre <= middle_pre)) (PreH7 : (middle_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (HeightIndexRangeDescendingNLogN source_h left_pre middle_pre)) (PreH10 : (HeightIndexRangeDescendingNLogN source_h middle_pre right_pre)) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest0_h dest0_i left_pre middle_pre right_pre left_pre middle_pre left_pre)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_2_1 : Prop :=
  (
forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i (0 : Int))) (dest_i_2)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h_2)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= (i + 1)) ” &&
  “ ((i + 1) <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ ((output + 1) = ((left_pre + ((i + 1) - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= (output + 1)) ” &&
  “ ((output + 1) <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre (i + 1) j (output + 1)) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
) \/
(
forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  TT && emp 
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre (i + 1) j (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1)) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_i (0 : Int))) (dest_i_2)))) = count_pre) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_h (0 : Int))) (dest_h_2)))) = count_pre) ”
  &&  emp
)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre (i + 1) j (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1))

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_i (0 : Int))) (dest_i_2)))) = count_pre)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth i source_h (0 : Int))) (dest_h_2)))) = count_pre)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_2_2 : Prop :=
  (
forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i (0 : Int))) (dest_i_2)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h_2)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= (j + 1)) ” &&
  “ ((j + 1) <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ ((output + 1) = ((left_pre + (i - left_pre)) + ((j + 1) - middle_pre))) ” &&
  “ (left_pre <= (output + 1)) ” &&
  “ ((output + 1) <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i (j + 1) (output + 1)) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
) \/
(
forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  TT && emp 
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre i (j + 1) (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1)) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)))) = count_pre) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)))) = count_pre) ”
  &&  emp
)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre i (j + 1) (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1))

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)))) = count_pre)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)))) = count_pre)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_3_1 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (i >= middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : ((0 : Int) <= left_pre)) (PreH9 : (left_pre <= i)) (PreH10 : (i <= middle_pre)) (PreH11 : (middle_pre <= j)) (PreH12 : (j <= right_pre)) (PreH13 : (right_pre <= count_pre)) (PreH14 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH15 : (left_pre <= output)) (PreH16 : (output <= right_pre)) (PreH17 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h_2)
  ** (intArray.full destinationIndex_pre count_pre dest_i_2)
|--
  (EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (i = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i))
  ||
  (EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (j = right_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i))

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_3_2 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j >= right_pre)) (PreH2 : (i < middle_pre)) (PreH3 : ((Zlength (source_h)) = count_pre)) (PreH4 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH5 : ((Zlength (dest0_h)) = count_pre)) (PreH6 : ((Zlength (dest0_i)) = count_pre)) (PreH7 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH8 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h_2)
  ** (intArray.full destinationIndex_pre count_pre dest_i_2)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (j = right_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_4 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (i : Int) (j : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i (0 : Int))) (dest_i_2)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h_2)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
|--
  (EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((i + 1) = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= (i + 1)) ” &&
  “ ((i + 1) <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ ((output + 1) = ((left_pre + ((i + 1) - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= (output + 1)) ” &&
  “ ((output + 1) <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre (i + 1) j (output + 1)) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i))
  ||
  (EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (j = right_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= (i + 1)) ” &&
  “ ((i + 1) <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ ((output + 1) = ((left_pre + ((i + 1) - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= (output + 1)) ” &&
  “ ((output + 1) <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre (i + 1) j (output + 1)) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i))

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_5_1 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (i >= middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h_2)
  ** (intArray.full destinationIndex_pre count_pre dest_i_2)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (i = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_5_2 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (i : Int) (j : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (i >= middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h_2)
  ** (intArray.full destinationIndex_pre count_pre dest_i_2)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (i = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_6 : Prop :=
  (
forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i (0 : Int))) (dest_i_2)))
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h_2)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
|--
  EX dest_i : (List Int), EX dest_h : (List Int),
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (i = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= (j + 1)) ” &&
  “ ((j + 1) <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ ((output + 1) = ((left_pre + (i - left_pre)) + ((j + 1) - middle_pre))) ” &&
  “ (left_pre <= (output + 1)) ” &&
  “ ((output + 1) <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i (j + 1) (output + 1)) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
) \/
(
forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  TT && emp 
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre middle_pre (j + 1) (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1)) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)))) = count_pre) ” &&
  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)))) = count_pre) ”
  &&  emp
)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)) left_pre middle_pre right_pre middle_pre (j + 1) (((left_pre + (i - left_pre)) + (j - middle_pre)) + 1))

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_i (0 : Int))) (dest_i_2)))) = count_pre)

noncomputable def mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre)) + (j - middle_pre))) ((Znth j source_h (0 : Int))) (dest_h_2)))) = count_pre)

noncomputable def mergeHeightIndexRunsNLogN_return_wit_1 : Prop :=
  (
forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j >= right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h_2)
  ** (intArray.full destinationIndex_pre count_pre dest_i_2)
|--
  EX dest_h : (List Int), EX dest_i : (List Int),
  “ (HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre) ”
  &&  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
) \/
(
forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j >= right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  TT && emp 
|--
  “ (HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre) ”
  &&  emp
)

noncomputable def mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i_2 : (List Int)) (dest_h_2 : (List Int)) (PreH1 : (j >= right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output)) ,
  (HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_1 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : (i < middle_pre)) (PreH3 : ((Zlength (source_h)) = count_pre)) (PreH4 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH5 : ((Zlength (dest0_h)) = count_pre)) (PreH6 : ((Zlength (dest0_i)) = count_pre)) (PreH7 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH8 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ (j < right_pre) ” &&
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((sourceHeight_pre + (i * sizeof(INT)))) # Int |-> ((Znth i source_h (0 : Int))))
  ** (intArray.missing_i sourceHeight_pre i (0 : Int) count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_2 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : (i < middle_pre)) (PreH3 : ((Zlength (source_h)) = count_pre)) (PreH4 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH5 : ((Zlength (dest0_h)) = count_pre)) (PreH6 : ((Zlength (dest0_i)) = count_pre)) (PreH7 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH8 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ (j < right_pre) ” &&
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((sourceHeight_pre + (j * sizeof(INT)))) # Int |-> ((Znth j source_h (0 : Int))))
  ** (intArray.missing_i sourceHeight_pre j (0 : Int) count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_3 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int))) ” &&
  “ (j < right_pre) ” &&
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((sourceHeight_pre + (i * sizeof(INT)))) # Int |-> ((Znth i source_h (0 : Int))))
  ** (intArray.missing_i sourceHeight_pre i (0 : Int) count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_4 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int))) ” &&
  “ (j < right_pre) ” &&
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((destinationHeight_pre + (output * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i destinationHeight_pre output (0 : Int) count_pre dest_h)
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_5 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int))) ” &&
  “ (j < right_pre) ” &&
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((sourceIndex_pre + (i * sizeof(INT)))) # Int |-> ((Znth i source_i (0 : Int))))
  ** (intArray.missing_i sourceIndex_pre i (0 : Int) count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_6 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ ((Znth i source_h (0 : Int)) >= (Znth j source_h (0 : Int))) ” &&
  “ (j < right_pre) ” &&
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((destinationIndex_pre + (output * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i destinationIndex_pre output (0 : Int) count_pre dest_i)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_7 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int))) ” &&
  “ (j < right_pre) ” &&
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((sourceHeight_pre + (j * sizeof(INT)))) # Int |-> ((Znth j source_h (0 : Int))))
  ** (intArray.missing_i sourceHeight_pre j (0 : Int) count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_8 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int))) ” &&
  “ (j < right_pre) ” &&
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((destinationHeight_pre + (output * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i destinationHeight_pre output (0 : Int) count_pre dest_h)
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_9 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int))) ” &&
  “ (j < right_pre) ” &&
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((sourceIndex_pre + (j * sizeof(INT)))) # Int |-> ((Znth j source_i (0 : Int))))
  ** (intArray.missing_i sourceIndex_pre j (0 : Int) count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_10 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int)))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ ((Znth i source_h (0 : Int)) < (Znth j source_h (0 : Int))) ” &&
  “ (j < right_pre) ” &&
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((destinationIndex_pre + (output * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i destinationIndex_pre output (0 : Int) count_pre dest_i)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_11 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (i : Int) (j : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (j = right_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((sourceHeight_pre + (i * sizeof(INT)))) # Int |-> ((Znth i source_h (0 : Int))))
  ** (intArray.missing_i sourceHeight_pre i (0 : Int) count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_12 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (i : Int) (j : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (j = right_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((destinationHeight_pre + (output * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i destinationHeight_pre output (0 : Int) count_pre dest_h)
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_13 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (i : Int) (j : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (j = right_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((sourceIndex_pre + (i * sizeof(INT)))) # Int |-> ((Znth i source_i (0 : Int))))
  ** (intArray.missing_i sourceIndex_pre i (0 : Int) count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_14 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (i : Int) (j : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ (i < middle_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (j = right_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((destinationIndex_pre + (output * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i destinationIndex_pre output (0 : Int) count_pre dest_i)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_15 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ (j < right_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (i = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((sourceHeight_pre + (j * sizeof(INT)))) # Int |-> ((Znth j source_h (0 : Int))))
  ** (intArray.missing_i sourceHeight_pre j (0 : Int) count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_16 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre dest_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ (j < right_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (i = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((destinationHeight_pre + (output * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i destinationHeight_pre output (0 : Int) count_pre dest_h)
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_17 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ (j < right_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (i = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((sourceIndex_pre + (j * sizeof(INT)))) # Int |-> ((Znth j source_i (0 : Int))))
  ** (intArray.missing_i sourceIndex_pre j (0 : Int) count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)

noncomputable def mergeHeightIndexRunsNLogN_partial_solve_wit_18 : Prop :=
  forall (dest0_i : (List Int)) (dest0_h : (List Int)) (source_i : (List Int)) (source_h : (List Int)) (sourceHeight_pre : Int) (sourceIndex_pre : Int) (destinationHeight_pre : Int) (destinationIndex_pre : Int) (count_pre : Int) (left_pre : Int) (middle_pre : Int) (right_pre : Int) (output : Int) (j : Int) (i : Int) (dest_i : (List Int)) (dest_h : (List Int)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre)) + (j - middle_pre)))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output)) ,
  (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)
  ** (intArray.full destinationIndex_pre count_pre dest_i)
|--
  “ (j < right_pre) ” &&
  “ ((Zlength (source_h)) = count_pre) ” &&
  “ ((Zlength (source_i)) = (Zlength (source_h))) ” &&
  “ ((Zlength (dest0_h)) = count_pre) ” &&
  “ ((Zlength (dest0_i)) = count_pre) ” &&
  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” &&
  “ (i = middle_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= i) ” &&
  “ (i <= middle_pre) ” &&
  “ (middle_pre <= j) ” &&
  “ (j <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (output = ((left_pre + (i - left_pre)) + (j - middle_pre))) ” &&
  “ (left_pre <= output) ” &&
  “ (output <= right_pre) ” &&
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output) ”
  &&  (((destinationIndex_pre + (output * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i destinationIndex_pre output (0 : Int) count_pre dest_i)
  ** (intArray.full sourceIndex_pre count_pre source_i)
  ** (intArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h (0 : Int))) (dest_h)))
  ** (intArray.full sourceHeight_pre count_pre source_h)

noncomputable def sortHeightIndexRangeNLogN_safety_wit_1 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((Zlength (work0_h)) = count_pre)) (PreH2 : ((Zlength (work0_i)) = count_pre)) (PreH3 : ((Zlength (buffer0_h)) = count_pre)) (PreH4 : ((Zlength (buffer0_i)) = count_pre)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre <= right_pre)) (PreH7 : (right_pre <= count_pre)) (PreH8 : (count_pre <= 100000)) ,
  ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((right_pre - left_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right_pre - left_pre)) ”

noncomputable def sortHeightIndexRangeNLogN_safety_wit_2 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((Zlength (work0_h)) = count_pre)) (PreH2 : ((Zlength (work0_i)) = count_pre)) (PreH3 : ((Zlength (buffer0_h)) = count_pre)) (PreH4 : ((Zlength (buffer0_i)) = count_pre)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre <= right_pre)) (PreH7 : (right_pre <= count_pre)) (PreH8 : (count_pre <= 100000)) ,
  ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortHeightIndexRangeNLogN_safety_wit_3 : Prop :=
  (
forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”
) \/
(
forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”
)

noncomputable def sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX) ”

noncomputable def sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((INT_MIN) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”

noncomputable def sortHeightIndexRangeNLogN_safety_wit_4 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ (((right_pre - left_pre) ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def sortHeightIndexRangeNLogN_safety_wit_5 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((right_pre - left_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right_pre - left_pre)) ”

noncomputable def sortHeightIndexRangeNLogN_safety_wit_6 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |->_)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def sortHeightIndexRangeNLogN_safety_wit_7 : Prop :=
  forall (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h)) = count_pre)) (PreH8 : ((Zlength (work_i)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h)) = count_pre)) (PreH12 : ((Zlength (buffer_i)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k)) ,
  (intArray.full workIndex_pre count_pre (replace_Znth (k) ((Znth k buffer_i (0 : Int))) (work_i1)))
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** (intArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h (0 : Int))) (work_h1)))
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "middle" ) )) # Int |-> (middle))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def sortHeightIndexRangeNLogN_entail_wit_1 : Prop :=
  (
forall (buffer0_i_2 : (List Int)) (buffer0_h_2 : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_h_3 : (List Int)) (work_i_3 : (List Int)) (dest_h : (List Int)) (dest_i : (List Int)) (PreH1 : (HeightIndexRangeMergeResultNLogN work_h_3 work_i_3 buffer_h_2 buffer_i_2 dest_h dest_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH2 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h_3 work_i_3 (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH3 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH4 : ((right_pre - left_pre) > 1)) (PreH5 : ((Zlength (work0_h)) = count_pre)) (PreH6 : ((Zlength (work0_i)) = count_pre)) (PreH7 : ((Zlength (buffer0_h_2)) = count_pre)) (PreH8 : ((Zlength (buffer0_i_2)) = count_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= right_pre)) (PreH11 : (right_pre <= count_pre)) (PreH12 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h_3)
  ** (intArray.full workIndex_pre count_pre work_i_3)
  ** (intArray.full bufferHeight_pre count_pre dest_h)
  ** (intArray.full bufferIndex_pre count_pre dest_i)
|--
  EX buffer0_h : (List Int), EX buffer0_i : (List Int), EX buffer_i : (List Int), EX buffer_h : (List Int), EX work_i1 : (List Int), EX work_h1 : (List Int), EX work_i : (List Int), EX work_h : (List Int), EX work_mid_i : (List Int), EX work_mid_h : (List Int),
  “ (count_pre <= 100000) ” &&
  “ (left_pre < (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) < right_pre) ” &&
  “ ((Zlength (work_mid_h)) = count_pre) ” &&
  “ ((Zlength (work_mid_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h1)) = count_pre) ” &&
  “ ((Zlength (work_i1)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre) ” &&
  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre) ” &&
  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre left_pre) ”
  &&  (intArray.full workHeight_pre count_pre work_h1)
  ** (intArray.full workIndex_pre count_pre work_i1)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
) \/
(
forall (buffer0_i_2 : (List Int)) (buffer0_h_2 : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_h_3 : (List Int)) (work_i_3 : (List Int)) (dest_h : (List Int)) (dest_i : (List Int)) (PreH1 : (HeightIndexRangeMergeResultNLogN work_h_3 work_i_3 buffer_h_2 buffer_i_2 dest_h dest_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH2 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h_3 work_i_3 (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH3 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH4 : ((right_pre - left_pre) > 1)) (PreH5 : ((Zlength (work0_h)) = count_pre)) (PreH6 : ((Zlength (work0_i)) = count_pre)) (PreH7 : ((Zlength (buffer0_h_2)) = count_pre)) (PreH8 : ((Zlength (buffer0_i_2)) = count_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : (left_pre <= right_pre)) (PreH11 : (right_pre <= count_pre)) (PreH12 : (count_pre <= 100000)) ,
  TT && emp 
|--
  EX buffer0_h : (List Int), EX buffer0_i : (List Int), EX work_i : (List Int), EX work_h : (List Int), EX work_mid_i : (List Int), EX work_mid_h : (List Int),
  “ (left_pre < (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) < right_pre) ” &&
  “ ((Zlength (work_mid_h)) = (Zlength (work0_h))) ” &&
  “ ((Zlength (work_mid_i)) = (Zlength (work0_h))) ” &&
  “ ((Zlength (work_h)) = (Zlength (work0_h))) ” &&
  “ ((Zlength (work_i)) = (Zlength (work0_h))) ” &&
  “ ((Zlength (work_h_3)) = (Zlength (work0_h))) ” &&
  “ ((Zlength (work_i_3)) = (Zlength (work0_h))) ” &&
  “ ((Zlength (dest_h)) = (Zlength (work0_h))) ” &&
  “ ((Zlength (dest_i)) = (Zlength (work0_h))) ” &&
  “ (left_pre <= left_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre) ” &&
  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i dest_h dest_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre) ” &&
  “ (CopyHeightIndexPrefixNLogN dest_h dest_i work_h work_i work_h_3 work_i_3 left_pre right_pre left_pre) ”
  &&  emp
)

noncomputable def sortHeightIndexRangeNLogN_entail_wit_2 : Prop :=
  (
forall (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer0_h_2 : (List Int)) (buffer0_i_2 : (List Int)) (k : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i1_2 : (List Int)) (work_h1_2 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (work_mid_i_2 : (List Int)) (work_mid_h_2 : (List Int)) (middle : Int) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h_2)) = count_pre)) (PreH6 : ((Zlength (work_mid_i_2)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1_2)) = count_pre)) (PreH10 : ((Zlength (work_i1_2)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h_2 work_mid_i_2 left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h_2 work_mid_i_2 work_h_2 work_i_2 middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h_2 buffer0_i_2 buffer_h_2 buffer_i_2 left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1_2 work_i1_2 left_pre right_pre k)) ,
  (intArray.full workIndex_pre count_pre (replace_Znth (k) ((Znth k buffer_i_2 (0 : Int))) (work_i1_2)))
  ** (intArray.full bufferIndex_pre count_pre buffer_i_2)
  ** (intArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h_2 (0 : Int))) (work_h1_2)))
  ** (intArray.full bufferHeight_pre count_pre buffer_h_2)
|--
  EX buffer0_h : (List Int), EX buffer0_i : (List Int), EX buffer_i : (List Int), EX buffer_h : (List Int), EX work_i1 : (List Int), EX work_h1 : (List Int), EX work_i : (List Int), EX work_h : (List Int), EX work_mid_i : (List Int), EX work_mid_h : (List Int),
  “ (count_pre <= 100000) ” &&
  “ (left_pre < middle) ” &&
  “ (middle < right_pre) ” &&
  “ ((Zlength (work_mid_h)) = count_pre) ” &&
  “ ((Zlength (work_mid_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h1)) = count_pre) ” &&
  “ ((Zlength (work_i1)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= (k + 1)) ” &&
  “ ((k + 1) <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle) ” &&
  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre) ” &&
  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre) ” &&
  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre (k + 1)) ”
  &&  (intArray.full workHeight_pre count_pre work_h1)
  ** (intArray.full workIndex_pre count_pre work_i1)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
) \/
(
forall (work0_i : (List Int)) (work0_h : (List Int)) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer0_h_2 : (List Int)) (buffer0_i_2 : (List Int)) (k : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i1_2 : (List Int)) (work_h1_2 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (work_mid_i_2 : (List Int)) (work_mid_h_2 : (List Int)) (middle : Int) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h_2)) = count_pre)) (PreH6 : ((Zlength (work_mid_i_2)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1_2)) = count_pre)) (PreH10 : ((Zlength (work_i1_2)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h_2 work_mid_i_2 left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h_2 work_mid_i_2 work_h_2 work_i_2 middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h_2 buffer0_i_2 buffer_h_2 buffer_i_2 left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1_2 work_i1_2 left_pre right_pre k)) ,
  TT && emp 
|--
  EX buffer0_h : (List Int), EX buffer0_i : (List Int), EX work_i : (List Int), EX work_h : (List Int), EX work_mid_i : (List Int), EX work_mid_h : (List Int),
  “ ((Zlength (work_mid_h)) = (Zlength (work_mid_h_2))) ” &&
  “ ((Zlength (work_mid_i)) = (Zlength (work_mid_h_2))) ” &&
  “ ((Zlength (work_h)) = (Zlength (work_mid_h_2))) ” &&
  “ ((Zlength (work_i)) = (Zlength (work_mid_h_2))) ” &&
  “ ((Zlength ((replace_Znth (k) ((Znth k buffer_h_2 (0 : Int))) (work_h1_2)))) = (Zlength (work_mid_h_2))) ” &&
  “ ((Zlength ((replace_Znth (k) ((Znth k buffer_i_2 (0 : Int))) (work_i1_2)))) = (Zlength (work_mid_h_2))) ” &&
  “ (left_pre <= (k + 1)) ” &&
  “ ((k + 1) <= right_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle) ” &&
  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre) ” &&
  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre) ” &&
  “ (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h work_i (replace_Znth (k) ((Znth k buffer_h_2 (0 : Int))) (work_h1_2)) (replace_Znth (k) ((Znth k buffer_i_2 (0 : Int))) (work_i1_2)) left_pre right_pre (k + 1)) ”
  &&  emp
)

noncomputable def sortHeightIndexRangeNLogN_return_wit_1 : Prop :=
  (
forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) <= 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX work_h : (List Int), EX work_i : (List Int),
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre right_pre) ”
  &&  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
) \/
(
forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) <= 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  TT && emp 
|--
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work0_h work0_i left_pre right_pre) ”
  &&  emp
)

noncomputable def sortHeightIndexRangeNLogN_return_wit_1_split_goal_1 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) <= 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  (HeightIndexRangeSortResultNLogN work0_h work0_i work0_h work0_i left_pre right_pre)

noncomputable def sortHeightIndexRangeNLogN_return_wit_2 : Prop :=
  (
forall (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k >= right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_2 work_i_2 middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1 work_i1 left_pre right_pre k)) ,
  (intArray.full workHeight_pre count_pre work_h1)
  ** (intArray.full workIndex_pre count_pre work_i1)
  ** (intArray.full bufferHeight_pre count_pre buffer_h_2)
  ** (intArray.full bufferIndex_pre count_pre buffer_i_2)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX work_h : (List Int), EX work_i : (List Int),
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre right_pre) ”
  &&  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
) \/
(
forall (work0_i : (List Int)) (work0_h : (List Int)) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k >= right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_2 work_i_2 middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1 work_i1 left_pre right_pre k)) ,
  TT && emp 
|--
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h1 work_i1 left_pre right_pre) ”
  &&  emp
)

noncomputable def sortHeightIndexRangeNLogN_return_wit_2_split_goal_1 : Prop :=
  forall (work0_i : (List Int)) (work0_h : (List Int)) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k >= right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_2 work_i_2 middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1 work_i1 left_pre right_pre k)) ,
  (HeightIndexRangeSortResultNLogN work0_h work0_i work_h1 work_i1 left_pre right_pre)

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_1_pure : Prop :=
  (
forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((Zlength (work0_h)) = count_pre) ” &&
  “ ((Zlength (work0_i)) = count_pre) ” &&
  “ ((Zlength (buffer0_h)) = count_pre) ” &&
  “ ((Zlength (buffer0_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (count_pre <= 100000) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= count_pre) ” &&
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”
) \/
(
forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : ((right_pre - left_pre) > 1)) (PreH10 : ((Zlength (work0_h)) = count_pre)) (PreH11 : ((Zlength (work0_i)) = count_pre)) (PreH12 : ((Zlength (buffer0_h)) = count_pre)) (PreH13 : ((Zlength (buffer0_i)) = count_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= count_pre) ”
)

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : ((right_pre - left_pre) > 1)) (PreH10 : ((Zlength (work0_h)) = count_pre)) (PreH11 : ((Zlength (work0_i)) = count_pre)) (PreH12 : ((Zlength (buffer0_h)) = count_pre)) (PreH13 : ((Zlength (buffer0_i)) = count_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : ((right_pre - left_pre) > 1)) (PreH10 : ((Zlength (work0_h)) = count_pre)) (PreH11 : ((Zlength (work0_i)) = count_pre)) (PreH12 : ((Zlength (buffer0_h)) = count_pre)) (PreH13 : ((Zlength (buffer0_i)) = count_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= count_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_1_aux : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((right_pre - left_pre) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)
|--
  “ ((Zlength (work0_h)) = count_pre) ” &&
  “ ((Zlength (work0_i)) = count_pre) ” &&
  “ ((Zlength (buffer0_h)) = count_pre) ” &&
  “ ((Zlength (buffer0_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (count_pre <= 100000) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= count_pre) ” &&
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((right_pre - left_pre) > 1) ” &&
  “ ((Zlength (work0_h)) = count_pre) ” &&
  “ ((Zlength (work0_i)) = count_pre) ” &&
  “ ((Zlength (buffer0_h)) = count_pre) ” &&
  “ ((Zlength (buffer0_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (count_pre <= 100000) ”
  &&  (intArray.full workHeight_pre count_pre work0_h)
  ** (intArray.full workIndex_pre count_pre work0_i)
  ** (intArray.full bufferHeight_pre count_pre buffer0_h)
  ** (intArray.full bufferIndex_pre count_pre buffer0_i)

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_1 : Prop := sortHeightIndexRangeNLogN_partial_solve_wit_1_pure -> sortHeightIndexRangeNLogN_partial_solve_wit_1_aux

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_2_pure : Prop :=
  (
forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH2 : ((right_pre - left_pre) > 1)) (PreH3 : ((Zlength (work0_h)) = count_pre)) (PreH4 : ((Zlength (work0_i)) = count_pre)) (PreH5 : ((Zlength (buffer0_h)) = count_pre)) (PreH6 : ((Zlength (buffer0_i)) = count_pre)) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre <= count_pre)) (PreH10 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ (right_pre <= count_pre) ” &&
  “ (count_pre <= 100000) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ” &&
  “ ((0 : Int) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ”
) \/
(
forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((0 : Int) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ”
)

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (work_h)) = count_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (work_i)) = count_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (buffer_h)) = count_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (buffer_i)) = count_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((0 : Int) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH10 : ((right_pre - left_pre) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_2_aux : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH2 : ((right_pre - left_pre) > 1)) (PreH3 : ((Zlength (work0_h)) = count_pre)) (PreH4 : ((Zlength (work0_i)) = count_pre)) (PreH5 : ((Zlength (buffer0_h)) = count_pre)) (PreH6 : ((Zlength (buffer0_i)) = count_pre)) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre <= count_pre)) (PreH10 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
|--
  “ (right_pre <= count_pre) ” &&
  “ (count_pre <= 100000) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ” &&
  “ ((0 : Int) <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((right_pre - left_pre) > 1) ” &&
  “ ((Zlength (work0_h)) = count_pre) ” &&
  “ ((Zlength (work0_i)) = count_pre) ” &&
  “ ((Zlength (buffer0_h)) = count_pre) ” &&
  “ ((Zlength (buffer0_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (count_pre <= 100000) ”
  &&  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_2 : Prop := sortHeightIndexRangeNLogN_partial_solve_wit_2_pure -> sortHeightIndexRangeNLogN_partial_solve_wit_2_aux

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3_pure : Prop :=
  (
forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH2 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH3 : ((right_pre - left_pre) > 1)) (PreH4 : ((Zlength (work0_h)) = count_pre)) (PreH5 : ((Zlength (work0_i)) = count_pre)) (PreH6 : ((Zlength (buffer0_h)) = count_pre)) (PreH7 : ((Zlength (buffer0_i)) = count_pre)) (PreH8 : ((0 : Int) <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre <= count_pre)) (PreH11 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((0 : Int) <= left_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (HeightIndexRangeDescendingNLogN work_h (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre) ” &&
  “ (HeightIndexRangeDescendingNLogN work_h left_pre (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ” &&
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ”
) \/
(
forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH11 : ((right_pre - left_pre) > 1)) (PreH12 : ((Zlength (work0_h)) = count_pre)) (PreH13 : ((Zlength (work0_i)) = count_pre)) (PreH14 : ((Zlength (buffer0_h)) = count_pre)) (PreH15 : ((Zlength (buffer0_i)) = count_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre <= count_pre)) (PreH19 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ” &&
  “ (HeightIndexRangeDescendingNLogN work_h left_pre (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ (HeightIndexRangeDescendingNLogN work_h (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre) ”
)

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_1 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH11 : ((right_pre - left_pre) > 1)) (PreH12 : ((Zlength (work0_h)) = count_pre)) (PreH13 : ((Zlength (work0_i)) = count_pre)) (PreH14 : ((Zlength (buffer0_h)) = count_pre)) (PreH15 : ((Zlength (buffer0_i)) = count_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre <= count_pre)) (PreH19 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (work_h)) = count_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_2 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH11 : ((right_pre - left_pre) > 1)) (PreH12 : ((Zlength (work0_h)) = count_pre)) (PreH13 : ((Zlength (work0_i)) = count_pre)) (PreH14 : ((Zlength (buffer0_h)) = count_pre)) (PreH15 : ((Zlength (buffer0_i)) = count_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre <= count_pre)) (PreH19 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (work_i)) = count_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_3 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH11 : ((right_pre - left_pre) > 1)) (PreH12 : ((Zlength (work0_h)) = count_pre)) (PreH13 : ((Zlength (work0_i)) = count_pre)) (PreH14 : ((Zlength (buffer0_h)) = count_pre)) (PreH15 : ((Zlength (buffer0_i)) = count_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre <= count_pre)) (PreH19 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (buffer_h)) = count_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_4 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH11 : ((right_pre - left_pre) > 1)) (PreH12 : ((Zlength (work0_h)) = count_pre)) (PreH13 : ((Zlength (work0_i)) = count_pre)) (PreH14 : ((Zlength (buffer0_h)) = count_pre)) (PreH15 : ((Zlength (buffer0_i)) = count_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre <= count_pre)) (PreH19 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((Zlength (buffer_i)) = count_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_5 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH11 : ((right_pre - left_pre) > 1)) (PreH12 : ((Zlength (work0_h)) = count_pre)) (PreH13 : ((Zlength (work0_i)) = count_pre)) (PreH14 : ((Zlength (buffer0_h)) = count_pre)) (PreH15 : ((Zlength (buffer0_i)) = count_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre <= count_pre)) (PreH19 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_6 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH11 : ((right_pre - left_pre) > 1)) (PreH12 : ((Zlength (work0_h)) = count_pre)) (PreH13 : ((Zlength (work0_i)) = count_pre)) (PreH14 : ((Zlength (buffer0_h)) = count_pre)) (PreH15 : ((Zlength (buffer0_i)) = count_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre <= count_pre)) (PreH19 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_7 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH11 : ((right_pre - left_pre) > 1)) (PreH12 : ((Zlength (work0_h)) = count_pre)) (PreH13 : ((Zlength (work0_i)) = count_pre)) (PreH14 : ((Zlength (buffer0_h)) = count_pre)) (PreH15 : ((Zlength (buffer0_i)) = count_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre <= count_pre)) (PreH19 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ (HeightIndexRangeDescendingNLogN work_h left_pre (left_pre + (Z.quot (right_pre - left_pre) 2))) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_8 : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + (Z.quot (right_pre - left_pre) 2)) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH11 : ((right_pre - left_pre) > 1)) (PreH12 : ((Zlength (work0_h)) = count_pre)) (PreH13 : ((Zlength (work0_i)) = count_pre)) (PreH14 : ((Zlength (buffer0_h)) = count_pre)) (PreH15 : ((Zlength (buffer0_i)) = count_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre <= count_pre)) (PreH19 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** ((( &( "middle" ) )) # Int |-> ((left_pre + (Z.quot (right_pre - left_pre) 2))))
  ** ((( &( "workHeight" ) )) # Ptr |-> (workHeight_pre))
  ** ((( &( "workIndex" ) )) # Ptr |-> (workIndex_pre))
  ** ((( &( "bufferHeight" ) )) # Ptr |-> (bufferHeight_pre))
  ** ((( &( "bufferIndex" ) )) # Ptr |-> (bufferIndex_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ (HeightIndexRangeDescendingNLogN work_h (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre) ”

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3_aux : Prop :=
  forall (buffer0_i : (List Int)) (buffer0_h : (List Int)) (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (work_h_2 : (List Int)) (work_i_2 : (List Int)) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre)) (PreH2 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2)))) (PreH3 : ((right_pre - left_pre) > 1)) (PreH4 : ((Zlength (work0_h)) = count_pre)) (PreH5 : ((Zlength (work0_i)) = count_pre)) (PreH6 : ((Zlength (buffer0_h)) = count_pre)) (PreH7 : ((Zlength (buffer0_i)) = count_pre)) (PreH8 : ((0 : Int) <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre <= count_pre)) (PreH11 : (count_pre <= 100000)) ,
  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
|--
  “ ((0 : Int) <= left_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (HeightIndexRangeDescendingNLogN work_h (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre) ” &&
  “ (HeightIndexRangeDescendingNLogN work_h left_pre (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((left_pre + (Z.quot (right_pre - left_pre) 2)) <= right_pre) ” &&
  “ (left_pre <= (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h work_i (left_pre + (Z.quot (right_pre - left_pre) 2)) right_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + (Z.quot (right_pre - left_pre) 2))) ” &&
  “ ((right_pre - left_pre) > 1) ” &&
  “ ((Zlength (work0_h)) = count_pre) ” &&
  “ ((Zlength (work0_i)) = count_pre) ” &&
  “ ((Zlength (buffer0_h)) = count_pre) ” &&
  “ ((Zlength (buffer0_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (count_pre <= 100000) ”
  &&  (intArray.full workHeight_pre count_pre work_h)
  ** (intArray.full workIndex_pre count_pre work_i)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_3 : Prop := sortHeightIndexRangeNLogN_partial_solve_wit_3_pure -> sortHeightIndexRangeNLogN_partial_solve_wit_3_aux

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_4 : Prop :=
  forall (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h)) = count_pre)) (PreH8 : ((Zlength (work_i)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h)) = count_pre)) (PreH12 : ((Zlength (buffer_i)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k)) ,
  (intArray.full workHeight_pre count_pre work_h1)
  ** (intArray.full workIndex_pre count_pre work_i1)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
|--
  “ (k < right_pre) ” &&
  “ (count_pre <= 100000) ” &&
  “ (left_pre < middle) ” &&
  “ (middle < right_pre) ” &&
  “ ((Zlength (work_mid_h)) = count_pre) ” &&
  “ ((Zlength (work_mid_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h1)) = count_pre) ” &&
  “ ((Zlength (work_i1)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= k) ” &&
  “ (k <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle) ” &&
  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre) ” &&
  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre) ” &&
  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k) ”
  &&  (((bufferHeight_pre + (k * sizeof(INT)))) # Int |-> ((Znth k buffer_h (0 : Int))))
  ** (intArray.missing_i bufferHeight_pre k (0 : Int) count_pre buffer_h)
  ** (intArray.full workHeight_pre count_pre work_h1)
  ** (intArray.full workIndex_pre count_pre work_i1)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_5 : Prop :=
  forall (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h)) = count_pre)) (PreH8 : ((Zlength (work_i)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h)) = count_pre)) (PreH12 : ((Zlength (buffer_i)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k)) ,
  (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full workHeight_pre count_pre work_h1)
  ** (intArray.full workIndex_pre count_pre work_i1)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
|--
  “ (k < right_pre) ” &&
  “ (count_pre <= 100000) ” &&
  “ (left_pre < middle) ” &&
  “ (middle < right_pre) ” &&
  “ ((Zlength (work_mid_h)) = count_pre) ” &&
  “ ((Zlength (work_mid_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h1)) = count_pre) ” &&
  “ ((Zlength (work_i1)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= k) ” &&
  “ (k <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle) ” &&
  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre) ” &&
  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre) ” &&
  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k) ”
  &&  (((workHeight_pre + (k * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i workHeight_pre k (0 : Int) count_pre work_h1)
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full workIndex_pre count_pre work_i1)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_6 : Prop :=
  forall (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h)) = count_pre)) (PreH8 : ((Zlength (work_i)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h)) = count_pre)) (PreH12 : ((Zlength (buffer_i)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k)) ,
  (intArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h (0 : Int))) (work_h1)))
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full workIndex_pre count_pre work_i1)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
|--
  “ (k < right_pre) ” &&
  “ (count_pre <= 100000) ” &&
  “ (left_pre < middle) ” &&
  “ (middle < right_pre) ” &&
  “ ((Zlength (work_mid_h)) = count_pre) ” &&
  “ ((Zlength (work_mid_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h1)) = count_pre) ” &&
  “ ((Zlength (work_i1)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= k) ” &&
  “ (k <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle) ” &&
  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre) ” &&
  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre) ” &&
  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k) ”
  &&  (((bufferIndex_pre + (k * sizeof(INT)))) # Int |-> ((Znth k buffer_i (0 : Int))))
  ** (intArray.missing_i bufferIndex_pre k (0 : Int) count_pre buffer_i)
  ** (intArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h (0 : Int))) (work_h1)))
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full workIndex_pre count_pre work_i1)

noncomputable def sortHeightIndexRangeNLogN_partial_solve_wit_7 : Prop :=
  forall (work0_i : (List Int)) (work0_h : (List Int)) (workHeight_pre : Int) (workIndex_pre : Int) (bufferHeight_pre : Int) (bufferIndex_pre : Int) (count_pre : Int) (left_pre : Int) (right_pre : Int) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (k : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i1 : (List Int)) (work_h1 : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (work_mid_i : (List Int)) (work_mid_h : (List Int)) (middle : Int) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h)) = count_pre)) (PreH8 : ((Zlength (work_i)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h)) = count_pre)) (PreH12 : ((Zlength (buffer_i)) = count_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle)) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre)) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre)) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k)) ,
  (intArray.full bufferIndex_pre count_pre buffer_i)
  ** (intArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h (0 : Int))) (work_h1)))
  ** (intArray.full bufferHeight_pre count_pre buffer_h)
  ** (intArray.full workIndex_pre count_pre work_i1)
|--
  “ (k < right_pre) ” &&
  “ (count_pre <= 100000) ” &&
  “ (left_pre < middle) ” &&
  “ (middle < right_pre) ” &&
  “ ((Zlength (work_mid_h)) = count_pre) ” &&
  “ ((Zlength (work_mid_i)) = count_pre) ” &&
  “ ((Zlength (work_h)) = count_pre) ” &&
  “ ((Zlength (work_i)) = count_pre) ” &&
  “ ((Zlength (work_h1)) = count_pre) ” &&
  “ ((Zlength (work_i1)) = count_pre) ” &&
  “ ((Zlength (buffer_h)) = count_pre) ” &&
  “ ((Zlength (buffer_i)) = count_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= k) ” &&
  “ (k <= right_pre) ” &&
  “ (right_pre <= count_pre) ” &&
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle) ” &&
  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre) ” &&
  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre) ” &&
  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k) ”
  &&  (((workIndex_pre + (k * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i workIndex_pre k (0 : Int) count_pre work_i1)
  ** (intArray.full bufferIndex_pre count_pre buffer_i)
  ** (intArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h (0 : Int))) (work_h1)))
  ** (intArray.full bufferHeight_pre count_pre buffer_h)

noncomputable def maxAreaNLogN_safety_wit_1 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "k" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_2 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "bufferIndex" ) ) (k + 1) (buffer_i ++ (k :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "bufferHeight" ) ) (k + 1) (buffer_h ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workIndex" ) ) (k + 1) (work_i ++ (k :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workHeight" ) ) (k + 1) (work_h ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full height_pre heightSize_pre l)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_3 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (work0_h : (List Int)) (work0_i : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((Zlength (work0_h)) = heightSize_pre)) (PreH5 : ((Zlength (work0_i)) = heightSize_pre)) (PreH6 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH8 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_4 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (work0_h : (List Int)) (work0_i : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((Zlength (work0_h)) = heightSize_pre)) (PreH5 : ((Zlength (work0_i)) = heightSize_pre)) (PreH6 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH8 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_5 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (work0_h : (List Int)) (work0_i : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((Zlength (work0_h)) = heightSize_pre)) (PreH5 : ((Zlength (work0_i)) = heightSize_pre)) (PreH6 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH8 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_6 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (work0_h : (List Int)) (work0_i : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((Zlength (work0_h)) = heightSize_pre)) (PreH5 : ((Zlength (work0_i)) = heightSize_pre)) (PreH6 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH8 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_7 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (work0_h : (List Int)) (work0_i : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((Zlength (work0_h)) = heightSize_pre)) (PreH5 : ((Zlength (work0_i)) = heightSize_pre)) (PreH6 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH8 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_8 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "minimumIndex" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_9 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "maximumIndex" ) )) # Int |->_)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "minimumIndex" ) )) # Int |-> ((Znth (0 : Int) sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_10 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "maximumArea" ) )) # Int |->_)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "maximumIndex" ) )) # Int |-> ((Znth (0 : Int) sorted_i (0 : Int))))
  ** ((( &( "minimumIndex" ) )) # Int |-> ((Znth (0 : Int) sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_11 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "k" ) )) # Int |->_)
  ** ((( &( "maximumArea" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "maximumIndex" ) )) # Int |-> ((Znth (0 : Int) sorted_i (0 : Int))))
  ** ((( &( "minimumIndex" ) )) # Int |-> ((Znth (0 : Int) sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def maxAreaNLogN_safety_wit_12 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMinimum" ) )) # Int |->_)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ”
) \/
(
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMinimum" ) )) # Int |->_)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ”
)

noncomputable def maxAreaNLogN_safety_wit_12_split_goal_1 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMinimum" ) )) # Int |->_)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= INT_MAX) ”

noncomputable def maxAreaNLogN_safety_wit_12_split_goal_2 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMinimum" ) )) # Int |->_)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((INT_MIN) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ”

noncomputable def maxAreaNLogN_safety_wit_13 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |->_)
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (((Znth k sorted_i (0 : Int)) - minimumIndex)))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ”
) \/
(
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |->_)
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (((Znth k sorted_i (0 : Int)) - minimumIndex)))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ”
)

noncomputable def maxAreaNLogN_safety_wit_13_split_goal_1 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |->_)
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (((Znth k sorted_i (0 : Int)) - minimumIndex)))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= INT_MAX) ”

noncomputable def maxAreaNLogN_safety_wit_13_split_goal_2 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |->_)
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (((Znth k sorted_i (0 : Int)) - minimumIndex)))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((INT_MIN) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ”

noncomputable def maxAreaNLogN_safety_wit_14 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |-> ((maximumIndex - (Znth k sorted_i (0 : Int)))))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (((Znth k sorted_i (0 : Int)) - minimumIndex)))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_15 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) < (0 : Int))) (PreH2 : (k < heightSize_pre)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k <= heightSize_pre)) (PreH8 : ((0 : Int) <= minimumIndex)) (PreH9 : (minimumIndex <= maximumIndex)) (PreH10 : (maximumIndex < heightSize_pre)) (PreH11 : ((0 : Int) <= maximumArea)) (PreH12 : (maximumArea <= 999990000)) (PreH13 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH14 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH15 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |-> ((maximumIndex - (Znth k sorted_i (0 : Int)))))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (((Znth k sorted_i (0 : Int)) - minimumIndex)))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) ≠ (INT_MIN)) ”

noncomputable def maxAreaNLogN_safety_wit_16 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) < (0 : Int))) (PreH2 : (k < heightSize_pre)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k <= heightSize_pre)) (PreH8 : ((0 : Int) <= minimumIndex)) (PreH9 : (minimumIndex <= maximumIndex)) (PreH10 : (maximumIndex < heightSize_pre)) (PreH11 : ((0 : Int) <= maximumArea)) (PreH12 : (maximumArea <= 999990000)) (PreH13 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH14 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH15 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |-> ((maximumIndex - (Znth k sorted_i (0 : Int)))))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> ((-((Znth k sorted_i (0 : Int)) - minimumIndex))))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_17 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH2 : (k < heightSize_pre)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k <= heightSize_pre)) (PreH8 : ((0 : Int) <= minimumIndex)) (PreH9 : (minimumIndex <= maximumIndex)) (PreH10 : (maximumIndex < heightSize_pre)) (PreH11 : ((0 : Int) <= maximumArea)) (PreH12 : (maximumArea <= 999990000)) (PreH13 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH14 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH15 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |-> ((maximumIndex - (Znth k sorted_i (0 : Int)))))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (((Znth k sorted_i (0 : Int)) - minimumIndex)))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaNLogN_safety_wit_18 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH2 : (((Znth k sorted_i (0 : Int)) - minimumIndex) < (0 : Int))) (PreH3 : (k < heightSize_pre)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k <= heightSize_pre)) (PreH9 : ((0 : Int) <= minimumIndex)) (PreH10 : (minimumIndex <= maximumIndex)) (PreH11 : (maximumIndex < heightSize_pre)) (PreH12 : ((0 : Int) <= maximumArea)) (PreH13 : (maximumArea <= 999990000)) (PreH14 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH15 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH16 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |-> ((maximumIndex - (Znth k sorted_i (0 : Int)))))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> ((-((Znth k sorted_i (0 : Int)) - minimumIndex))))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_19 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH2 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH3 : (k < heightSize_pre)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k <= heightSize_pre)) (PreH9 : ((0 : Int) <= minimumIndex)) (PreH10 : (minimumIndex <= maximumIndex)) (PreH11 : (maximumIndex < heightSize_pre)) (PreH12 : ((0 : Int) <= maximumArea)) (PreH13 : (maximumArea <= 999990000)) (PreH14 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH15 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH16 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |-> ((maximumIndex - (Znth k sorted_i (0 : Int)))))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (((Znth k sorted_i (0 : Int)) - minimumIndex)))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) ≠ (INT_MIN)) ”

noncomputable def maxAreaNLogN_safety_wit_20 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : ((-((Znth k sorted_i (0 : Int)) - minimumIndex)) > (maximumIndex - (Znth k sorted_i (0 : Int))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) >= (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) < (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "width" ) )) # Int |->_)
  ** ((( &( "distanceToMaximum" ) )) # Int |-> ((maximumIndex - (Znth k sorted_i (0 : Int)))))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> ((-((Znth k sorted_i (0 : Int)) - minimumIndex))))
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** ((( &( "currentHeight" ) )) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** ((( &( "index" ) )) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_21 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i (0 : Int)))) (PreH7 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH8 : (currentHeight = (Znth index l (0 : Int)))) (PreH9 : ((0 : Int) <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : ((0 : Int) <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : ((0 : Int) <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : ((0 : Int) <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : ((0 : Int) <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (minimumIndex - index))) (PreH21 : (distanceToMaximum = (maximumIndex - index))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMaximum)) (PreH25 : ((0 : Int) <= width)) (PreH26 : (width <= 99999)) (PreH27 : ((0 : Int) <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (width * currentHeight)) ”

noncomputable def maxAreaNLogN_safety_wit_22 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i (0 : Int)))) (PreH7 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH8 : (currentHeight = (Znth index l (0 : Int)))) (PreH9 : ((0 : Int) <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : ((0 : Int) <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : ((0 : Int) <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : ((0 : Int) <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : ((0 : Int) <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (minimumIndex - index))) (PreH21 : (distanceToMaximum = (maximumIndex - index))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMinimum)) (PreH25 : ((0 : Int) <= width)) (PreH26 : (width <= 99999)) (PreH27 : ((0 : Int) <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (width * currentHeight)) ”

noncomputable def maxAreaNLogN_safety_wit_23 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i (0 : Int)))) (PreH7 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH8 : (currentHeight = (Znth index l (0 : Int)))) (PreH9 : ((0 : Int) <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : ((0 : Int) <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : ((0 : Int) <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : ((0 : Int) <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : ((0 : Int) <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (minimumIndex - index))) (PreH21 : (distanceToMaximum = (index - maximumIndex))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMaximum)) (PreH25 : ((0 : Int) <= width)) (PreH26 : (width <= 99999)) (PreH27 : ((0 : Int) <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (width * currentHeight)) ”

noncomputable def maxAreaNLogN_safety_wit_24 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i (0 : Int)))) (PreH7 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH8 : (currentHeight = (Znth index l (0 : Int)))) (PreH9 : ((0 : Int) <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : ((0 : Int) <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : ((0 : Int) <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : ((0 : Int) <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : ((0 : Int) <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (minimumIndex - index))) (PreH21 : (distanceToMaximum = (index - maximumIndex))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMinimum)) (PreH25 : ((0 : Int) <= width)) (PreH26 : (width <= 99999)) (PreH27 : ((0 : Int) <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (width * currentHeight)) ”

noncomputable def maxAreaNLogN_safety_wit_25 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i (0 : Int)))) (PreH7 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH8 : (currentHeight = (Znth index l (0 : Int)))) (PreH9 : ((0 : Int) <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : ((0 : Int) <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : ((0 : Int) <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : ((0 : Int) <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : ((0 : Int) <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (index - minimumIndex))) (PreH21 : (distanceToMaximum = (maximumIndex - index))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMaximum)) (PreH25 : ((0 : Int) <= width)) (PreH26 : (width <= 99999)) (PreH27 : ((0 : Int) <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (width * currentHeight)) ”

noncomputable def maxAreaNLogN_safety_wit_26 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i (0 : Int)))) (PreH7 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH8 : (currentHeight = (Znth index l (0 : Int)))) (PreH9 : ((0 : Int) <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : ((0 : Int) <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : ((0 : Int) <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : ((0 : Int) <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : ((0 : Int) <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (index - minimumIndex))) (PreH21 : (distanceToMaximum = (maximumIndex - index))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMinimum)) (PreH25 : ((0 : Int) <= width)) (PreH26 : (width <= 99999)) (PreH27 : ((0 : Int) <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (width * currentHeight)) ”

noncomputable def maxAreaNLogN_safety_wit_27 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i (0 : Int)))) (PreH7 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH8 : (currentHeight = (Znth index l (0 : Int)))) (PreH9 : ((0 : Int) <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : ((0 : Int) <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : ((0 : Int) <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : ((0 : Int) <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : ((0 : Int) <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (index - minimumIndex))) (PreH21 : (distanceToMaximum = (index - maximumIndex))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMaximum)) (PreH25 : ((0 : Int) <= width)) (PreH26 : (width <= 99999)) (PreH27 : ((0 : Int) <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (width * currentHeight)) ”

noncomputable def maxAreaNLogN_safety_wit_28 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i (0 : Int)))) (PreH7 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH8 : (currentHeight = (Znth index l (0 : Int)))) (PreH9 : ((0 : Int) <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : ((0 : Int) <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : ((0 : Int) <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : ((0 : Int) <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : ((0 : Int) <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (index - minimumIndex))) (PreH21 : (distanceToMaximum = (index - maximumIndex))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMinimum)) (PreH25 : ((0 : Int) <= width)) (PreH26 : (width <= 99999)) (PreH27 : ((0 : Int) <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (width * currentHeight)) ”

noncomputable def maxAreaNLogN_safety_wit_29 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index))) (PreH23 : (distanceToMaximum = (index - maximumIndex))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_30 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index))) (PreH23 : (distanceToMaximum = (index - maximumIndex))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_31 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex))) (PreH23 : (distanceToMaximum = (maximumIndex - index))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_32 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex))) (PreH23 : (distanceToMaximum = (maximumIndex - index))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_33 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex))) (PreH23 : (distanceToMaximum = (index - maximumIndex))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_34 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex))) (PreH23 : (distanceToMaximum = (index - maximumIndex))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_35 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index))) (PreH23 : (distanceToMaximum = (index - maximumIndex))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_36 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index))) (PreH23 : (distanceToMaximum = (index - maximumIndex))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_37 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex))) (PreH23 : (distanceToMaximum = (maximumIndex - index))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_38 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex))) (PreH23 : (distanceToMaximum = (maximumIndex - index))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_39 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex))) (PreH23 : (distanceToMaximum = (index - maximumIndex))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_40 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex))) (PreH23 : (distanceToMaximum = (index - maximumIndex))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_41 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i (0 : Int)))) (PreH27 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH28 : (currentHeight = (Znth index l (0 : Int)))) (PreH29 : ((0 : Int) <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : ((0 : Int) <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : ((0 : Int) <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : ((0 : Int) <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : ((0 : Int) <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index))) (PreH41 : (distanceToMaximum = (maximumIndex - index))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMaximum)) (PreH45 : ((0 : Int) <= width)) (PreH46 : (width <= 99999)) (PreH47 : ((0 : Int) <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH53 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_42 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i (0 : Int)))) (PreH27 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH28 : (currentHeight = (Znth index l (0 : Int)))) (PreH29 : ((0 : Int) <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : ((0 : Int) <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : ((0 : Int) <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : ((0 : Int) <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : ((0 : Int) <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index))) (PreH41 : (distanceToMaximum = (maximumIndex - index))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMinimum)) (PreH45 : ((0 : Int) <= width)) (PreH46 : (width <= 99999)) (PreH47 : ((0 : Int) <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH53 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_43 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i (0 : Int)))) (PreH29 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH30 : (currentHeight = (Znth index l (0 : Int)))) (PreH31 : ((0 : Int) <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : ((0 : Int) <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : ((0 : Int) <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : ((0 : Int) <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : ((0 : Int) <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index))) (PreH43 : (distanceToMaximum = (maximumIndex - index))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMaximum)) (PreH47 : ((0 : Int) <= width)) (PreH48 : (width <= 99999)) (PreH49 : ((0 : Int) <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH55 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_44 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i (0 : Int)))) (PreH29 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH30 : (currentHeight = (Znth index l (0 : Int)))) (PreH31 : ((0 : Int) <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : ((0 : Int) <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : ((0 : Int) <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : ((0 : Int) <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : ((0 : Int) <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index))) (PreH43 : (distanceToMaximum = (maximumIndex - index))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMinimum)) (PreH47 : ((0 : Int) <= width)) (PreH48 : (width <= 99999)) (PreH49 : ((0 : Int) <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH55 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_45 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_46 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_47 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_48 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_49 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_50 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_51 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_52 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_53 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_54 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_55 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_56 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ False ”

noncomputable def maxAreaNLogN_safety_wit_57 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (distanceToMaximum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight) >= INT_MIN)) (PreH18 : (index > maximumIndex)) (PreH19 : (index >= minimumIndex)) (PreH20 : ((width * currentHeight) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i (0 : Int)))) (PreH27 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH28 : (currentHeight = (Znth index l (0 : Int)))) (PreH29 : ((0 : Int) <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : ((0 : Int) <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : ((0 : Int) <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : ((0 : Int) <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : ((0 : Int) <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (index - minimumIndex))) (PreH41 : (distanceToMaximum = (index - maximumIndex))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMaximum)) (PreH45 : ((0 : Int) <= width)) (PreH46 : (width <= 99999)) (PreH47 : ((0 : Int) <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH53 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_58 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (distanceToMaximum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight) >= INT_MIN)) (PreH18 : (index > maximumIndex)) (PreH19 : (index >= minimumIndex)) (PreH20 : ((width * currentHeight) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i (0 : Int)))) (PreH27 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH28 : (currentHeight = (Znth index l (0 : Int)))) (PreH29 : ((0 : Int) <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : ((0 : Int) <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : ((0 : Int) <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : ((0 : Int) <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : ((0 : Int) <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (index - minimumIndex))) (PreH41 : (distanceToMaximum = (index - maximumIndex))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMinimum)) (PreH45 : ((0 : Int) <= width)) (PreH46 : (width <= 99999)) (PreH47 : ((0 : Int) <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH53 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_59 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMaximum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMaximum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight) >= INT_MIN)) (PreH20 : (index > maximumIndex)) (PreH21 : (index >= minimumIndex)) (PreH22 : ((width * currentHeight) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i (0 : Int)))) (PreH29 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH30 : (currentHeight = (Znth index l (0 : Int)))) (PreH31 : ((0 : Int) <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : ((0 : Int) <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : ((0 : Int) <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : ((0 : Int) <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : ((0 : Int) <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (index - minimumIndex))) (PreH43 : (distanceToMaximum = (index - maximumIndex))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMaximum)) (PreH47 : ((0 : Int) <= width)) (PreH48 : (width <= 99999)) (PreH49 : ((0 : Int) <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH55 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_60 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMaximum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMaximum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight) >= INT_MIN)) (PreH20 : (index > maximumIndex)) (PreH21 : (index >= minimumIndex)) (PreH22 : ((width * currentHeight) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i (0 : Int)))) (PreH29 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH30 : (currentHeight = (Znth index l (0 : Int)))) (PreH31 : ((0 : Int) <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : ((0 : Int) <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : ((0 : Int) <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : ((0 : Int) <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : ((0 : Int) <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (index - minimumIndex))) (PreH43 : (distanceToMaximum = (index - maximumIndex))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMinimum)) (PreH47 : ((0 : Int) <= width)) (PreH48 : (width <= 99999)) (PreH49 : ((0 : Int) <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH55 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_61 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i (0 : Int)))) (PreH27 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH28 : (currentHeight = (Znth index l (0 : Int)))) (PreH29 : ((0 : Int) <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : ((0 : Int) <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : ((0 : Int) <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : ((0 : Int) <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : ((0 : Int) <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index))) (PreH41 : (distanceToMaximum = (maximumIndex - index))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMaximum)) (PreH45 : ((0 : Int) <= width)) (PreH46 : (width <= 99999)) (PreH47 : ((0 : Int) <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH53 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_62 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i (0 : Int)))) (PreH27 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH28 : (currentHeight = (Znth index l (0 : Int)))) (PreH29 : ((0 : Int) <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : ((0 : Int) <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : ((0 : Int) <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : ((0 : Int) <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : ((0 : Int) <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index))) (PreH41 : (distanceToMaximum = (maximumIndex - index))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMinimum)) (PreH45 : ((0 : Int) <= width)) (PreH46 : (width <= 99999)) (PreH47 : ((0 : Int) <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH53 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_63 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i (0 : Int)))) (PreH29 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH30 : (currentHeight = (Znth index l (0 : Int)))) (PreH31 : ((0 : Int) <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : ((0 : Int) <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : ((0 : Int) <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : ((0 : Int) <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : ((0 : Int) <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index))) (PreH43 : (distanceToMaximum = (maximumIndex - index))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMaximum)) (PreH47 : ((0 : Int) <= width)) (PreH48 : (width <= 99999)) (PreH49 : ((0 : Int) <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH55 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_64 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i (0 : Int)))) (PreH29 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH30 : (currentHeight = (Znth index l (0 : Int)))) (PreH31 : ((0 : Int) <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : ((0 : Int) <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : ((0 : Int) <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : ((0 : Int) <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : ((0 : Int) <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index))) (PreH43 : (distanceToMaximum = (maximumIndex - index))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMinimum)) (PreH47 : ((0 : Int) <= width)) (PreH48 : (width <= 99999)) (PreH49 : ((0 : Int) <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH55 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (index))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_65 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_66 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_67 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_68 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_69 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_70 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_71 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_72 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_73 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_74 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_75 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_76 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_77 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_78 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_79 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_safety_wit_80 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def maxAreaNLogN_entail_wit_1 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
  ** (intArray.full height_pre heightSize_pre l)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX work_i : (List Int), EX work_h : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= heightSize_pre) ” &&
  “ ((Zlength (work_h)) = (0 : Int)) ” &&
  “ ((Zlength (work_i)) = (0 : Int)) ” &&
  “ ((Zlength (buffer_h)) = (0 : Int)) ” &&
  “ ((Zlength (buffer_i)) = (0 : Int)) ” &&
  “ (WorkspacePrefixNLogN l work_h work_i (0 : Int)) ” &&
  “ (WorkspacePrefixNLogN l buffer_h buffer_i (0 : Int)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) (0 : Int) work_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) (0 : Int) work_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) (0 : Int) buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) (0 : Int) buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
|--
  “ (WorkspacePrefixNLogN l (@List.nil Int) (@List.nil Int) (0 : Int)) ” &&
  “ (WorkspacePrefixNLogN l (@List.nil Int) (@List.nil Int) (0 : Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  (intArray.undef_seg ( &( "workHeight" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
)

noncomputable def maxAreaNLogN_entail_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
|--
  “ (WorkspacePrefixNLogN l (@List.nil Int) (@List.nil Int) (0 : Int)) ”

noncomputable def maxAreaNLogN_entail_wit_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
|--
  “ (WorkspacePrefixNLogN l (@List.nil Int) (@List.nil Int) (0 : Int)) ”

noncomputable def maxAreaNLogN_entail_wit_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
|--
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”

noncomputable def maxAreaNLogN_entail_wit_1_split_goal_4 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
|--
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”

noncomputable def maxAreaNLogN_entail_wit_1_split_goal_5 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
|--
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”

noncomputable def maxAreaNLogN_entail_wit_1_split_goal_6 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
|--
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”

noncomputable def maxAreaNLogN_entail_wit_1_split_goal_spatial : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
|--
  (intArray.undef_seg ( &( "workHeight" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) (0 : Int) heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)

noncomputable def maxAreaNLogN_entail_wit_2 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "bufferIndex" ) ) (k + 1) (buffer_i_2 ++ (k :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "bufferHeight" ) ) (k + 1) (buffer_h_2 ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workIndex" ) ) (k + 1) (work_i_2 ++ (k :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workHeight" ) ) (k + 1) (work_h_2 ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX work_i : (List Int), EX work_h : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((Zlength (work_h)) = (k + 1)) ” &&
  “ ((Zlength (work_i)) = (k + 1)) ” &&
  “ ((Zlength (buffer_h)) = (k + 1)) ” &&
  “ ((Zlength (buffer_i)) = (k + 1)) ” &&
  “ (WorkspacePrefixNLogN l work_h work_i (k + 1)) ” &&
  “ (WorkspacePrefixNLogN l buffer_h buffer_i (k + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) (k + 1) work_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) (k + 1) work_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) (k + 1) buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) (k + 1) buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (WorkspacePrefixNLogN l (buffer_h_2 ++ ((Znth k l (0 : Int)) :: (@List.nil Int))) (buffer_i_2 ++ (k :: (@List.nil Int))) (k + 1)) ” &&
  “ (WorkspacePrefixNLogN l (work_h_2 ++ ((Znth k l (0 : Int)) :: (@List.nil Int))) (work_i_2 ++ (k :: (@List.nil Int))) (k + 1)) ” &&
  “ ((Zlength ((buffer_i_2 ++ (k :: (@List.nil Int))))) = (k + 1)) ” &&
  “ ((Zlength ((buffer_h_2 ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))) = (k + 1)) ” &&
  “ ((Zlength ((work_i_2 ++ (k :: (@List.nil Int))))) = (k + 1)) ” &&
  “ ((Zlength ((work_h_2 ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))) = (k + 1)) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (WorkspacePrefixNLogN l (buffer_h_2 ++ ((Znth k l (0 : Int)) :: (@List.nil Int))) (buffer_i_2 ++ (k :: (@List.nil Int))) (k + 1))

noncomputable def maxAreaNLogN_entail_wit_2_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (WorkspacePrefixNLogN l (work_h_2 ++ ((Znth k l (0 : Int)) :: (@List.nil Int))) (work_i_2 ++ (k :: (@List.nil Int))) (k + 1))

noncomputable def maxAreaNLogN_entail_wit_2_split_goal_3 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Zlength ((buffer_i_2 ++ (k :: (@List.nil Int))))) = (k + 1))

noncomputable def maxAreaNLogN_entail_wit_2_split_goal_4 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Zlength ((buffer_h_2 ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))) = (k + 1))

noncomputable def maxAreaNLogN_entail_wit_2_split_goal_5 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Zlength ((work_i_2 ++ (k :: (@List.nil Int))))) = (k + 1))

noncomputable def maxAreaNLogN_entail_wit_2_split_goal_6 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_i_2 : (List Int)) (work_h_2 : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Zlength ((work_h_2 ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))) = (k + 1))

noncomputable def maxAreaNLogN_entail_wit_3 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (k : Int) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) k work_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) k work_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) k buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer0_i : (List Int), EX buffer0_h : (List Int), EX work0_i : (List Int), EX work0_h : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((Zlength (work0_h)) = heightSize_pre) ” &&
  “ ((Zlength (work0_i)) = heightSize_pre) ” &&
  “ ((Zlength (buffer0_h)) = heightSize_pre) ” &&
  “ ((Zlength (buffer0_i)) = heightSize_pre) ” &&
  “ (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre) ” &&
  “ (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (k : Int) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workHeight" ) ) k work_h)
  ** (intArray.full ( &( "workIndex" ) ) k work_i)
  ** (intArray.full ( &( "bufferHeight" ) ) k buffer_h)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
|--
  EX buffer0_i : (List Int), EX buffer0_h : (List Int), EX work0_i : (List Int), EX work0_h : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((Zlength (work0_h)) = heightSize_pre) ” &&
  “ ((Zlength (work0_i)) = heightSize_pre) ” &&
  “ ((Zlength (buffer0_h)) = heightSize_pre) ” &&
  “ ((Zlength (buffer0_i)) = heightSize_pre) ” &&
  “ (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre) ” &&
  “ (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_h)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_i)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_h)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_i)
)

noncomputable def maxAreaNLogN_entail_wit_4 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (work0_h : (List Int)) (work0_i : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i (0 : Int) heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((Zlength (work0_h)) = heightSize_pre)) (PreH6 : ((Zlength (work0_i)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH8 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre)) (PreH10 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work_h)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work_i)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer_h_2)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer_i_2)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (work0_h : (List Int)) (work0_i : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (work_h : (List Int)) (work_i : (List Int)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i (0 : Int) heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((Zlength (work0_h)) = heightSize_pre)) (PreH6 : ((Zlength (work0_i)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH8 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre)) (PreH10 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work_h)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work_i)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer_h_2)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer_i_2)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
)

noncomputable def maxAreaNLogN_entail_wit_5 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) sorted_i (0 : Int))) ” &&
  “ ((Znth (0 : Int) sorted_i (0 : Int)) <= (Znth (0 : Int) sorted_i (0 : Int))) ” &&
  “ ((Znth (0 : Int) sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 1 (Znth (0 : Int) sorted_i (0 : Int)) (Znth (0 : Int) sorted_i (0 : Int))) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 1 (0 : Int)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i 1 (0 : Int)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i 1 (Znth (0 : Int) sorted_i (0 : Int)) (Znth (0 : Int) sorted_i (0 : Int))) ” &&
  “ ((Znth (0 : Int) sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) sorted_i (0 : Int))) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_5_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i 1 (0 : Int))

noncomputable def maxAreaNLogN_entail_wit_5_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i 1 (Znth (0 : Int) sorted_i (0 : Int)) (Znth (0 : Int) sorted_i (0 : Int)))

noncomputable def maxAreaNLogN_entail_wit_5_split_goal_3 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth (0 : Int) sorted_i (0 : Int)) < heightSize_pre)

noncomputable def maxAreaNLogN_entail_wit_5_split_goal_4 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((0 : Int) <= (Znth (0 : Int) sorted_i (0 : Int)))

noncomputable def maxAreaNLogN_entail_wit_6_1 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) > (-(maximumIndex - (Znth k sorted_i (0 : Int)))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (-(maximumIndex - (Znth k sorted_i (0 : Int))))) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) = ((Znth k sorted_i (0 : Int)) - maximumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) > (-(maximumIndex - (Znth k sorted_i (0 : Int)))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_6_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) > (-(maximumIndex - (Znth k sorted_i (0 : Int)))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999)

noncomputable def maxAreaNLogN_entail_wit_6_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) > (-(maximumIndex - (Znth k sorted_i (0 : Int)))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) <= 99999)

noncomputable def maxAreaNLogN_entail_wit_6_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) > (-(maximumIndex - (Znth k sorted_i (0 : Int)))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999)

noncomputable def maxAreaNLogN_entail_wit_6_1_split_goal_4 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) > (-(maximumIndex - (Znth k sorted_i (0 : Int)))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth k sorted_h (0 : Int)) <= 10000)

noncomputable def maxAreaNLogN_entail_wit_6_1_split_goal_5 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) > (-(maximumIndex - (Znth k sorted_i (0 : Int)))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((0 : Int) <= (Znth k sorted_h (0 : Int)))

noncomputable def maxAreaNLogN_entail_wit_6_1_split_goal_6 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) > (-(maximumIndex - (Znth k sorted_i (0 : Int)))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth k sorted_i (0 : Int)) < heightSize_pre)

noncomputable def maxAreaNLogN_entail_wit_6_1_split_goal_7 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) > (-(maximumIndex - (Znth k sorted_i (0 : Int)))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int)))

noncomputable def maxAreaNLogN_entail_wit_6_2 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) > (maximumIndex - (Znth k sorted_i (0 : Int))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) >= (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = ((Znth k sorted_i (0 : Int)) - maximumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_6_3 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (-(maximumIndex - (Znth k sorted_i (0 : Int)))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) < (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (-(maximumIndex - (Znth k sorted_i (0 : Int))))) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) = ((Znth k sorted_i (0 : Int)) - maximumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (-(maximumIndex - (Znth k sorted_i (0 : Int))))) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) <= (-(maximumIndex - (Znth k sorted_i (0 : Int))))) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) = (-(maximumIndex - (Znth k sorted_i (0 : Int))))) ” &&
  “ ((0 : Int) <= (-(maximumIndex - (Znth k sorted_i (0 : Int))))) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (-(maximumIndex - (Znth k sorted_i (0 : Int))))) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) = ((Znth k sorted_i (0 : Int)) - maximumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (-(maximumIndex - (Znth k sorted_i (0 : Int))))) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) <= (-(maximumIndex - (Znth k sorted_i (0 : Int))))) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((0 : Int) <= (-(maximumIndex - (Znth k sorted_i (0 : Int))))) ” &&
  “ ((-(maximumIndex - (Znth k sorted_i (0 : Int)))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_6_4 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : ((-((Znth k sorted_i (0 : Int)) - minimumIndex)) <= (maximumIndex - (Znth k sorted_i (0 : Int))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) >= (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) < (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= (-((Znth k sorted_i (0 : Int)) - minimumIndex))) ” &&
  “ ((-((Znth k sorted_i (0 : Int)) - minimumIndex)) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((-((Znth k sorted_i (0 : Int)) - minimumIndex)) = (minimumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((-((Znth k sorted_i (0 : Int)) - minimumIndex)) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= (-((Znth k sorted_i (0 : Int)) - minimumIndex))) ” &&
  “ ((-((Znth k sorted_i (0 : Int)) - minimumIndex)) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((-((Znth k sorted_i (0 : Int)) - minimumIndex)) = (minimumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((-((Znth k sorted_i (0 : Int)) - minimumIndex)) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (-((Znth k sorted_i (0 : Int)) - minimumIndex))) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_6_5 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i_2 : (List Int)) (buffer_h_2 : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (maximumIndex - (Znth k sorted_i (0 : Int))))) (PreH2 : ((maximumIndex - (Znth k sorted_i (0 : Int))) >= (0 : Int))) (PreH3 : (((Znth k sorted_i (0 : Int)) - minimumIndex) >= (0 : Int))) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : ((0 : Int) <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : ((0 : Int) <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = (minimumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = (minimumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = (minimumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = ((Znth k sorted_i (0 : Int)) - maximumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = (minimumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = ((Znth k sorted_i (0 : Int)) - maximumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = ((Znth k sorted_i (0 : Int)) - maximumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h_2 : (List Int), EX sorted_i_2 : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ ((Znth k sorted_i (0 : Int)) = (Znth k sorted_i_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth k sorted_h_2 (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) = (Znth (Znth k sorted_i (0 : Int)) l (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth k sorted_i (0 : Int))) ” &&
  “ ((Znth k sorted_i (0 : Int)) < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (Znth k sorted_h (0 : Int))) ” &&
  “ ((Znth k sorted_h (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= 99999) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = ((Znth k sorted_i (0 : Int)) - maximumIndex)) ” &&
  “ (((Znth k sorted_i (0 : Int)) - minimumIndex) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) = ((Znth k sorted_i (0 : Int)) - minimumIndex)) ” &&
  “ ((0 : Int) <= (maximumIndex - (Znth k sorted_i (0 : Int)))) ” &&
  “ ((maximumIndex - (Znth k sorted_i (0 : Int))) <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_7_1 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index))) (PreH23 : (distanceToMaximum = (maximumIndex - index))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (“ (distanceToMaximum = distanceToMaximum) ” &&
  “ (distanceToMinimum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (distanceToMinimum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index < minimumIndex) ” &&
  “ ((width * currentHeight) > maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (minimumIndex - index)) ” &&
  “ (distanceToMaximum = (maximumIndex - index)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX k_2 : Int, EX index_2 : Int, EX currentHeight_2 : Int, EX minimumIndex_2 : Int, EX maximumIndex_2 : Int, EX distanceToMinimum_2 : Int, EX distanceToMaximum_2 : Int, EX width_2 : Int, EX maximumArea_2 : Int,
  “ (distanceToMaximum_2 = distanceToMaximum_2) ” &&
  “ (distanceToMinimum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (distanceToMinimum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 < minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) > maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2)) ” &&
  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX k_2 : Int, EX index_2 : Int, EX currentHeight_2 : Int, EX minimumIndex_2 : Int, EX maximumIndex_2 : Int, EX distanceToMinimum_2 : Int, EX distanceToMaximum_2 : Int, EX width_2 : Int, EX maximumArea_2 : Int,
  “ (distanceToMaximum_2 = distanceToMaximum_2) ” &&
  “ (maximumArea_2 <= INT_MAX) ” &&
  “ (distanceToMinimum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (maximumArea_2 >= INT_MIN) ” &&
  “ (distanceToMinimum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 < minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) <= maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2)) ” &&
  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea_2))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_7_2 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k_2 : Int) (index_2 : Int) (currentHeight_2 : Int) (minimumIndex_2 : Int) (maximumIndex_2 : Int) (distanceToMinimum_2 : Int) (distanceToMaximum_2 : Int) (width_2 : Int) (maximumArea_2 : Int) (PreH1 : (index_2 < minimumIndex_2)) (PreH2 : ((width_2 * currentHeight_2) > maximumArea_2)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k_2)) (PreH7 : (k_2 < heightSize_pre)) (PreH8 : (index_2 = (Znth k_2 sorted_i (0 : Int)))) (PreH9 : (currentHeight_2 = (Znth k_2 sorted_h (0 : Int)))) (PreH10 : (currentHeight_2 = (Znth index_2 l (0 : Int)))) (PreH11 : ((0 : Int) <= index_2)) (PreH12 : (index_2 < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex_2)) (PreH14 : (minimumIndex_2 <= maximumIndex_2)) (PreH15 : (maximumIndex_2 < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight_2)) (PreH17 : (currentHeight_2 <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum_2)) (PreH19 : (distanceToMinimum_2 <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum_2)) (PreH21 : (distanceToMaximum_2 <= 99999)) (PreH22 : (distanceToMinimum_2 = (minimumIndex_2 - index_2))) (PreH23 : (distanceToMaximum_2 = (maximumIndex_2 - index_2))) (PreH24 : (distanceToMinimum_2 <= width_2)) (PreH25 : (distanceToMaximum_2 <= width_2)) (PreH26 : (width_2 = distanceToMinimum_2)) (PreH27 : ((0 : Int) <= width_2)) (PreH28 : (width_2 <= 99999)) (PreH29 : ((0 : Int) <= maximumArea_2)) (PreH30 : (maximumArea_2 <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "width" ) )) # Int |-> (width_2))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (EX k : Int, EX index : Int, EX currentHeight : Int, EX minimumIndex : Int, EX maximumIndex : Int, EX distanceToMinimum : Int, EX distanceToMaximum : Int, EX width : Int, EX maximumArea : Int,
  “ (distanceToMaximum = distanceToMaximum) ” &&
  “ (distanceToMinimum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (distanceToMinimum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index < minimumIndex) ” &&
  “ ((width * currentHeight) > maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (minimumIndex - index)) ” &&
  “ (distanceToMaximum = (maximumIndex - index)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (“ (distanceToMaximum_2 = distanceToMaximum_2) ” &&
  “ (distanceToMinimum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (distanceToMinimum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 < minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) > maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2)) ” &&
  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX k : Int, EX index : Int, EX currentHeight : Int, EX minimumIndex : Int, EX maximumIndex : Int, EX distanceToMinimum : Int, EX distanceToMaximum : Int, EX width : Int, EX maximumArea : Int,
  “ (distanceToMaximum = distanceToMaximum) ” &&
  “ (maximumArea <= INT_MAX) ” &&
  “ (distanceToMinimum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (maximumArea >= INT_MIN) ” &&
  “ (distanceToMinimum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index < minimumIndex) ” &&
  “ ((width * currentHeight) <= maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (minimumIndex - index)) ” &&
  “ (distanceToMaximum = (maximumIndex - index)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_7_3 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i (0 : Int)))) (PreH9 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH10 : (currentHeight = (Znth index l (0 : Int)))) (PreH11 : ((0 : Int) <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index))) (PreH23 : (distanceToMaximum = (maximumIndex - index))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : ((0 : Int) <= width)) (PreH28 : (width <= 99999)) (PreH29 : ((0 : Int) <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (EX k_2 : Int, EX index_2 : Int, EX currentHeight_2 : Int, EX minimumIndex_2 : Int, EX maximumIndex_2 : Int, EX distanceToMinimum_2 : Int, EX distanceToMaximum_2 : Int, EX width_2 : Int, EX maximumArea_2 : Int,
  “ (distanceToMaximum_2 = distanceToMaximum_2) ” &&
  “ (distanceToMinimum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (distanceToMinimum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 < minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) > maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2)) ” &&
  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (“ (distanceToMaximum = distanceToMaximum) ” &&
  “ (maximumArea <= INT_MAX) ” &&
  “ (distanceToMinimum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (maximumArea >= INT_MIN) ” &&
  “ (distanceToMinimum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index < minimumIndex) ” &&
  “ ((width * currentHeight) <= maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (minimumIndex - index)) ” &&
  “ (distanceToMaximum = (maximumIndex - index)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX k_2 : Int, EX index_2 : Int, EX currentHeight_2 : Int, EX minimumIndex_2 : Int, EX maximumIndex_2 : Int, EX distanceToMinimum_2 : Int, EX distanceToMaximum_2 : Int, EX width_2 : Int, EX maximumArea_2 : Int,
  “ (distanceToMaximum_2 = distanceToMaximum_2) ” &&
  “ (maximumArea_2 <= INT_MAX) ” &&
  “ (distanceToMinimum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (maximumArea_2 >= INT_MIN) ” &&
  “ (distanceToMinimum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 < minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) <= maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2)) ” &&
  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea_2))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_7_4 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k_2 : Int) (index_2 : Int) (currentHeight_2 : Int) (minimumIndex_2 : Int) (maximumIndex_2 : Int) (distanceToMinimum_2 : Int) (distanceToMaximum_2 : Int) (width_2 : Int) (maximumArea_2 : Int) (PreH1 : (index_2 < minimumIndex_2)) (PreH2 : ((width_2 * currentHeight_2) <= maximumArea_2)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k_2)) (PreH7 : (k_2 < heightSize_pre)) (PreH8 : (index_2 = (Znth k_2 sorted_i (0 : Int)))) (PreH9 : (currentHeight_2 = (Znth k_2 sorted_h (0 : Int)))) (PreH10 : (currentHeight_2 = (Znth index_2 l (0 : Int)))) (PreH11 : ((0 : Int) <= index_2)) (PreH12 : (index_2 < heightSize_pre)) (PreH13 : ((0 : Int) <= minimumIndex_2)) (PreH14 : (minimumIndex_2 <= maximumIndex_2)) (PreH15 : (maximumIndex_2 < heightSize_pre)) (PreH16 : ((0 : Int) <= currentHeight_2)) (PreH17 : (currentHeight_2 <= 10000)) (PreH18 : ((0 : Int) <= distanceToMinimum_2)) (PreH19 : (distanceToMinimum_2 <= 99999)) (PreH20 : ((0 : Int) <= distanceToMaximum_2)) (PreH21 : (distanceToMaximum_2 <= 99999)) (PreH22 : (distanceToMinimum_2 = (minimumIndex_2 - index_2))) (PreH23 : (distanceToMaximum_2 = (maximumIndex_2 - index_2))) (PreH24 : (distanceToMinimum_2 <= width_2)) (PreH25 : (distanceToMaximum_2 <= width_2)) (PreH26 : (width_2 = distanceToMinimum_2)) (PreH27 : ((0 : Int) <= width_2)) (PreH28 : (width_2 <= 99999)) (PreH29 : ((0 : Int) <= maximumArea_2)) (PreH30 : (maximumArea_2 <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2)) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "width" ) )) # Int |-> (width_2))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea_2))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (EX k : Int, EX index : Int, EX currentHeight : Int, EX minimumIndex : Int, EX maximumIndex : Int, EX distanceToMinimum : Int, EX distanceToMaximum : Int, EX width : Int, EX maximumArea : Int,
  “ (distanceToMaximum = distanceToMaximum) ” &&
  “ (distanceToMinimum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (distanceToMinimum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index < minimumIndex) ” &&
  “ ((width * currentHeight) > maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (minimumIndex - index)) ” &&
  “ (distanceToMaximum = (maximumIndex - index)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX k : Int, EX index : Int, EX currentHeight : Int, EX minimumIndex : Int, EX maximumIndex : Int, EX distanceToMinimum : Int, EX distanceToMaximum : Int, EX width : Int, EX maximumArea : Int,
  “ (distanceToMaximum = distanceToMaximum) ” &&
  “ (maximumArea <= INT_MAX) ” &&
  “ (distanceToMinimum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (maximumArea >= INT_MIN) ” &&
  “ (distanceToMinimum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index < minimumIndex) ” &&
  “ ((width * currentHeight) <= maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (minimumIndex - index)) ” &&
  “ (distanceToMaximum = (maximumIndex - index)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (“ (distanceToMaximum_2 = distanceToMaximum_2) ” &&
  “ (maximumArea_2 <= INT_MAX) ” &&
  “ (distanceToMinimum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (maximumArea_2 >= INT_MIN) ” &&
  “ (distanceToMinimum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 < minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) <= maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2)) ” &&
  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea_2))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_8_1 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (“ (distanceToMinimum = distanceToMinimum) ” &&
  “ (distanceToMaximum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (distanceToMaximum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index > maximumIndex) ” &&
  “ (index >= minimumIndex) ” &&
  “ ((width * currentHeight) > maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (index - minimumIndex)) ” &&
  “ (distanceToMaximum = (index - maximumIndex)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX k_2 : Int, EX index_2 : Int, EX currentHeight_2 : Int, EX minimumIndex_2 : Int, EX maximumIndex_2 : Int, EX distanceToMinimum_2 : Int, EX distanceToMaximum_2 : Int, EX width_2 : Int, EX maximumArea_2 : Int,
  “ (distanceToMinimum_2 = distanceToMinimum_2) ” &&
  “ (distanceToMaximum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (distanceToMaximum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 > maximumIndex_2) ” &&
  “ (index_2 >= minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) > maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2)) ” &&
  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX k_2 : Int, EX index_2 : Int, EX currentHeight_2 : Int, EX minimumIndex_2 : Int, EX maximumIndex_2 : Int, EX distanceToMinimum_2 : Int, EX distanceToMaximum_2 : Int, EX width_2 : Int, EX maximumArea_2 : Int,
  “ (distanceToMinimum_2 = distanceToMinimum_2) ” &&
  “ (maximumArea_2 <= INT_MAX) ” &&
  “ (distanceToMaximum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (maximumArea_2 >= INT_MIN) ” &&
  “ (distanceToMaximum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 > maximumIndex_2) ” &&
  “ (index_2 >= minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) <= maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2)) ” &&
  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea_2))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_8_2 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k_2 : Int) (index_2 : Int) (currentHeight_2 : Int) (minimumIndex_2 : Int) (maximumIndex_2 : Int) (distanceToMinimum_2 : Int) (distanceToMaximum_2 : Int) (width_2 : Int) (maximumArea_2 : Int) (PreH1 : (index_2 > maximumIndex_2)) (PreH2 : (index_2 >= minimumIndex_2)) (PreH3 : ((width_2 * currentHeight_2) > maximumArea_2)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k_2)) (PreH8 : (k_2 < heightSize_pre)) (PreH9 : (index_2 = (Znth k_2 sorted_i (0 : Int)))) (PreH10 : (currentHeight_2 = (Znth k_2 sorted_h (0 : Int)))) (PreH11 : (currentHeight_2 = (Znth index_2 l (0 : Int)))) (PreH12 : ((0 : Int) <= index_2)) (PreH13 : (index_2 < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex_2)) (PreH15 : (minimumIndex_2 <= maximumIndex_2)) (PreH16 : (maximumIndex_2 < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight_2)) (PreH18 : (currentHeight_2 <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum_2)) (PreH20 : (distanceToMinimum_2 <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum_2)) (PreH22 : (distanceToMaximum_2 <= 99999)) (PreH23 : (distanceToMinimum_2 = (index_2 - minimumIndex_2))) (PreH24 : (distanceToMaximum_2 = (index_2 - maximumIndex_2))) (PreH25 : (distanceToMinimum_2 <= width_2)) (PreH26 : (distanceToMaximum_2 <= width_2)) (PreH27 : (width_2 = distanceToMinimum_2)) (PreH28 : ((0 : Int) <= width_2)) (PreH29 : (width_2 <= 99999)) (PreH30 : ((0 : Int) <= maximumArea_2)) (PreH31 : (maximumArea_2 <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "width" ) )) # Int |-> (width_2))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (EX k : Int, EX index : Int, EX currentHeight : Int, EX minimumIndex : Int, EX maximumIndex : Int, EX distanceToMinimum : Int, EX distanceToMaximum : Int, EX width : Int, EX maximumArea : Int,
  “ (distanceToMinimum = distanceToMinimum) ” &&
  “ (distanceToMaximum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (distanceToMaximum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index > maximumIndex) ” &&
  “ (index >= minimumIndex) ” &&
  “ ((width * currentHeight) > maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (index - minimumIndex)) ” &&
  “ (distanceToMaximum = (index - maximumIndex)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (“ (distanceToMinimum_2 = distanceToMinimum_2) ” &&
  “ (distanceToMaximum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (distanceToMaximum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 > maximumIndex_2) ” &&
  “ (index_2 >= minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) > maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2)) ” &&
  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX k : Int, EX index : Int, EX currentHeight : Int, EX minimumIndex : Int, EX maximumIndex : Int, EX distanceToMinimum : Int, EX distanceToMaximum : Int, EX width : Int, EX maximumArea : Int,
  “ (distanceToMinimum = distanceToMinimum) ” &&
  “ (maximumArea <= INT_MAX) ” &&
  “ (distanceToMaximum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (maximumArea >= INT_MIN) ” &&
  “ (distanceToMaximum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index > maximumIndex) ” &&
  “ (index >= minimumIndex) ” &&
  “ ((width * currentHeight) <= maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (index - minimumIndex)) ” &&
  “ (distanceToMaximum = (index - maximumIndex)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_8_3 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (EX k_2 : Int, EX index_2 : Int, EX currentHeight_2 : Int, EX minimumIndex_2 : Int, EX maximumIndex_2 : Int, EX distanceToMinimum_2 : Int, EX distanceToMaximum_2 : Int, EX width_2 : Int, EX maximumArea_2 : Int,
  “ (distanceToMinimum_2 = distanceToMinimum_2) ” &&
  “ (distanceToMaximum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (distanceToMaximum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 > maximumIndex_2) ” &&
  “ (index_2 >= minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) > maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2)) ” &&
  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (“ (distanceToMinimum = distanceToMinimum) ” &&
  “ (maximumArea <= INT_MAX) ” &&
  “ (distanceToMaximum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (maximumArea >= INT_MIN) ” &&
  “ (distanceToMaximum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index > maximumIndex) ” &&
  “ (index >= minimumIndex) ” &&
  “ ((width * currentHeight) <= maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (index - minimumIndex)) ” &&
  “ (distanceToMaximum = (index - maximumIndex)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX k_2 : Int, EX index_2 : Int, EX currentHeight_2 : Int, EX minimumIndex_2 : Int, EX maximumIndex_2 : Int, EX distanceToMinimum_2 : Int, EX distanceToMaximum_2 : Int, EX width_2 : Int, EX maximumArea_2 : Int,
  “ (distanceToMinimum_2 = distanceToMinimum_2) ” &&
  “ (maximumArea_2 <= INT_MAX) ” &&
  “ (distanceToMaximum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (maximumArea_2 >= INT_MIN) ” &&
  “ (distanceToMaximum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 > maximumIndex_2) ” &&
  “ (index_2 >= minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) <= maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2)) ” &&
  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea_2))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_8_4 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (k_2 : Int) (index_2 : Int) (currentHeight_2 : Int) (minimumIndex_2 : Int) (maximumIndex_2 : Int) (distanceToMinimum_2 : Int) (distanceToMaximum_2 : Int) (width_2 : Int) (maximumArea_2 : Int) (PreH1 : (index_2 > maximumIndex_2)) (PreH2 : (index_2 >= minimumIndex_2)) (PreH3 : ((width_2 * currentHeight_2) <= maximumArea_2)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k_2)) (PreH8 : (k_2 < heightSize_pre)) (PreH9 : (index_2 = (Znth k_2 sorted_i (0 : Int)))) (PreH10 : (currentHeight_2 = (Znth k_2 sorted_h (0 : Int)))) (PreH11 : (currentHeight_2 = (Znth index_2 l (0 : Int)))) (PreH12 : ((0 : Int) <= index_2)) (PreH13 : (index_2 < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex_2)) (PreH15 : (minimumIndex_2 <= maximumIndex_2)) (PreH16 : (maximumIndex_2 < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight_2)) (PreH18 : (currentHeight_2 <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum_2)) (PreH20 : (distanceToMinimum_2 <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum_2)) (PreH22 : (distanceToMaximum_2 <= 99999)) (PreH23 : (distanceToMinimum_2 = (index_2 - minimumIndex_2))) (PreH24 : (distanceToMaximum_2 = (index_2 - maximumIndex_2))) (PreH25 : (distanceToMinimum_2 <= width_2)) (PreH26 : (distanceToMaximum_2 <= width_2)) (PreH27 : (width_2 = distanceToMinimum_2)) (PreH28 : ((0 : Int) <= width_2)) (PreH29 : (width_2 <= 99999)) (PreH30 : ((0 : Int) <= maximumArea_2)) (PreH31 : (maximumArea_2 <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "width" ) )) # Int |-> (width_2))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea_2))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (EX k : Int, EX index : Int, EX currentHeight : Int, EX minimumIndex : Int, EX maximumIndex : Int, EX distanceToMinimum : Int, EX distanceToMaximum : Int, EX width : Int, EX maximumArea : Int,
  “ (distanceToMinimum = distanceToMinimum) ” &&
  “ (distanceToMaximum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (distanceToMaximum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index > maximumIndex) ” &&
  “ (index >= minimumIndex) ” &&
  “ ((width * currentHeight) > maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (index - minimumIndex)) ” &&
  “ (distanceToMaximum = (index - maximumIndex)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "maximumArea" ) )) # Int |-> ((width * currentHeight)))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (EX k : Int, EX index : Int, EX currentHeight : Int, EX minimumIndex : Int, EX maximumIndex : Int, EX distanceToMinimum : Int, EX distanceToMaximum : Int, EX width : Int, EX maximumArea : Int,
  “ (distanceToMinimum = distanceToMinimum) ” &&
  “ (maximumArea <= INT_MAX) ” &&
  “ (distanceToMaximum <= INT_MAX) ” &&
  “ (maximumIndex <= INT_MAX) ” &&
  “ (minimumIndex <= INT_MAX) ” &&
  “ (currentHeight <= INT_MAX) ” &&
  “ (index <= INT_MAX) ” &&
  “ (k <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width * currentHeight) <= INT_MAX) ” &&
  “ (maximumArea >= INT_MIN) ” &&
  “ (distanceToMaximum >= INT_MIN) ” &&
  “ (maximumIndex >= INT_MIN) ” &&
  “ (minimumIndex >= INT_MIN) ” &&
  “ (currentHeight >= INT_MIN) ” &&
  “ (index >= INT_MIN) ” &&
  “ (k >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width * currentHeight) >= INT_MIN) ” &&
  “ (index > maximumIndex) ” &&
  “ (index >= minimumIndex) ” &&
  “ ((width * currentHeight) <= maximumArea) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k < heightSize_pre) ” &&
  “ (index = (Znth k sorted_i (0 : Int))) ” &&
  “ (currentHeight = (Znth k sorted_h (0 : Int))) ” &&
  “ (currentHeight = (Znth index l (0 : Int))) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight) ” &&
  “ (currentHeight <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum) ” &&
  “ (distanceToMinimum <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum) ” &&
  “ (distanceToMaximum <= 99999) ” &&
  “ (distanceToMinimum = (index - minimumIndex)) ” &&
  “ (distanceToMaximum = (index - maximumIndex)) ” &&
  “ (distanceToMinimum <= width) ” &&
  “ (distanceToMaximum <= width) ” &&
  “ (width = distanceToMaximum) ” &&
  “ ((0 : Int) <= width) ” &&
  “ (width <= 99999) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum))
  ** ((( &( "area" ) )) # Int |-> ((width * currentHeight)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "index" ) )) # Int |-> (index))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))
  ||
  (“ (distanceToMinimum_2 = distanceToMinimum_2) ” &&
  “ (maximumArea_2 <= INT_MAX) ” &&
  “ (distanceToMaximum_2 <= INT_MAX) ” &&
  “ (maximumIndex_2 <= INT_MAX) ” &&
  “ (minimumIndex_2 <= INT_MAX) ” &&
  “ (currentHeight_2 <= INT_MAX) ” &&
  “ (index_2 <= INT_MAX) ” &&
  “ (k_2 <= INT_MAX) ” &&
  “ (heightSize_pre <= INT_MAX) ” &&
  “ ((width_2 * currentHeight_2) <= INT_MAX) ” &&
  “ (maximumArea_2 >= INT_MIN) ” &&
  “ (distanceToMaximum_2 >= INT_MIN) ” &&
  “ (maximumIndex_2 >= INT_MIN) ” &&
  “ (minimumIndex_2 >= INT_MIN) ” &&
  “ (currentHeight_2 >= INT_MIN) ” &&
  “ (index_2 >= INT_MIN) ” &&
  “ (k_2 >= INT_MIN) ” &&
  “ (heightSize_pre >= INT_MIN) ” &&
  “ ((width_2 * currentHeight_2) >= INT_MIN) ” &&
  “ (index_2 > maximumIndex_2) ” &&
  “ (index_2 >= minimumIndex_2) ” &&
  “ ((width_2 * currentHeight_2) <= maximumArea_2) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k_2) ” &&
  “ (k_2 < heightSize_pre) ” &&
  “ (index_2 = (Znth k_2 sorted_i (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth k_2 sorted_h (0 : Int))) ” &&
  “ (currentHeight_2 = (Znth index_2 l (0 : Int))) ” &&
  “ ((0 : Int) <= index_2) ” &&
  “ (index_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex_2) ” &&
  “ (minimumIndex_2 <= maximumIndex_2) ” &&
  “ (maximumIndex_2 < heightSize_pre) ” &&
  “ ((0 : Int) <= currentHeight_2) ” &&
  “ (currentHeight_2 <= 10000) ” &&
  “ ((0 : Int) <= distanceToMinimum_2) ” &&
  “ (distanceToMinimum_2 <= 99999) ” &&
  “ ((0 : Int) <= distanceToMaximum_2) ” &&
  “ (distanceToMaximum_2 <= 99999) ” &&
  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2)) ” &&
  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2)) ” &&
  “ (distanceToMinimum_2 <= width_2) ” &&
  “ (distanceToMaximum_2 <= width_2) ” &&
  “ (width_2 = distanceToMinimum_2) ” &&
  “ ((0 : Int) <= width_2) ” &&
  “ (width_2 <= 99999) ” &&
  “ ((0 : Int) <= maximumArea_2) ” &&
  “ (maximumArea_2 <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "width" ) )) # Int |-> (distanceToMinimum_2))
  ** ((( &( "area" ) )) # Int |-> ((width_2 * currentHeight_2)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "k" ) )) # Int |-> (k_2))
  ** ((( &( "index" ) )) # Int |-> (index_2))
  ** ((( &( "currentHeight" ) )) # Int |-> (currentHeight_2))
  ** ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex_2))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex_2))
  ** ((( &( "distanceToMaximum" ) )) # Int |-> (distanceToMaximum_2))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea_2))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000))

noncomputable def maxAreaNLogN_entail_wit_9_1 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (distanceToMaximum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight) >= INT_MIN)) (PreH18 : (index > maximumIndex)) (PreH19 : (index >= minimumIndex)) (PreH20 : ((width * currentHeight) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth index l (0 : Int)))) (PreH29 : ((0 : Int) <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : ((0 : Int) <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : ((0 : Int) <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : ((0 : Int) <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : ((0 : Int) <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (index - minimumIndex))) (PreH41 : (distanceToMaximum = (index - maximumIndex))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMaximum)) (PreH45 : ((0 : Int) <= width)) (PreH46 : (width <= 99999)) (PreH47 : ((0 : Int) <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH53 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex index) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex))) (PreH40 : (distanceToMaximum = (index - maximumIndex))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex index) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex))) (PreH40 : (distanceToMaximum = (index - maximumIndex))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex))) (PreH40 : (distanceToMaximum = (index - maximumIndex))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex index)

noncomputable def maxAreaNLogN_entail_wit_9_2 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (distanceToMaximum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight) >= INT_MIN)) (PreH18 : (index > maximumIndex)) (PreH19 : (index >= minimumIndex)) (PreH20 : ((width * currentHeight) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth index l (0 : Int)))) (PreH29 : ((0 : Int) <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : ((0 : Int) <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : ((0 : Int) <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : ((0 : Int) <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : ((0 : Int) <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (index - minimumIndex))) (PreH41 : (distanceToMaximum = (index - maximumIndex))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMinimum)) (PreH45 : ((0 : Int) <= width)) (PreH46 : (width <= 99999)) (PreH47 : ((0 : Int) <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH53 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex index) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex))) (PreH40 : (distanceToMaximum = (index - maximumIndex))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex index) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex))) (PreH40 : (distanceToMaximum = (index - maximumIndex))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_2_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex))) (PreH40 : (distanceToMaximum = (index - maximumIndex))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex index)

noncomputable def maxAreaNLogN_entail_wit_9_3 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMaximum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMaximum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight) >= INT_MIN)) (PreH20 : (index > maximumIndex)) (PreH21 : (index >= minimumIndex)) (PreH22 : ((width * currentHeight) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH30 : (currentHeight = (Znth index l (0 : Int)))) (PreH31 : ((0 : Int) <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : ((0 : Int) <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : ((0 : Int) <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : ((0 : Int) <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : ((0 : Int) <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (index - minimumIndex))) (PreH43 : (distanceToMaximum = (index - maximumIndex))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMaximum)) (PreH47 : ((0 : Int) <= width)) (PreH48 : (width <= 99999)) (PreH49 : ((0 : Int) <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH55 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex index) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex))) (PreH42 : (distanceToMaximum = (index - maximumIndex))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex index) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_3_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex))) (PreH42 : (distanceToMaximum = (index - maximumIndex))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_3_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex))) (PreH42 : (distanceToMaximum = (index - maximumIndex))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex index)

noncomputable def maxAreaNLogN_entail_wit_9_4 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMaximum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMaximum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight) >= INT_MIN)) (PreH20 : (index > maximumIndex)) (PreH21 : (index >= minimumIndex)) (PreH22 : ((width * currentHeight) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH30 : (currentHeight = (Znth index l (0 : Int)))) (PreH31 : ((0 : Int) <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : ((0 : Int) <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : ((0 : Int) <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : ((0 : Int) <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : ((0 : Int) <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (index - minimumIndex))) (PreH43 : (distanceToMaximum = (index - maximumIndex))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMinimum)) (PreH47 : ((0 : Int) <= width)) (PreH48 : (width <= 99999)) (PreH49 : ((0 : Int) <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH55 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= index) ” &&
  “ (index < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex index) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex))) (PreH42 : (distanceToMaximum = (index - maximumIndex))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex index) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_4_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex))) (PreH42 : (distanceToMaximum = (index - maximumIndex))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_4_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex))) (PreH42 : (distanceToMaximum = (index - maximumIndex))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex index)

noncomputable def maxAreaNLogN_entail_wit_9_5 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth index l (0 : Int)))) (PreH29 : ((0 : Int) <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : ((0 : Int) <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : ((0 : Int) <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : ((0 : Int) <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : ((0 : Int) <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index))) (PreH41 : (distanceToMaximum = (maximumIndex - index))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMaximum)) (PreH45 : ((0 : Int) <= width)) (PreH46 : (width <= 99999)) (PreH47 : ((0 : Int) <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH53 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) index maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index))) (PreH40 : (distanceToMaximum = (maximumIndex - index))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) index maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_5_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index))) (PreH40 : (distanceToMaximum = (maximumIndex - index))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_5_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index))) (PreH40 : (distanceToMaximum = (maximumIndex - index))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) index maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_6 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth index l (0 : Int)))) (PreH29 : ((0 : Int) <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : ((0 : Int) <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : ((0 : Int) <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : ((0 : Int) <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : ((0 : Int) <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index))) (PreH41 : (distanceToMaximum = (maximumIndex - index))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMinimum)) (PreH45 : ((0 : Int) <= width)) (PreH46 : (width <= 99999)) (PreH47 : ((0 : Int) <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH53 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) index maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index))) (PreH40 : (distanceToMaximum = (maximumIndex - index))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) index maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_6_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index))) (PreH40 : (distanceToMaximum = (maximumIndex - index))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_6_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH26 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH27 : (currentHeight = (Znth index l (0 : Int)))) (PreH28 : ((0 : Int) <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : ((0 : Int) <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : ((0 : Int) <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : ((0 : Int) <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : ((0 : Int) <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index))) (PreH40 : (distanceToMaximum = (maximumIndex - index))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : ((0 : Int) <= width)) (PreH45 : (width <= 99999)) (PreH46 : ((0 : Int) <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH52 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) index maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_7 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH30 : (currentHeight = (Znth index l (0 : Int)))) (PreH31 : ((0 : Int) <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : ((0 : Int) <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : ((0 : Int) <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : ((0 : Int) <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : ((0 : Int) <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index))) (PreH43 : (distanceToMaximum = (maximumIndex - index))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMaximum)) (PreH47 : ((0 : Int) <= width)) (PreH48 : (width <= 99999)) (PreH49 : ((0 : Int) <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH55 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) index maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index))) (PreH42 : (distanceToMaximum = (maximumIndex - index))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) index maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_7_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index))) (PreH42 : (distanceToMaximum = (maximumIndex - index))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_7_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index))) (PreH42 : (distanceToMaximum = (maximumIndex - index))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) index maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_8 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH30 : (currentHeight = (Znth index l (0 : Int)))) (PreH31 : ((0 : Int) <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : ((0 : Int) <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : ((0 : Int) <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : ((0 : Int) <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : ((0 : Int) <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index))) (PreH43 : (distanceToMaximum = (maximumIndex - index))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMinimum)) (PreH47 : ((0 : Int) <= width)) (PreH48 : (width <= 99999)) (PreH49 : ((0 : Int) <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH55 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= index) ” &&
  “ (index <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) index maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index))) (PreH42 : (distanceToMaximum = (maximumIndex - index))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) index maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_8_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index))) (PreH42 : (distanceToMaximum = (maximumIndex - index))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_8_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH28 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH29 : (currentHeight = (Znth index l (0 : Int)))) (PreH30 : ((0 : Int) <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : ((0 : Int) <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : ((0 : Int) <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : ((0 : Int) <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : ((0 : Int) <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index))) (PreH42 : (distanceToMaximum = (maximumIndex - index))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : ((0 : Int) <= width)) (PreH47 : (width <= 99999)) (PreH48 : ((0 : Int) <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH54 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) index maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_9 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_9_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_9_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_10 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_10_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_10_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_11 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_11_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_11_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_12 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_12_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_12_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_13 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_13_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_13_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_14 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_14_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_14_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_15 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_15_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMaximum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_15_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_16 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= (width * currentHeight)) ” &&
  “ ((width * currentHeight) <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) (width * currentHeight)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight)) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_16_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) (distanceToMinimum * currentHeight))

noncomputable def maxAreaNLogN_entail_wit_9_16_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_17 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_17_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_17_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_18 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_18_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_18_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_19 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_19_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_19_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_20 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_20_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_20_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_21 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_21_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_21_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_22 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_22_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_22_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (maximumIndex - index))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_23 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_23_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_23_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_9_24 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (buffer_h_2 : (List Int)) (buffer_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h_2)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i_2)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h_2)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i_2)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  EX buffer_i : (List Int), EX buffer_h : (List Int), EX sorted_h : (List Int), EX sorted_i : (List Int),
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= (k + 1)) ” &&
  “ ((k + 1) <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1) minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex) ”
  &&  emp
)

noncomputable def maxAreaNLogN_entail_wit_9_24_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1) maximumArea)

noncomputable def maxAreaNLogN_entail_wit_9_24_split_goal_2 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (sorted_h_2 : (List Int)) (sorted_i_2 : (List Int)) (k : Int) (index : Int) (currentHeight : Int) (minimumIndex : Int) (maximumIndex : Int) (distanceToMinimum : Int) (distanceToMaximum : Int) (width : Int) (maximumArea : Int) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 (0 : Int)))) (PreH10 : (currentHeight = (Znth k sorted_h_2 (0 : Int)))) (PreH11 : (currentHeight = (Znth index l (0 : Int)))) (PreH12 : ((0 : Int) <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : ((0 : Int) <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : ((0 : Int) <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : ((0 : Int) <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : ((0 : Int) <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex))) (PreH24 : (distanceToMaximum = (index - maximumIndex))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : ((0 : Int) <= width)) (PreH29 : (width <= 99999)) (PreH30 : ((0 : Int) <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2)) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex)) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1) minimumIndex maximumIndex)

noncomputable def maxAreaNLogN_entail_wit_10 : Prop :=
  (
forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "minimumIndex" ) )) # Int |-> (minimumIndex))
  ** ((( &( "maximumIndex" ) )) # Int |-> (maximumIndex))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (MaximumContainerArea l maximumArea) ”
  &&  (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_full ( &( "workHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
  ** ((( &( "minimumIndex" ) )) # Int |->_)
  ** ((( &( "maximumIndex" ) )) # Int |->_)
) \/
(
forall (l : (List Int)) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (MaximumContainerArea l maximumArea) ”
  &&  (intArray.undef_full ( &( "workHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferIndex" ) ) 100000)
)

noncomputable def maxAreaNLogN_entail_wit_10_split_goal_1 : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (MaximumContainerArea l maximumArea) ”

noncomputable def maxAreaNLogN_entail_wit_10_split_goal_spatial : Prop :=
  forall (l : (List Int)) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  (intArray.undef_full ( &( "workHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "workIndex" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferHeight" ) ) 100000)
  ** (intArray.undef_full ( &( "bufferIndex" ) ) 100000)

noncomputable def maxAreaNLogN_return_wit_1 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (maximumArea : Int) (PreH1 : (MaximumContainerArea l maximumArea)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (MaximumContainerArea l maximumArea) ”
  &&  (intArray.full height_pre heightSize_pre l)

noncomputable def maxAreaNLogN_partial_solve_wit_1 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) k work_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) k work_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) k buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (k < heightSize_pre) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= heightSize_pre) ” &&
  “ ((Zlength (work_h)) = k) ” &&
  “ ((Zlength (work_i)) = k) ” &&
  “ ((Zlength (buffer_h)) = k) ” &&
  “ ((Zlength (buffer_i)) = k) ” &&
  “ (WorkspacePrefixNLogN l work_h work_i k) ” &&
  “ (WorkspacePrefixNLogN l buffer_h buffer_i k) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((height_pre + (k * sizeof(INT)))) # Int |-> ((Znth k l (0 : Int))))
  ** (intArray.missing_i height_pre k (0 : Int) heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) k work_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) k work_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) k buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)

noncomputable def maxAreaNLogN_partial_solve_wit_2 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) k work_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) k work_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) k buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (k < heightSize_pre) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= heightSize_pre) ” &&
  “ ((Zlength (work_h)) = k) ” &&
  “ ((Zlength (work_i)) = k) ” &&
  “ ((Zlength (buffer_h)) = k) ” &&
  “ ((Zlength (buffer_i)) = k) ” &&
  “ (WorkspacePrefixNLogN l work_h work_i k) ” &&
  “ (WorkspacePrefixNLogN l buffer_h buffer_i k) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((( &( "workHeight" ) ) + (k * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "workHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) k work_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) k work_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) k buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)

noncomputable def maxAreaNLogN_partial_solve_wit_3 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workHeight" ) ) (k + 1) (work_h ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) k work_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) k buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (k < heightSize_pre) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= heightSize_pre) ” &&
  “ ((Zlength (work_h)) = k) ” &&
  “ ((Zlength (work_i)) = k) ” &&
  “ ((Zlength (buffer_h)) = k) ” &&
  “ ((Zlength (buffer_i)) = k) ” &&
  “ (WorkspacePrefixNLogN l work_h work_i k) ” &&
  “ (WorkspacePrefixNLogN l buffer_h buffer_i k) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((( &( "workIndex" ) ) + (k * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "workIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workHeight" ) ) (k + 1) (work_h ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) k work_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) k buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)

noncomputable def maxAreaNLogN_partial_solve_wit_4 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workIndex" ) ) (k + 1) (work_i ++ (k :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workHeight" ) ) (k + 1) (work_h ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) k buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (k < heightSize_pre) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= heightSize_pre) ” &&
  “ ((Zlength (work_h)) = k) ” &&
  “ ((Zlength (work_i)) = k) ” &&
  “ ((Zlength (buffer_h)) = k) ” &&
  “ ((Zlength (buffer_i)) = k) ” &&
  “ (WorkspacePrefixNLogN l work_h work_i k) ” &&
  “ (WorkspacePrefixNLogN l buffer_h buffer_i k) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((( &( "bufferHeight" ) ) + (k * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workIndex" ) ) (k + 1) (work_i ++ (k :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workHeight" ) ) (k + 1) (work_h ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) k buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)

noncomputable def maxAreaNLogN_partial_solve_wit_5 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (work_i : (List Int)) (work_h : (List Int)) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k)) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "bufferHeight" ) ) (k + 1) (buffer_h ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workIndex" ) ) (k + 1) (work_i ++ (k :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workHeight" ) ) (k + 1) (work_h ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) k heightSize_pre)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (k < heightSize_pre) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= heightSize_pre) ” &&
  “ ((Zlength (work_h)) = k) ” &&
  “ ((Zlength (work_i)) = k) ” &&
  “ ((Zlength (buffer_h)) = k) ” &&
  “ ((Zlength (buffer_i)) = k) ” &&
  “ (WorkspacePrefixNLogN l work_h work_i k) ” &&
  “ (WorkspacePrefixNLogN l buffer_h buffer_i k) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((( &( "bufferIndex" ) ) + (k * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "bufferHeight" ) ) (k + 1) (buffer_h ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workIndex" ) ) (k + 1) (work_i ++ (k :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workIndex" ) ) (k + 1) heightSize_pre)
  ** (intArray.full ( &( "workHeight" ) ) (k + 1) (work_h ++ ((Znth k l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "workHeight" ) ) (k + 1) heightSize_pre)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) k buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)

noncomputable def maxAreaNLogN_partial_solve_wit_6_pure : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (work0_h : (List Int)) (work0_i : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((Zlength (work0_h)) = heightSize_pre)) (PreH5 : ((Zlength (work0_i)) = heightSize_pre)) (PreH6 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH8 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((Zlength (work0_h)) = heightSize_pre) ” &&
  “ ((Zlength (work0_i)) = heightSize_pre) ” &&
  “ ((Zlength (buffer0_h)) = heightSize_pre) ” &&
  “ ((Zlength (buffer0_i)) = heightSize_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= heightSize_pre) ” &&
  “ (heightSize_pre <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ”

noncomputable def maxAreaNLogN_partial_solve_wit_6_aux : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (work0_h : (List Int)) (work0_i : (List Int)) (buffer0_h : (List Int)) (buffer0_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((Zlength (work0_h)) = heightSize_pre)) (PreH5 : ((Zlength (work0_i)) = heightSize_pre)) (PreH6 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH8 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ ((Zlength (work0_h)) = heightSize_pre) ” &&
  “ ((Zlength (work0_i)) = heightSize_pre) ” &&
  “ ((Zlength (buffer0_h)) = heightSize_pre) ” &&
  “ ((Zlength (buffer0_i)) = heightSize_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= heightSize_pre) ” &&
  “ (heightSize_pre <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((Zlength (work0_h)) = heightSize_pre) ” &&
  “ ((Zlength (work0_i)) = heightSize_pre) ” &&
  “ ((Zlength (buffer0_h)) = heightSize_pre) ” &&
  “ ((Zlength (buffer0_i)) = heightSize_pre) ” &&
  “ (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre) ” &&
  “ (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full (( &( "workHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_h)
  ** (intArray.full (( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre work0_i)
  ** (intArray.full (( &( "bufferHeight" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_h)
  ** (intArray.full (( &( "bufferIndex" ) ) + ((0 : Int) * sizeof(INT))) heightSize_pre buffer0_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)

noncomputable def maxAreaNLogN_partial_solve_wit_6 : Prop := maxAreaNLogN_partial_solve_wit_6_pure -> maxAreaNLogN_partial_solve_wit_6_aux

noncomputable def maxAreaNLogN_partial_solve_wit_7 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) sorted_i (0 : Int))))
  ** (intArray.missing_i ( &( "workIndex" ) ) (0 : Int) (0 : Int) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)

noncomputable def maxAreaNLogN_partial_solve_wit_8 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (sorted_h : (List Int)) (sorted_i : (List Int)) (buffer_h : (List Int)) (buffer_i : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((( &( "workIndex" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) sorted_i (0 : Int))))
  ** (intArray.missing_i ( &( "workIndex" ) ) (0 : Int) (0 : Int) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)

noncomputable def maxAreaNLogN_partial_solve_wit_9 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (k < heightSize_pre) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((( &( "workIndex" ) ) + (k * sizeof(INT)))) # Int |-> ((Znth k sorted_i (0 : Int))))
  ** (intArray.missing_i ( &( "workIndex" ) ) k (0 : Int) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)

noncomputable def maxAreaNLogN_partial_solve_wit_10 : Prop :=
  forall (l : (List Int)) (height_pre : Int) (heightSize_pre : Int) (buffer_i : (List Int)) (buffer_h : (List Int)) (sorted_h : (List Int)) (sorted_i : (List Int)) (maximumArea : Int) (maximumIndex : Int) (minimumIndex : Int) (k : Int) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((0 : Int) <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i)) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex)) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.full ( &( "workHeight" ) ) heightSize_pre sorted_h)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)
|--
  “ (k < heightSize_pre) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ (1 <= k) ” &&
  “ (k <= heightSize_pre) ” &&
  “ ((0 : Int) <= minimumIndex) ” &&
  “ (minimumIndex <= maximumIndex) ” &&
  “ (maximumIndex < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i) ” &&
  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex) ” &&
  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((( &( "workHeight" ) ) + (k * sizeof(INT)))) # Int |-> ((Znth k sorted_h (0 : Int))))
  ** (intArray.missing_i ( &( "workHeight" ) ) k (0 : Int) heightSize_pre sorted_h)
  ** (intArray.full ( &( "workIndex" ) ) heightSize_pre sorted_i)
  ** (intArray.full height_pre heightSize_pre l)
  ** (intArray.undef_seg ( &( "workHeight" ) ) heightSize_pre 100000)
  ** (intArray.undef_seg ( &( "workIndex" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferHeight" ) ) heightSize_pre buffer_h)
  ** (intArray.undef_seg ( &( "bufferHeight" ) ) heightSize_pre 100000)
  ** (intArray.full ( &( "bufferIndex" ) ) heightSize_pre buffer_i)
  ** (intArray.undef_seg ( &( "bufferIndex" ) ) heightSize_pre 100000)


structure VC_Correct : Type where
  proof_of_mergeHeightIndexRunsNLogN_safety_wit_1 : mergeHeightIndexRunsNLogN_safety_wit_1
  proof_of_mergeHeightIndexRunsNLogN_safety_wit_2 : mergeHeightIndexRunsNLogN_safety_wit_2
  proof_of_mergeHeightIndexRunsNLogN_safety_wit_3 : mergeHeightIndexRunsNLogN_safety_wit_3
  proof_of_mergeHeightIndexRunsNLogN_safety_wit_4 : mergeHeightIndexRunsNLogN_safety_wit_4
  proof_of_mergeHeightIndexRunsNLogN_safety_wit_5 : mergeHeightIndexRunsNLogN_safety_wit_5
  proof_of_mergeHeightIndexRunsNLogN_safety_wit_6 : mergeHeightIndexRunsNLogN_safety_wit_6
  proof_of_mergeHeightIndexRunsNLogN_safety_wit_7 : mergeHeightIndexRunsNLogN_safety_wit_7
  proof_of_mergeHeightIndexRunsNLogN_safety_wit_8 : mergeHeightIndexRunsNLogN_safety_wit_8
  proof_of_mergeHeightIndexRunsNLogN_safety_wit_9 : mergeHeightIndexRunsNLogN_safety_wit_9
  proof_of_mergeHeightIndexRunsNLogN_entail_wit_3_1 : mergeHeightIndexRunsNLogN_entail_wit_3_1
  proof_of_mergeHeightIndexRunsNLogN_entail_wit_3_2 : mergeHeightIndexRunsNLogN_entail_wit_3_2
  proof_of_mergeHeightIndexRunsNLogN_entail_wit_5_1 : mergeHeightIndexRunsNLogN_entail_wit_5_1
  proof_of_mergeHeightIndexRunsNLogN_entail_wit_5_2 : mergeHeightIndexRunsNLogN_entail_wit_5_2
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_1 : mergeHeightIndexRunsNLogN_partial_solve_wit_1
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_2 : mergeHeightIndexRunsNLogN_partial_solve_wit_2
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_3 : mergeHeightIndexRunsNLogN_partial_solve_wit_3
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_4 : mergeHeightIndexRunsNLogN_partial_solve_wit_4
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_5 : mergeHeightIndexRunsNLogN_partial_solve_wit_5
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_6 : mergeHeightIndexRunsNLogN_partial_solve_wit_6
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_7 : mergeHeightIndexRunsNLogN_partial_solve_wit_7
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_8 : mergeHeightIndexRunsNLogN_partial_solve_wit_8
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_9 : mergeHeightIndexRunsNLogN_partial_solve_wit_9
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_10 : mergeHeightIndexRunsNLogN_partial_solve_wit_10
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_11 : mergeHeightIndexRunsNLogN_partial_solve_wit_11
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_12 : mergeHeightIndexRunsNLogN_partial_solve_wit_12
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_13 : mergeHeightIndexRunsNLogN_partial_solve_wit_13
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_14 : mergeHeightIndexRunsNLogN_partial_solve_wit_14
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_15 : mergeHeightIndexRunsNLogN_partial_solve_wit_15
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_16 : mergeHeightIndexRunsNLogN_partial_solve_wit_16
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_17 : mergeHeightIndexRunsNLogN_partial_solve_wit_17
  proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_18 : mergeHeightIndexRunsNLogN_partial_solve_wit_18
  proof_of_sortHeightIndexRangeNLogN_safety_wit_1 : sortHeightIndexRangeNLogN_safety_wit_1
  proof_of_sortHeightIndexRangeNLogN_safety_wit_2 : sortHeightIndexRangeNLogN_safety_wit_2
  proof_of_sortHeightIndexRangeNLogN_safety_wit_4 : sortHeightIndexRangeNLogN_safety_wit_4
  proof_of_sortHeightIndexRangeNLogN_safety_wit_5 : sortHeightIndexRangeNLogN_safety_wit_5
  proof_of_sortHeightIndexRangeNLogN_safety_wit_6 : sortHeightIndexRangeNLogN_safety_wit_6
  proof_of_sortHeightIndexRangeNLogN_safety_wit_7 : sortHeightIndexRangeNLogN_safety_wit_7
  proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1 : sortHeightIndexRangeNLogN_partial_solve_wit_1
  proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2 : sortHeightIndexRangeNLogN_partial_solve_wit_2
  proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3 : sortHeightIndexRangeNLogN_partial_solve_wit_3
  proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_4 : sortHeightIndexRangeNLogN_partial_solve_wit_4
  proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_5 : sortHeightIndexRangeNLogN_partial_solve_wit_5
  proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_6 : sortHeightIndexRangeNLogN_partial_solve_wit_6
  proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_7 : sortHeightIndexRangeNLogN_partial_solve_wit_7
  proof_of_maxAreaNLogN_safety_wit_1 : maxAreaNLogN_safety_wit_1
  proof_of_maxAreaNLogN_safety_wit_2 : maxAreaNLogN_safety_wit_2
  proof_of_maxAreaNLogN_safety_wit_3 : maxAreaNLogN_safety_wit_3
  proof_of_maxAreaNLogN_safety_wit_4 : maxAreaNLogN_safety_wit_4
  proof_of_maxAreaNLogN_safety_wit_5 : maxAreaNLogN_safety_wit_5
  proof_of_maxAreaNLogN_safety_wit_6 : maxAreaNLogN_safety_wit_6
  proof_of_maxAreaNLogN_safety_wit_7 : maxAreaNLogN_safety_wit_7
  proof_of_maxAreaNLogN_safety_wit_8 : maxAreaNLogN_safety_wit_8
  proof_of_maxAreaNLogN_safety_wit_9 : maxAreaNLogN_safety_wit_9
  proof_of_maxAreaNLogN_safety_wit_10 : maxAreaNLogN_safety_wit_10
  proof_of_maxAreaNLogN_safety_wit_11 : maxAreaNLogN_safety_wit_11
  proof_of_maxAreaNLogN_safety_wit_14 : maxAreaNLogN_safety_wit_14
  proof_of_maxAreaNLogN_safety_wit_15 : maxAreaNLogN_safety_wit_15
  proof_of_maxAreaNLogN_safety_wit_16 : maxAreaNLogN_safety_wit_16
  proof_of_maxAreaNLogN_safety_wit_17 : maxAreaNLogN_safety_wit_17
  proof_of_maxAreaNLogN_safety_wit_18 : maxAreaNLogN_safety_wit_18
  proof_of_maxAreaNLogN_safety_wit_19 : maxAreaNLogN_safety_wit_19
  proof_of_maxAreaNLogN_safety_wit_20 : maxAreaNLogN_safety_wit_20
  proof_of_maxAreaNLogN_safety_wit_21 : maxAreaNLogN_safety_wit_21
  proof_of_maxAreaNLogN_safety_wit_22 : maxAreaNLogN_safety_wit_22
  proof_of_maxAreaNLogN_safety_wit_23 : maxAreaNLogN_safety_wit_23
  proof_of_maxAreaNLogN_safety_wit_24 : maxAreaNLogN_safety_wit_24
  proof_of_maxAreaNLogN_safety_wit_25 : maxAreaNLogN_safety_wit_25
  proof_of_maxAreaNLogN_safety_wit_26 : maxAreaNLogN_safety_wit_26
  proof_of_maxAreaNLogN_safety_wit_27 : maxAreaNLogN_safety_wit_27
  proof_of_maxAreaNLogN_safety_wit_28 : maxAreaNLogN_safety_wit_28
  proof_of_maxAreaNLogN_safety_wit_29 : maxAreaNLogN_safety_wit_29
  proof_of_maxAreaNLogN_safety_wit_30 : maxAreaNLogN_safety_wit_30
  proof_of_maxAreaNLogN_safety_wit_31 : maxAreaNLogN_safety_wit_31
  proof_of_maxAreaNLogN_safety_wit_32 : maxAreaNLogN_safety_wit_32
  proof_of_maxAreaNLogN_safety_wit_33 : maxAreaNLogN_safety_wit_33
  proof_of_maxAreaNLogN_safety_wit_34 : maxAreaNLogN_safety_wit_34
  proof_of_maxAreaNLogN_safety_wit_35 : maxAreaNLogN_safety_wit_35
  proof_of_maxAreaNLogN_safety_wit_36 : maxAreaNLogN_safety_wit_36
  proof_of_maxAreaNLogN_safety_wit_37 : maxAreaNLogN_safety_wit_37
  proof_of_maxAreaNLogN_safety_wit_38 : maxAreaNLogN_safety_wit_38
  proof_of_maxAreaNLogN_safety_wit_39 : maxAreaNLogN_safety_wit_39
  proof_of_maxAreaNLogN_safety_wit_40 : maxAreaNLogN_safety_wit_40
  proof_of_maxAreaNLogN_safety_wit_41 : maxAreaNLogN_safety_wit_41
  proof_of_maxAreaNLogN_safety_wit_42 : maxAreaNLogN_safety_wit_42
  proof_of_maxAreaNLogN_safety_wit_43 : maxAreaNLogN_safety_wit_43
  proof_of_maxAreaNLogN_safety_wit_44 : maxAreaNLogN_safety_wit_44
  proof_of_maxAreaNLogN_safety_wit_45 : maxAreaNLogN_safety_wit_45
  proof_of_maxAreaNLogN_safety_wit_46 : maxAreaNLogN_safety_wit_46
  proof_of_maxAreaNLogN_safety_wit_47 : maxAreaNLogN_safety_wit_47
  proof_of_maxAreaNLogN_safety_wit_48 : maxAreaNLogN_safety_wit_48
  proof_of_maxAreaNLogN_safety_wit_49 : maxAreaNLogN_safety_wit_49
  proof_of_maxAreaNLogN_safety_wit_50 : maxAreaNLogN_safety_wit_50
  proof_of_maxAreaNLogN_safety_wit_51 : maxAreaNLogN_safety_wit_51
  proof_of_maxAreaNLogN_safety_wit_52 : maxAreaNLogN_safety_wit_52
  proof_of_maxAreaNLogN_safety_wit_53 : maxAreaNLogN_safety_wit_53
  proof_of_maxAreaNLogN_safety_wit_54 : maxAreaNLogN_safety_wit_54
  proof_of_maxAreaNLogN_safety_wit_55 : maxAreaNLogN_safety_wit_55
  proof_of_maxAreaNLogN_safety_wit_56 : maxAreaNLogN_safety_wit_56
  proof_of_maxAreaNLogN_safety_wit_57 : maxAreaNLogN_safety_wit_57
  proof_of_maxAreaNLogN_safety_wit_58 : maxAreaNLogN_safety_wit_58
  proof_of_maxAreaNLogN_safety_wit_59 : maxAreaNLogN_safety_wit_59
  proof_of_maxAreaNLogN_safety_wit_60 : maxAreaNLogN_safety_wit_60
  proof_of_maxAreaNLogN_safety_wit_61 : maxAreaNLogN_safety_wit_61
  proof_of_maxAreaNLogN_safety_wit_62 : maxAreaNLogN_safety_wit_62
  proof_of_maxAreaNLogN_safety_wit_63 : maxAreaNLogN_safety_wit_63
  proof_of_maxAreaNLogN_safety_wit_64 : maxAreaNLogN_safety_wit_64
  proof_of_maxAreaNLogN_safety_wit_65 : maxAreaNLogN_safety_wit_65
  proof_of_maxAreaNLogN_safety_wit_66 : maxAreaNLogN_safety_wit_66
  proof_of_maxAreaNLogN_safety_wit_67 : maxAreaNLogN_safety_wit_67
  proof_of_maxAreaNLogN_safety_wit_68 : maxAreaNLogN_safety_wit_68
  proof_of_maxAreaNLogN_safety_wit_69 : maxAreaNLogN_safety_wit_69
  proof_of_maxAreaNLogN_safety_wit_70 : maxAreaNLogN_safety_wit_70
  proof_of_maxAreaNLogN_safety_wit_71 : maxAreaNLogN_safety_wit_71
  proof_of_maxAreaNLogN_safety_wit_72 : maxAreaNLogN_safety_wit_72
  proof_of_maxAreaNLogN_safety_wit_73 : maxAreaNLogN_safety_wit_73
  proof_of_maxAreaNLogN_safety_wit_74 : maxAreaNLogN_safety_wit_74
  proof_of_maxAreaNLogN_safety_wit_75 : maxAreaNLogN_safety_wit_75
  proof_of_maxAreaNLogN_safety_wit_76 : maxAreaNLogN_safety_wit_76
  proof_of_maxAreaNLogN_safety_wit_77 : maxAreaNLogN_safety_wit_77
  proof_of_maxAreaNLogN_safety_wit_78 : maxAreaNLogN_safety_wit_78
  proof_of_maxAreaNLogN_safety_wit_79 : maxAreaNLogN_safety_wit_79
  proof_of_maxAreaNLogN_safety_wit_80 : maxAreaNLogN_safety_wit_80
  proof_of_maxAreaNLogN_return_wit_1 : maxAreaNLogN_return_wit_1
  proof_of_maxAreaNLogN_partial_solve_wit_1 : maxAreaNLogN_partial_solve_wit_1
  proof_of_maxAreaNLogN_partial_solve_wit_2 : maxAreaNLogN_partial_solve_wit_2
  proof_of_maxAreaNLogN_partial_solve_wit_3 : maxAreaNLogN_partial_solve_wit_3
  proof_of_maxAreaNLogN_partial_solve_wit_4 : maxAreaNLogN_partial_solve_wit_4
  proof_of_maxAreaNLogN_partial_solve_wit_5 : maxAreaNLogN_partial_solve_wit_5
  proof_of_maxAreaNLogN_partial_solve_wit_6_pure : maxAreaNLogN_partial_solve_wit_6_pure
  proof_of_maxAreaNLogN_partial_solve_wit_6 : maxAreaNLogN_partial_solve_wit_6
  proof_of_maxAreaNLogN_partial_solve_wit_7 : maxAreaNLogN_partial_solve_wit_7
  proof_of_maxAreaNLogN_partial_solve_wit_8 : maxAreaNLogN_partial_solve_wit_8
  proof_of_maxAreaNLogN_partial_solve_wit_9 : maxAreaNLogN_partial_solve_wit_9
  proof_of_maxAreaNLogN_partial_solve_wit_10 : maxAreaNLogN_partial_solve_wit_10
  proof_of_mergeHeightIndexRunsNLogN_entail_wit_1 : mergeHeightIndexRunsNLogN_entail_wit_1
  proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1 : mergeHeightIndexRunsNLogN_entail_wit_2_1
  proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2 : mergeHeightIndexRunsNLogN_entail_wit_2_2
  proof_of_mergeHeightIndexRunsNLogN_entail_wit_4 : mergeHeightIndexRunsNLogN_entail_wit_4
  proof_of_mergeHeightIndexRunsNLogN_entail_wit_6 : mergeHeightIndexRunsNLogN_entail_wit_6
  proof_of_mergeHeightIndexRunsNLogN_return_wit_1 : mergeHeightIndexRunsNLogN_return_wit_1
  proof_of_sortHeightIndexRangeNLogN_safety_wit_3 : sortHeightIndexRangeNLogN_safety_wit_3
  proof_of_sortHeightIndexRangeNLogN_entail_wit_1 : sortHeightIndexRangeNLogN_entail_wit_1
  proof_of_sortHeightIndexRangeNLogN_entail_wit_2 : sortHeightIndexRangeNLogN_entail_wit_2
  proof_of_sortHeightIndexRangeNLogN_return_wit_1 : sortHeightIndexRangeNLogN_return_wit_1
  proof_of_sortHeightIndexRangeNLogN_return_wit_2 : sortHeightIndexRangeNLogN_return_wit_2
  proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure : sortHeightIndexRangeNLogN_partial_solve_wit_1_pure
  proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure
  proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure : sortHeightIndexRangeNLogN_partial_solve_wit_3_pure
  proof_of_maxAreaNLogN_safety_wit_12 : maxAreaNLogN_safety_wit_12
  proof_of_maxAreaNLogN_safety_wit_13 : maxAreaNLogN_safety_wit_13
  proof_of_maxAreaNLogN_entail_wit_1 : maxAreaNLogN_entail_wit_1
  proof_of_maxAreaNLogN_entail_wit_2 : maxAreaNLogN_entail_wit_2
  proof_of_maxAreaNLogN_entail_wit_3 : maxAreaNLogN_entail_wit_3
  proof_of_maxAreaNLogN_entail_wit_4 : maxAreaNLogN_entail_wit_4
  proof_of_maxAreaNLogN_entail_wit_5 : maxAreaNLogN_entail_wit_5
  proof_of_maxAreaNLogN_entail_wit_6_1 : maxAreaNLogN_entail_wit_6_1
  proof_of_maxAreaNLogN_entail_wit_6_2 : maxAreaNLogN_entail_wit_6_2
  proof_of_maxAreaNLogN_entail_wit_6_3 : maxAreaNLogN_entail_wit_6_3
  proof_of_maxAreaNLogN_entail_wit_6_4 : maxAreaNLogN_entail_wit_6_4
  proof_of_maxAreaNLogN_entail_wit_6_5 : maxAreaNLogN_entail_wit_6_5
  proof_of_maxAreaNLogN_entail_wit_7_1 : maxAreaNLogN_entail_wit_7_1
  proof_of_maxAreaNLogN_entail_wit_7_2 : maxAreaNLogN_entail_wit_7_2
  proof_of_maxAreaNLogN_entail_wit_7_3 : maxAreaNLogN_entail_wit_7_3
  proof_of_maxAreaNLogN_entail_wit_7_4 : maxAreaNLogN_entail_wit_7_4
  proof_of_maxAreaNLogN_entail_wit_8_1 : maxAreaNLogN_entail_wit_8_1
  proof_of_maxAreaNLogN_entail_wit_8_2 : maxAreaNLogN_entail_wit_8_2
  proof_of_maxAreaNLogN_entail_wit_8_3 : maxAreaNLogN_entail_wit_8_3
  proof_of_maxAreaNLogN_entail_wit_8_4 : maxAreaNLogN_entail_wit_8_4
  proof_of_maxAreaNLogN_entail_wit_9_1 : maxAreaNLogN_entail_wit_9_1
  proof_of_maxAreaNLogN_entail_wit_9_2 : maxAreaNLogN_entail_wit_9_2
  proof_of_maxAreaNLogN_entail_wit_9_3 : maxAreaNLogN_entail_wit_9_3
  proof_of_maxAreaNLogN_entail_wit_9_4 : maxAreaNLogN_entail_wit_9_4
  proof_of_maxAreaNLogN_entail_wit_9_5 : maxAreaNLogN_entail_wit_9_5
  proof_of_maxAreaNLogN_entail_wit_9_6 : maxAreaNLogN_entail_wit_9_6
  proof_of_maxAreaNLogN_entail_wit_9_7 : maxAreaNLogN_entail_wit_9_7
  proof_of_maxAreaNLogN_entail_wit_9_8 : maxAreaNLogN_entail_wit_9_8
  proof_of_maxAreaNLogN_entail_wit_9_9 : maxAreaNLogN_entail_wit_9_9
  proof_of_maxAreaNLogN_entail_wit_9_10 : maxAreaNLogN_entail_wit_9_10
  proof_of_maxAreaNLogN_entail_wit_9_11 : maxAreaNLogN_entail_wit_9_11
  proof_of_maxAreaNLogN_entail_wit_9_12 : maxAreaNLogN_entail_wit_9_12
  proof_of_maxAreaNLogN_entail_wit_9_13 : maxAreaNLogN_entail_wit_9_13
  proof_of_maxAreaNLogN_entail_wit_9_14 : maxAreaNLogN_entail_wit_9_14
  proof_of_maxAreaNLogN_entail_wit_9_15 : maxAreaNLogN_entail_wit_9_15
  proof_of_maxAreaNLogN_entail_wit_9_16 : maxAreaNLogN_entail_wit_9_16
  proof_of_maxAreaNLogN_entail_wit_9_17 : maxAreaNLogN_entail_wit_9_17
  proof_of_maxAreaNLogN_entail_wit_9_18 : maxAreaNLogN_entail_wit_9_18
  proof_of_maxAreaNLogN_entail_wit_9_19 : maxAreaNLogN_entail_wit_9_19
  proof_of_maxAreaNLogN_entail_wit_9_20 : maxAreaNLogN_entail_wit_9_20
  proof_of_maxAreaNLogN_entail_wit_9_21 : maxAreaNLogN_entail_wit_9_21
  proof_of_maxAreaNLogN_entail_wit_9_22 : maxAreaNLogN_entail_wit_9_22
  proof_of_maxAreaNLogN_entail_wit_9_23 : maxAreaNLogN_entail_wit_9_23
  proof_of_maxAreaNLogN_entail_wit_9_24 : maxAreaNLogN_entail_wit_9_24
  proof_of_maxAreaNLogN_entail_wit_10 : maxAreaNLogN_entail_wit_10

end SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_goal
